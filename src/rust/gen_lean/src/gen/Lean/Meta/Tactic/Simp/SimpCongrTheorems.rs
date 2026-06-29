// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpCongrTheorems
// Imports: Lean.Util.Recognizers Lean.Util.CollectMVars Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_find_expr, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_nat_to_int,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_length,
    lean_uint64_lor, lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{l_Lean_getAttrParamOptPrio, l_Lean_registerBuiltinAttribute};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isExplicit,
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConst, l_Lean_Expr_isFVar,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override,
    l_Lean_MVarIdSet_insert, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_forallMetaTelescopeReducing,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::r#gen::Lean::Util::CollectMVars::{
    initialize_Lean_Util_CollectMVars, l_Lean_Expr_collectMVars,
    runtime_initialize_Lean_Util_CollectMVars,
};
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, runtime_initialize_Lean_Util_Recognizers,
};
pub static l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedSimpCongrTheorem_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedSimpCongrTheorem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSimpCongrTheorem_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value:
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
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 104, 101, 111, 114, 101, 109, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value:
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
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 117, 110, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value:
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
    m_data: [
        104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 80, 111, 115, 0,
    ],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value:
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
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__17_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_instReprSimpCongrTheorem_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instReprSimpCongrTheorem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReprSimpCongrTheorem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedSimpCongrTheorems_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedSimpCongrTheorems: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 101, 109, 109, 97, 115, 0],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [46, 116, 111, 83, 77, 97, 112, 0],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value:
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
    m_fun: l_Lean_Meta_instReprSimpCongrTheorems_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instReprSimpCongrTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReprSimpCongrTheorems: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprSimpCongrTheorems___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [99, 111, 110, 103, 114, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14078617454908886696 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_addSimpCongrTheoremEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_congrExtension: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 99, 111, 110, 103, 114, 96, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32, 80, 97, 114, 97, 109, 101, 116, 101, 114, 32, 35, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2_value: crate::leanh::LeanStringObject<88> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 108, 105, 100, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 108, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 99, 111, 110, 103, 114, 96, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32, 65, 114, 103, 117, 109, 101, 110, 116, 32, 35, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 35, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 117, 110, 114, 101, 115, 111, 108, 118, 101, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1_value: crate::leanh::LeanStringObject<81> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 81, m_capacity: 81, m_length: 80, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 108, 105, 100, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 104, 101, 97, 100, 32, 119, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 115, 111, 108, 118, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3_value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 108, 105, 100, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 104, 101, 97, 100, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5_value: crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 108, 105, 100, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 117, 110, 114, 101, 115, 111, 108, 118, 101, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,9917798623386220051 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1_value: crate::leanh::LeanStringObject<114> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 114, m_capacity: 114, m_length: 113, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 99, 111, 110, 103, 114, 96, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32, 84, 104, 101, 32, 108, 101, 102, 116, 45, 32, 97, 110, 100, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 97, 114, 101, 32, 110, 111, 116, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 111, 102, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkSimpCongrTheorem___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpCongrTheorem___closed__0: u64 = 0;
pub static l_Lean_Meta_mkSimpCongrTheorem___closed__1_value: crate::leanh::LeanStringObject<59> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 59,
        m_capacity: 59,
        m_length: 58,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 96, 99, 111, 110, 103, 114, 96, 32, 116, 104, 101,
            111, 114, 101, 109, 58, 32, 84, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110,
            111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 114, 32,
            105, 102, 102, 0,
        ],
    };
static mut l_Lean_Meta_mkSimpCongrTheorem___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSimpCongrTheorem___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkSimpCongrTheorem___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSimpCongrTheorem___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12926315994152569291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 105, 109, 112, 67, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9618108526300627014 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6590157143111312079 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4079170924794950370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4369968210829550070 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9710069995307297755 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7900123763592426302 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16286478035785460487 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1425586510940655511 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6137465486370381910 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9094542763737031186 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15469732694694911555 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11699215918282396216 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<1291> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1291, m_capacity: 1291, m_length: 1266, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 96, 115, 105, 109, 112, 96, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 108, 101, 109, 109, 97, 115, 46, 10, 10, 65, 32, 96, 115, 105, 109, 112, 96, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 108, 101, 109, 109, 97, 32, 115, 104, 111, 117, 108, 100, 32, 112, 114, 111, 118, 101, 32, 116, 104, 101, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 102, 32, 116, 119, 111, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 111, 102, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 102, 114, 111, 109, 10, 116, 104, 101, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 100, 105, 118, 105, 100, 117, 97, 108, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 46, 32, 84, 104, 101, 121, 32, 97, 114, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 115, 105, 109, 112, 96, 32, 116, 111, 32, 118, 105, 115, 105, 116, 32, 115, 117, 98, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 111, 102, 32, 97, 110, 10, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 119, 104, 101, 114, 101, 32, 116, 104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 97, 108, 103, 111, 114, 105, 116, 104, 109, 32, 102, 97, 105, 108, 115, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 108, 121, 32, 105, 109, 112, 111, 114, 116, 97, 110, 116, 32, 102, 111, 114, 10, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 119, 104, 101, 114, 101, 32, 115, 111, 109, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 100, 101, 112, 101, 110, 100, 32, 111, 110, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 46, 10, 10, 67, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 108, 101, 109, 109, 97, 115, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 102, 111, 114, 32, 101, 118, 101, 114, 121, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 44, 32, 112, 111, 115, 115, 105, 98, 108, 121, 32, 98, 111, 117, 110, 100, 101, 100, 32, 98, 121, 32, 102, 111, 114, 97, 108, 108, 115, 44, 32, 119, 105, 116, 104, 10, 116, 104, 101, 32, 114, 105, 103, 104, 116, 32, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 98, 101, 105, 110, 103, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 110, 32, 116, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 46, 32, 87, 104, 101, 110, 32, 97, 112, 112, 108, 121, 105, 110, 103, 10, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 116, 104, 101, 111, 114, 101, 109, 115, 44, 32, 96, 115, 105, 109, 112, 96, 32, 119, 105, 108, 108, 32, 102, 105, 114, 115, 116, 32, 105, 110, 102, 101, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 44, 32, 116, 104, 101, 110, 32, 116, 114, 121, 32, 116, 111, 10, 115, 105, 109, 112, 108, 105, 102, 121, 32, 101, 97, 99, 104, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 111, 102, 32, 116, 104, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 32, 97, 110, 100, 32, 102, 105, 110, 97, 108, 108, 121, 32, 105, 110, 102, 101, 114, 32, 116, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 10, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 100, 101, 102, 32, 79, 112, 116, 105, 111, 110, 46, 112, 98, 105, 110, 100, 32, 40, 111, 32, 58, 32, 79, 112, 116, 105, 111, 110, 32, 206, 177, 41, 32, 40, 102, 32, 58, 32, 40, 97, 32, 58, 32, 206, 177, 41, 32, 226, 134, 146, 32, 111, 32, 61, 32, 115, 111, 109, 101, 32, 97, 32, 226, 134, 146, 32, 79, 112, 116, 105, 111, 110, 32, 206, 178, 41, 32, 58, 32, 79, 112, 116, 105, 111, 110, 32, 206, 178, 32, 58, 61, 32, 46, 46, 46, 10, 10, 64, 91, 99, 111, 110, 103, 114, 93, 10, 116, 104, 101, 111, 114, 101, 109, 32, 79, 112, 116, 105, 111, 110, 46, 112, 98, 105, 110, 100, 95, 99, 111, 110, 103, 114, 10, 32, 32, 32, 32, 123, 111, 32, 111, 39, 32, 58, 32, 79, 112, 116, 105, 111, 110, 32, 206, 177, 125, 32, 40, 104, 111, 32, 58, 32, 111, 32, 61, 32, 111, 39, 41, 32, 45, 45, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 102, 111, 114, 32, 102, 105, 114, 115, 116, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 10, 32, 32, 32, 32, 123, 102, 32, 58, 32, 40, 97, 32, 58, 32, 206, 177, 41, 32, 226, 134, 146, 32, 111, 32, 61, 32, 115, 111, 109, 101, 32, 97, 32, 226, 134, 146, 32, 79, 112, 116, 105, 111, 110, 32, 206, 178, 125, 32, 123, 102, 39, 32, 58, 32, 40, 97, 32, 58, 32, 206, 177, 41, 32, 226, 134, 146, 32, 111, 39, 32, 61, 32, 115, 111, 109, 101, 32, 97, 32, 226, 134, 146, 32, 79, 112, 116, 105, 111, 110, 32, 206, 178, 125, 10, 32, 32, 32, 32, 40, 104, 102, 32, 58, 32, 226, 136, 128, 32, 40, 97, 32, 58, 32, 206, 177, 41, 32, 40, 104, 32, 58, 32, 95, 41, 44, 32, 102, 32, 97, 32, 40, 104, 111, 46, 116, 114, 97, 110, 115, 32, 104, 41, 32, 61, 32, 102, 39, 32, 97, 32, 104, 41, 32, 58, 32, 45, 45, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 102, 111, 114, 32, 115, 101, 99, 111, 110, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 10, 32, 32, 32, 32, 111, 46, 112, 98, 105, 110, 100, 32, 102, 32, 61, 32, 111, 39, 46, 112, 98, 105, 110, 100, 32, 102, 39, 32, 58, 61, 32, 45, 45, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 58, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 102, 32, 116, 104, 101, 32, 119, 104, 111, 108, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 10, 32, 32, 46, 46, 46, 10, 96, 96, 96, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__1(
    mut v_a_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = lean_nat_to_int(v_a_3175_);
    return v___x_3176_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(
    mut v___y_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3178_ = l_Nat_reprFast(v___y_3177_);
    v___x_3179_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3179_, 0, v___x_3178_);
    return v___x_3179_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_3180_: *mut crate::leanh::LeanObject,
    mut v_x_3181_: *mut crate::leanh::LeanObject,
    mut v_x_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3182_) == 0 {
                    crate::leanh::lean_dec(v_x_3180_);
                    return v_x_3181_;
                } else {
                    v_head_3183_ = crate::leanh::lean_ctor_get(v_x_3182_, 0);
                    v_tail_3184_ = crate::leanh::lean_ctor_get(v_x_3182_, 1);
                    v_isSharedCheck_3195_ = (!crate::leanh::lean_is_exclusive(v_x_3182_)) as u8;
                    if v_isSharedCheck_3195_ == 0 {
                        v___x_3186_ = v_x_3182_;
                        v_isShared_3187_ = v_isSharedCheck_3195_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3184_);
                        crate::leanh::lean_inc(v_head_3183_);
                        crate::leanh::lean_dec(v_x_3182_);
                        v___x_3186_ = crate::leanh::lean_box(0);
                        v_isShared_3187_ = v_isSharedCheck_3195_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3180_);
                if v_isShared_3187_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3186_, 5);
                    crate::leanh::lean_ctor_set(v___x_3186_, 1, v_x_3180_);
                    crate::leanh::lean_ctor_set(v___x_3186_, 0, v_x_3181_);
                    v___x_3189_ = v___x_3186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_x_3181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_x_3180_);
                    v___x_3189_ = v_reuseFailAlloc_3194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3190_ = l_Nat_reprFast(v_head_3183_);
                v___x_3191_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3191_, 0, v___x_3190_);
                v___x_3192_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3192_, 0, v___x_3189_);
                crate::leanh::lean_ctor_set(v___x_3192_, 1, v___x_3191_);
                v_x_3181_ = v___x_3192_;
                v_x_3182_ = v_tail_3184_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2(
    mut v_x_3196_: *mut crate::leanh::LeanObject,
    mut v_x_3197_: *mut crate::leanh::LeanObject,
    mut v_x_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3198_) == 0 {
                    crate::leanh::lean_dec(v_x_3196_);
                    return v_x_3197_;
                } else {
                    v_head_3199_ = crate::leanh::lean_ctor_get(v_x_3198_, 0);
                    v_tail_3200_ = crate::leanh::lean_ctor_get(v_x_3198_, 1);
                    v_isSharedCheck_3211_ = (!crate::leanh::lean_is_exclusive(v_x_3198_)) as u8;
                    if v_isSharedCheck_3211_ == 0 {
                        v___x_3202_ = v_x_3198_;
                        v_isShared_3203_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3200_);
                        crate::leanh::lean_inc(v_head_3199_);
                        crate::leanh::lean_dec(v_x_3198_);
                        v___x_3202_ = crate::leanh::lean_box(0);
                        v_isShared_3203_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3196_);
                if v_isShared_3203_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3202_, 5);
                    crate::leanh::lean_ctor_set(v___x_3202_, 1, v_x_3196_);
                    crate::leanh::lean_ctor_set(v___x_3202_, 0, v_x_3197_);
                    v___x_3205_ = v___x_3202_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_x_3197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_x_3196_);
                    v___x_3205_ = v_reuseFailAlloc_3210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3206_ = l_Nat_reprFast(v_head_3199_);
                v___x_3207_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3207_, 0, v___x_3206_);
                v___x_3208_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3205_);
                crate::leanh::lean_ctor_set(v___x_3208_, 1, v___x_3207_);
                v___x_3209_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2_spec__3(v_x_3196_, v___x_3208_, v_tail_3200_);
                return v___x_3209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0(
    mut v_x_3212_: *mut crate::leanh::LeanObject,
    mut v_x_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3212_) == 0 {
        let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3213_);
        v___x_3214_ = crate::leanh::lean_box(0);
        return v___x_3214_;
    } else {
        let mut v_tail_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3215_ = crate::leanh::lean_ctor_get(v_x_3212_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3215_) == 0 {
            let mut v_head_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3213_);
            v_head_3216_ = crate::leanh::lean_ctor_get(v_x_3212_, 0);
            crate::leanh::lean_inc(v_head_3216_);
            crate::leanh::lean_dec_ref_known(v_x_3212_, 2);
            v___x_3217_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(v_head_3216_);
            return v___x_3217_;
        } else {
            let mut v_head_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3215_);
            v_head_3218_ = crate::leanh::lean_ctor_get(v_x_3212_, 0);
            crate::leanh::lean_inc(v_head_3218_);
            crate::leanh::lean_dec_ref_known(v_x_3212_, 2);
            v___x_3219_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0___lam__0(v_head_3218_);
            v___x_3220_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0_spec__2(v_x_3213_, v___x_3219_, v_tail_3215_);
            return v___x_3220_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3229_ = l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__0;
    v___x_3230_ = lean_string_length(v___x_3229_);
    return v___x_3230_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__5,
    );
    v___x_3232_ = lean_nat_to_int(v___x_3231_);
    return v___x_3232_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0(
    mut v_xs_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: u8 = 0;
    v___x_3241_ = lean_array_get_size(v_xs_3240_);
    v___x_3242_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3243_ = lean_nat_dec_eq(v___x_3241_, v___x_3242_);
    if v___x_3243_ == 0 {
        let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3244_ = lean_array_to_list(v_xs_3240_);
        v___x_3245_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3;
        v___x_3246_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0_spec__0(v___x_3244_, v___x_3245_);
        v___x_3247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__6);
        v___x_3248_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__7;
        v___x_3249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3249_, 0, v___x_3248_);
        crate::leanh::lean_ctor_set(v___x_3249_, 1, v___x_3246_);
        v___x_3250_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8;
        v___x_3251_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3251_, 0, v___x_3249_);
        crate::leanh::lean_ctor_set(v___x_3251_, 1, v___x_3250_);
        v___x_3252_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3252_, 0, v___x_3247_);
        crate::leanh::lean_ctor_set(v___x_3252_, 1, v___x_3251_);
        v___x_3253_ = l_Std_Format_fill(v___x_3252_);
        return v___x_3253_;
    } else {
        let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_3240_);
        v___x_3254_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__10;
        return v___x_3254_;
    }
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_3269_ = lean_nat_to_int(v___x_3268_);
    return v___x_3269_;
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3273_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3274_ = lean_nat_to_int(v___x_3273_);
    return v___x_3274_;
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3278_ = crate::leanh::lean_unsigned_to_nat(17);
    v___x_3279_ = lean_nat_to_int(v___x_3278_);
    return v___x_3279_;
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_3284_ = lean_nat_to_int(v___x_3283_);
    return v___x_3284_;
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3286_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__0;
    v___x_3287_ = lean_string_length(v___x_3286_);
    return v___x_3287_;
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3288_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__18,
    );
    v___x_3289_ = lean_nat_to_int(v___x_3288_);
    return v___x_3289_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(
    mut v_x_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_theoremName_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hypothesesPos_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: u8 = 0;
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_theoremName_3295_ = crate::leanh::lean_ctor_get(v_x_3294_, 0);
    crate::leanh::lean_inc(v_theoremName_3295_);
    v_funName_3296_ = crate::leanh::lean_ctor_get(v_x_3294_, 1);
    crate::leanh::lean_inc(v_funName_3296_);
    v_hypothesesPos_3297_ = crate::leanh::lean_ctor_get(v_x_3294_, 2);
    crate::leanh::lean_inc_ref(v_hypothesesPos_3297_);
    v_priority_3298_ = crate::leanh::lean_ctor_get(v_x_3294_, 3);
    crate::leanh::lean_inc(v_priority_3298_);
    crate::leanh::lean_dec_ref(v_x_3294_);
    v___x_3299_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__5;
    v___x_3300_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__6;
    v___x_3301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__7,
    );
    v___x_3302_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3303_ = l_Lean_Name_reprPrec(v_theoremName_3295_, v___x_3302_);
    v___x_3304_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3304_, 0, v___x_3301_);
    crate::leanh::lean_ctor_set(v___x_3304_, 1, v___x_3303_);
    v___x_3305_ = 0;
    v___x_3306_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3306_, 0, v___x_3304_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3306_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3305_,
    );
    v___x_3307_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3307_, 0, v___x_3300_);
    crate::leanh::lean_ctor_set(v___x_3307_, 1, v___x_3306_);
    v___x_3308_ = l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__2;
    v___x_3309_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3307_);
    crate::leanh::lean_ctor_set(v___x_3309_, 1, v___x_3308_);
    v___x_3310_ = crate::leanh::lean_box(1);
    v___x_3311_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3311_, 0, v___x_3309_);
    crate::leanh::lean_ctor_set(v___x_3311_, 1, v___x_3310_);
    v___x_3312_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__9;
    v___x_3313_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3313_, 0, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3313_, 1, v___x_3312_);
    v___x_3314_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3314_, 0, v___x_3313_);
    crate::leanh::lean_ctor_set(v___x_3314_, 1, v___x_3299_);
    v___x_3315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__10,
    );
    v___x_3316_ = l_Lean_Name_reprPrec(v_funName_3296_, v___x_3302_);
    v___x_3317_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3317_, 0, v___x_3315_);
    crate::leanh::lean_ctor_set(v___x_3317_, 1, v___x_3316_);
    v___x_3318_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3318_, 0, v___x_3317_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3318_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3305_,
    );
    v___x_3319_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3319_, 0, v___x_3314_);
    crate::leanh::lean_ctor_set(v___x_3319_, 1, v___x_3318_);
    v___x_3320_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3319_);
    crate::leanh::lean_ctor_set(v___x_3320_, 1, v___x_3308_);
    v___x_3321_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3321_, 0, v___x_3320_);
    crate::leanh::lean_ctor_set(v___x_3321_, 1, v___x_3310_);
    v___x_3322_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__12;
    v___x_3323_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3323_, 0, v___x_3321_);
    crate::leanh::lean_ctor_set(v___x_3323_, 1, v___x_3322_);
    v___x_3324_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3324_, 0, v___x_3323_);
    crate::leanh::lean_ctor_set(v___x_3324_, 1, v___x_3299_);
    v___x_3325_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__13,
    );
    v___x_3326_ = l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0(
        v_hypothesesPos_3297_,
    );
    v___x_3327_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3327_, 0, v___x_3325_);
    crate::leanh::lean_ctor_set(v___x_3327_, 1, v___x_3326_);
    v___x_3328_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3328_, 0, v___x_3327_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3328_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3305_,
    );
    v___x_3329_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3324_);
    crate::leanh::lean_ctor_set(v___x_3329_, 1, v___x_3328_);
    v___x_3330_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3330_, 0, v___x_3329_);
    crate::leanh::lean_ctor_set(v___x_3330_, 1, v___x_3308_);
    v___x_3331_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3331_, 0, v___x_3330_);
    crate::leanh::lean_ctor_set(v___x_3331_, 1, v___x_3310_);
    v___x_3332_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__15;
    v___x_3333_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3333_, 0, v___x_3331_);
    crate::leanh::lean_ctor_set(v___x_3333_, 1, v___x_3332_);
    v___x_3334_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3333_);
    crate::leanh::lean_ctor_set(v___x_3334_, 1, v___x_3299_);
    v___x_3335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__16,
    );
    v___x_3336_ = l_Nat_reprFast(v_priority_3298_);
    v___x_3337_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3337_, 0, v___x_3336_);
    v___x_3338_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3338_, 0, v___x_3335_);
    crate::leanh::lean_ctor_set(v___x_3338_, 1, v___x_3337_);
    v___x_3339_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3339_, 0, v___x_3338_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3339_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3305_,
    );
    v___x_3340_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3340_, 0, v___x_3334_);
    crate::leanh::lean_ctor_set(v___x_3340_, 1, v___x_3339_);
    v___x_3341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19,
    );
    v___x_3342_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20;
    v___x_3343_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3343_, 0, v___x_3342_);
    crate::leanh::lean_ctor_set(v___x_3343_, 1, v___x_3340_);
    v___x_3344_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21;
    v___x_3345_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3345_, 0, v___x_3343_);
    crate::leanh::lean_ctor_set(v___x_3345_, 1, v___x_3344_);
    v___x_3346_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3341_);
    crate::leanh::lean_ctor_set(v___x_3346_, 1, v___x_3345_);
    v___x_3347_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3347_, 0, v___x_3346_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3347_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3305_,
    );
    return v___x_3347_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorem_repr(
    mut v_x_3348_: *mut crate::leanh::LeanObject,
    mut v_prec_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_x_3348_);
    return v___x_3350_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorem_repr___boxed(
    mut v_x_3351_: *mut crate::leanh::LeanObject,
    mut v_prec_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_Meta_instReprSimpCongrTheorem_repr(v_x_3351_, v_prec_3352_);
    crate::leanh::lean_dec(v_prec_3352_);
    return v_res_3353_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = crate::leanh::lean_box(0);
    v___x_3357_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3358_ = lean_mk_array(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3359_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__0,
    );
    v___x_3360_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3360_);
    crate::leanh::lean_ctor_set(v___x_3361_, 1, v___x_3359_);
    return v___x_3361_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3362_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__2,
    );
    v___x_3364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3364_, 0, v___x_3363_);
    return v___x_3364_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u8 = 0;
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__3,
    );
    v___x_3366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__1,
    );
    v___x_3367_ = 1;
    v___x_3368_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3366_);
    crate::leanh::lean_ctor_set(v___x_3368_, 1, v___x_3365_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3368_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_3367_,
    );
    return v___x_3368_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4,
    );
    return v___x_3369_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedSimpCongrTheorems() -> *mut crate::leanh::LeanObject {
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
    return v___x_3370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(
    mut v_f_3371_: *mut crate::leanh::LeanObject,
    mut v_x_3372_: *mut crate::leanh::LeanObject,
    mut v_x_3373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3373_) == 0 {
                    crate::leanh::lean_dec(v_f_3371_);
                    return v_x_3372_;
                } else {
                    v_key_3374_ = crate::leanh::lean_ctor_get(v_x_3373_, 0);
                    crate::leanh::lean_inc(v_key_3374_);
                    v_value_3375_ = crate::leanh::lean_ctor_get(v_x_3373_, 1);
                    crate::leanh::lean_inc(v_value_3375_);
                    v_tail_3376_ = crate::leanh::lean_ctor_get(v_x_3373_, 2);
                    crate::leanh::lean_inc(v_tail_3376_);
                    crate::leanh::lean_dec_ref_known(v_x_3373_, 3);
                    crate::leanh::lean_inc(v_f_3371_);
                    v___x_3377_ = crate::leanh::lean_apply_3(
                        v_f_3371_,
                        v_x_3372_,
                        v_key_3374_,
                        v_value_3375_,
                    );
                    v_x_3372_ = v___x_3377_;
                    v_x_3373_ = v_tail_3376_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(
    mut v_f_3379_: *mut crate::leanh::LeanObject,
    mut v_as_3380_: *mut crate::leanh::LeanObject,
    mut v_i_3381_: usize,
    mut v_stop_3382_: usize,
    mut v_b_3383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3384_ = lean_usize_dec_eq(v_i_3381_, v_stop_3382_);
                if v___x_3384_ == 0 {
                    v___x_3385_ = lean_array_uget_borrowed(v_as_3380_, v_i_3381_);
                    crate::leanh::lean_inc(v___x_3385_);
                    crate::leanh::lean_inc(v_f_3379_);
                    v___x_3386_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(v_f_3379_, v_b_3383_, v___x_3385_);
                    v___x_3387_ = 1usize;
                    v___x_3388_ = lean_usize_add(v_i_3381_, v___x_3387_);
                    v_i_3381_ = v___x_3388_;
                    v_b_3383_ = v___x_3386_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_f_3379_);
                    return v_b_3383_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_f_3390_: *mut crate::leanh::LeanObject,
    mut v_as_3391_: *mut crate::leanh::LeanObject,
    mut v_i_3392_: *mut crate::leanh::LeanObject,
    mut v_stop_3393_: *mut crate::leanh::LeanObject,
    mut v_b_3394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3395_: usize = 0;
    let mut v_stop_boxed_3396_: usize = 0;
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3395_ = crate::leanh::lean_unbox_usize(v_i_3392_);
    crate::leanh::lean_dec(v_i_3392_);
    v_stop_boxed_3396_ = crate::leanh::lean_unbox_usize(v_stop_3393_);
    crate::leanh::lean_dec(v_stop_3393_);
    v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_3390_, v_as_3391_, v_i_boxed_3395_, v_stop_boxed_3396_, v_b_3394_);
    crate::leanh::lean_dec_ref(v_as_3391_);
    return v_res_3397_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v_f_3398_: *mut crate::leanh::LeanObject,
    mut v_x1_3399_: *mut crate::leanh::LeanObject,
    mut v_x2_3400_: *mut crate::leanh::LeanObject,
    mut v_x3_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3402_ = crate::leanh::lean_apply_3(v_f_3398_, v_x1_3399_, v_x2_3400_, v_x3_3401_);
    return v___x_3402_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(
    mut v_f_3403_: *mut crate::leanh::LeanObject,
    mut v_keys_3404_: *mut crate::leanh::LeanObject,
    mut v_vals_3405_: *mut crate::leanh::LeanObject,
    mut v_i_3406_: *mut crate::leanh::LeanObject,
    mut v_acc_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: u8 = 0;
    let mut v_k_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3408_ = lean_array_get_size(v_keys_3404_);
                v___x_3409_ = lean_nat_dec_lt(v_i_3406_, v___x_3408_);
                if v___x_3409_ == 0 {
                    crate::leanh::lean_dec(v_i_3406_);
                    crate::leanh::lean_dec(v_f_3403_);
                    return v_acc_3407_;
                } else {
                    v_k_3410_ = lean_array_fget_borrowed(v_keys_3404_, v_i_3406_);
                    v_v_3411_ = lean_array_fget_borrowed(v_vals_3405_, v_i_3406_);
                    crate::leanh::lean_inc(v_f_3403_);
                    crate::leanh::lean_inc(v_v_3411_);
                    crate::leanh::lean_inc(v_k_3410_);
                    v___x_3412_ =
                        crate::leanh::lean_apply_3(v_f_3403_, v_acc_3407_, v_k_3410_, v_v_3411_);
                    v___x_3413_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3414_ = lean_nat_add(v_i_3406_, v___x_3413_);
                    crate::leanh::lean_dec(v_i_3406_);
                    v_i_3406_ = v___x_3414_;
                    v_acc_3407_ = v___x_3412_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(
    mut v_f_3416_: *mut crate::leanh::LeanObject,
    mut v_keys_3417_: *mut crate::leanh::LeanObject,
    mut v_vals_3418_: *mut crate::leanh::LeanObject,
    mut v_i_3419_: *mut crate::leanh::LeanObject,
    mut v_acc_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_3416_, v_keys_3417_, v_vals_3418_, v_i_3419_, v_acc_3420_);
    crate::leanh::lean_dec_ref(v_vals_3418_);
    crate::leanh::lean_dec_ref(v_keys_3417_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(
    mut v_f_3422_: *mut crate::leanh::LeanObject,
    mut v_x_3423_: *mut crate::leanh::LeanObject,
    mut v_x_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3423_) == 0 {
        let mut v_es_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3428_: u8 = 0;
        v_es_3425_ = crate::leanh::lean_ctor_get(v_x_3423_, 0);
        v___x_3426_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3427_ = lean_array_get_size(v_es_3425_);
        v___x_3428_ = lean_nat_dec_lt(v___x_3426_, v___x_3427_);
        if v___x_3428_ == 0 {
            crate::leanh::lean_dec(v_f_3422_);
            return v_x_3424_;
        } else {
            let mut v___x_3429_: u8 = 0;
            v___x_3429_ = lean_nat_dec_le(v___x_3427_, v___x_3427_);
            if v___x_3429_ == 0 {
                if v___x_3428_ == 0 {
                    crate::leanh::lean_dec(v_f_3422_);
                    return v_x_3424_;
                } else {
                    let mut v___x_3430_: usize = 0;
                    let mut v___x_3431_: usize = 0;
                    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3430_ = 0usize;
                    v___x_3431_ = lean_usize_of_nat(v___x_3427_);
                    v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_3422_, v_es_3425_, v___x_3430_, v___x_3431_, v_x_3424_);
                    return v___x_3432_;
                }
            } else {
                let mut v___x_3433_: usize = 0;
                let mut v___x_3434_: usize = 0;
                let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3433_ = 0usize;
                v___x_3434_ = lean_usize_of_nat(v___x_3427_);
                v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_3422_, v_es_3425_, v___x_3433_, v___x_3434_, v_x_3424_);
                return v___x_3435_;
            }
        }
    } else {
        let mut v_ks_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_3436_ = crate::leanh::lean_ctor_get(v_x_3423_, 0);
        v_vs_3437_ = crate::leanh::lean_ctor_get(v_x_3423_, 1);
        v___x_3438_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_3422_, v_ks_3436_, v_vs_3437_, v___x_3438_, v_x_3424_);
        return v___x_3439_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(
    mut v_f_3440_: *mut crate::leanh::LeanObject,
    mut v_as_3441_: *mut crate::leanh::LeanObject,
    mut v_i_3442_: usize,
    mut v_stop_3443_: usize,
    mut v_b_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: usize = 0;
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3450_ = lean_usize_dec_eq(v_i_3442_, v_stop_3443_);
                if v___x_3450_ == 0 {
                    v___x_3451_ = lean_array_uget_borrowed(v_as_3441_, v_i_3442_);
                    match crate::leanh::lean_obj_tag(v___x_3451_) {
                        0 => {
                            v_key_3452_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                            v_val_3453_ = crate::leanh::lean_ctor_get(v___x_3451_, 1);
                            crate::leanh::lean_inc(v_f_3440_);
                            crate::leanh::lean_inc(v_val_3453_);
                            crate::leanh::lean_inc(v_key_3452_);
                            v___x_3454_ = crate::leanh::lean_apply_3(
                                v_f_3440_,
                                v_b_3444_,
                                v_key_3452_,
                                v_val_3453_,
                            );
                            v___y_3446_ = v___x_3454_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3455_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                            crate::leanh::lean_inc(v_f_3440_);
                            v___x_3456_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_3440_, v_node_3455_, v_b_3444_);
                            v___y_3446_ = v___x_3456_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3446_ = v_b_3444_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_3440_);
                    return v_b_3444_;
                }
            }
            1 => {
                v___x_3447_ = 1usize;
                v___x_3448_ = lean_usize_add(v_i_3442_, v___x_3447_);
                v_i_3442_ = v___x_3448_;
                v_b_3444_ = v___y_3446_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(
    mut v_f_3457_: *mut crate::leanh::LeanObject,
    mut v_as_3458_: *mut crate::leanh::LeanObject,
    mut v_i_3459_: *mut crate::leanh::LeanObject,
    mut v_stop_3460_: *mut crate::leanh::LeanObject,
    mut v_b_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3462_: usize = 0;
    let mut v_stop_boxed_3463_: usize = 0;
    let mut v_res_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3462_ = crate::leanh::lean_unbox_usize(v_i_3459_);
    crate::leanh::lean_dec(v_i_3459_);
    v_stop_boxed_3463_ = crate::leanh::lean_unbox_usize(v_stop_3460_);
    crate::leanh::lean_dec(v_stop_3460_);
    v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_3457_, v_as_3458_, v_i_boxed_3462_, v_stop_boxed_3463_, v_b_3461_);
    crate::leanh::lean_dec_ref(v_as_3458_);
    return v_res_3464_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_f_3465_: *mut crate::leanh::LeanObject,
    mut v_x_3466_: *mut crate::leanh::LeanObject,
    mut v_x_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_3465_, v_x_3466_, v_x_3467_);
    crate::leanh::lean_dec_ref(v_x_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(
    mut v_map_3469_: *mut crate::leanh::LeanObject,
    mut v_f_3470_: *mut crate::leanh::LeanObject,
    mut v_init_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3472_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3472_, 0, v_f_3470_);
    v___x_3473_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_3472_, v_map_3469_, v_init_3471_);
    return v___x_3473_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_map_3474_: *mut crate::leanh::LeanObject,
    mut v_f_3475_: *mut crate::leanh::LeanObject,
    mut v_init_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_3474_, v_f_3475_, v_init_3476_);
    crate::leanh::lean_dec_ref(v_map_3474_);
    return v_res_3477_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(
    mut v_f_3478_: *mut crate::leanh::LeanObject,
    mut v_init_3479_: *mut crate::leanh::LeanObject,
    mut v_m_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    v_map_u2081_3481_ = crate::leanh::lean_ctor_get(v_m_3480_, 0);
    v_map_u2082_3482_ = crate::leanh::lean_ctor_get(v_m_3480_, 1);
    v_buckets_3483_ = crate::leanh::lean_ctor_get(v_map_u2081_3481_, 1);
    v___x_3484_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3485_ = lean_array_get_size(v_buckets_3483_);
    v___x_3486_ = lean_nat_dec_lt(v___x_3484_, v___x_3485_);
    if v___x_3486_ == 0 {
        let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3487_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_3482_, v_f_3478_, v_init_3479_);
        return v___x_3487_;
    } else {
        let mut v___x_3488_: u8 = 0;
        v___x_3488_ = lean_nat_dec_le(v___x_3485_, v___x_3485_);
        if v___x_3488_ == 0 {
            if v___x_3486_ == 0 {
                let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3489_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_3482_, v_f_3478_, v_init_3479_);
                return v___x_3489_;
            } else {
                let mut v___x_3490_: usize = 0;
                let mut v___x_3491_: usize = 0;
                let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3490_ = 0usize;
                v___x_3491_ = lean_usize_of_nat(v___x_3485_);
                crate::leanh::lean_inc(v_f_3478_);
                v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_3478_, v_buckets_3483_, v___x_3490_, v___x_3491_, v_init_3479_);
                v___x_3493_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_3482_, v_f_3478_, v___x_3492_);
                return v___x_3493_;
            }
        } else {
            let mut v___x_3494_: usize = 0;
            let mut v___x_3495_: usize = 0;
            let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3494_ = 0usize;
            v___x_3495_ = lean_usize_of_nat(v___x_3485_);
            crate::leanh::lean_inc(v_f_3478_);
            v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_3478_, v_buckets_3483_, v___x_3494_, v___x_3495_, v_init_3479_);
            v___x_3497_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_3482_, v_f_3478_, v___x_3496_);
            return v___x_3497_;
        }
    }
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg___boxed(
    mut v_f_3498_: *mut crate::leanh::LeanObject,
    mut v_init_3499_: *mut crate::leanh::LeanObject,
    mut v_m_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v_f_3498_, v_init_3499_, v_m_3500_);
    crate::leanh::lean_dec_ref(v_m_3500_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___lam__0(
    mut v_es_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_b_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3505_, 0, v_a_3503_);
    crate::leanh::lean_ctor_set(v___x_3505_, 1, v_b_3504_);
    v___x_3506_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3506_, 0, v___x_3505_);
    crate::leanh::lean_ctor_set(v___x_3506_, 1, v_es_3502_);
    return v___x_3506_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(
    mut v_m_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3509_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___closed__0;
    v___x_3510_ = crate::leanh::lean_box(0);
    v___x_3511_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v___f_3509_, v___x_3510_, v_m_3508_);
    return v___x_3511_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg___boxed(
    mut v_m_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3513_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(
            v_m_3512_,
        );
    crate::leanh::lean_dec_ref(v_m_3512_);
    return v_res_3513_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11_spec__16(
    mut v_x_3514_: *mut crate::leanh::LeanObject,
    mut v_x_3515_: *mut crate::leanh::LeanObject,
    mut v_x_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3516_) == 0 {
                    crate::leanh::lean_dec(v_x_3514_);
                    return v_x_3515_;
                } else {
                    v_head_3517_ = crate::leanh::lean_ctor_get(v_x_3516_, 0);
                    v_tail_3518_ = crate::leanh::lean_ctor_get(v_x_3516_, 1);
                    v_isSharedCheck_3528_ = (!crate::leanh::lean_is_exclusive(v_x_3516_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v___x_3520_ = v_x_3516_;
                        v_isShared_3521_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3518_);
                        crate::leanh::lean_inc(v_head_3517_);
                        crate::leanh::lean_dec(v_x_3516_);
                        v___x_3520_ = crate::leanh::lean_box(0);
                        v_isShared_3521_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3514_);
                if v_isShared_3521_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3520_, 5);
                    crate::leanh::lean_ctor_set(v___x_3520_, 1, v_x_3514_);
                    crate::leanh::lean_ctor_set(v___x_3520_, 0, v_x_3515_);
                    v___x_3523_ = v___x_3520_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_x_3515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_x_3514_);
                    v___x_3523_ = v_reuseFailAlloc_3527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3524_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_3517_);
                v___x_3525_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3523_);
                crate::leanh::lean_ctor_set(v___x_3525_, 1, v___x_3524_);
                v_x_3515_ = v___x_3525_;
                v_x_3516_ = v_tail_3518_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11(
    mut v_x_3529_: *mut crate::leanh::LeanObject,
    mut v_x_3530_: *mut crate::leanh::LeanObject,
    mut v_x_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3531_) == 0 {
                    crate::leanh::lean_dec(v_x_3529_);
                    return v_x_3530_;
                } else {
                    v_head_3532_ = crate::leanh::lean_ctor_get(v_x_3531_, 0);
                    v_tail_3533_ = crate::leanh::lean_ctor_get(v_x_3531_, 1);
                    v_isSharedCheck_3543_ = (!crate::leanh::lean_is_exclusive(v_x_3531_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3535_ = v_x_3531_;
                        v_isShared_3536_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3533_);
                        crate::leanh::lean_inc(v_head_3532_);
                        crate::leanh::lean_dec(v_x_3531_);
                        v___x_3535_ = crate::leanh::lean_box(0);
                        v_isShared_3536_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3529_);
                if v_isShared_3536_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3535_, 5);
                    crate::leanh::lean_ctor_set(v___x_3535_, 1, v_x_3529_);
                    crate::leanh::lean_ctor_set(v___x_3535_, 0, v_x_3530_);
                    v___x_3538_ = v___x_3535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_x_3530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_x_3529_);
                    v___x_3538_ = v_reuseFailAlloc_3542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3539_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_3532_);
                v___x_3540_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3538_);
                crate::leanh::lean_ctor_set(v___x_3540_, 1, v___x_3539_);
                v___x_3541_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11_spec__16(v_x_3529_, v___x_3540_, v_tail_3533_);
                return v___x_3541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8(
    mut v_x_3544_: *mut crate::leanh::LeanObject,
    mut v_x_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3544_) == 0 {
        let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3545_);
        v___x_3546_ = crate::leanh::lean_box(0);
        return v___x_3546_;
    } else {
        let mut v_tail_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3547_ = crate::leanh::lean_ctor_get(v_x_3544_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3547_) == 0 {
            let mut v_head_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3545_);
            v_head_3548_ = crate::leanh::lean_ctor_get(v_x_3544_, 0);
            crate::leanh::lean_inc(v_head_3548_);
            crate::leanh::lean_dec_ref_known(v_x_3544_, 2);
            v___x_3549_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_3548_);
            return v___x_3549_;
        } else {
            let mut v_head_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3547_);
            v_head_3550_ = crate::leanh::lean_ctor_get(v_x_3544_, 0);
            crate::leanh::lean_inc(v_head_3550_);
            crate::leanh::lean_dec_ref_known(v_x_3544_, 2);
            v___x_3551_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg(v_head_3550_);
            v___x_3552_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8_spec__11(v_x_3545_, v___x_3551_, v_tail_3547_);
            return v___x_3552_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3557_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__2;
    v___x_3558_ = lean_string_length(v___x_3557_);
    return v___x_3558_;
}
pub unsafe fn _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__3);
    v___x_3560_ = lean_nat_to_int(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(
    mut v_a_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3563_) == 0 {
        let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3564_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1;
        return v___x_3564_;
    } else {
        let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: u8 = 0;
        let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3565_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3;
        v___x_3566_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6_spec__8(v_a_3563_, v___x_3565_);
        v___x_3567_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4);
        v___x_3568_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5;
        v___x_3569_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3569_, 0, v___x_3568_);
        crate::leanh::lean_ctor_set(v___x_3569_, 1, v___x_3566_);
        v___x_3570_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8;
        v___x_3571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3571_, 0, v___x_3569_);
        crate::leanh::lean_ctor_set(v___x_3571_, 1, v___x_3570_);
        v___x_3572_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3572_, 0, v___x_3567_);
        crate::leanh::lean_ctor_set(v___x_3572_, 1, v___x_3571_);
        v___x_3573_ = 0;
        v___x_3574_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3572_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_3574_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_3573_,
        );
        return v___x_3574_;
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7_spec__10(
    mut v_x_3575_: *mut crate::leanh::LeanObject,
    mut v_x_3576_: *mut crate::leanh::LeanObject,
    mut v_x_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3577_) == 0 {
                    crate::leanh::lean_dec(v_x_3575_);
                    return v_x_3576_;
                } else {
                    v_head_3578_ = crate::leanh::lean_ctor_get(v_x_3577_, 0);
                    v_tail_3579_ = crate::leanh::lean_ctor_get(v_x_3577_, 1);
                    v_isSharedCheck_3588_ = (!crate::leanh::lean_is_exclusive(v_x_3577_)) as u8;
                    if v_isSharedCheck_3588_ == 0 {
                        v___x_3581_ = v_x_3577_;
                        v_isShared_3582_ = v_isSharedCheck_3588_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3579_);
                        crate::leanh::lean_inc(v_head_3578_);
                        crate::leanh::lean_dec(v_x_3577_);
                        v___x_3581_ = crate::leanh::lean_box(0);
                        v_isShared_3582_ = v_isSharedCheck_3588_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3575_);
                if v_isShared_3582_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3581_, 5);
                    crate::leanh::lean_ctor_set(v___x_3581_, 1, v_x_3575_);
                    crate::leanh::lean_ctor_set(v___x_3581_, 0, v_x_3576_);
                    v___x_3584_ = v___x_3581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_x_3576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_x_3575_);
                    v___x_3584_ = v_reuseFailAlloc_3587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3585_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                crate::leanh::lean_ctor_set(v___x_3585_, 1, v_head_3578_);
                v_x_3576_ = v___x_3585_;
                v_x_3577_ = v_tail_3579_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7(
    mut v_x_3589_: *mut crate::leanh::LeanObject,
    mut v_x_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3589_) == 0 {
        let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3590_);
        v___x_3591_ = crate::leanh::lean_box(0);
        return v___x_3591_;
    } else {
        let mut v_tail_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3592_ = crate::leanh::lean_ctor_get(v_x_3589_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3592_) == 0 {
            let mut v_head_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3590_);
            v_head_3593_ = crate::leanh::lean_ctor_get(v_x_3589_, 0);
            crate::leanh::lean_inc(v_head_3593_);
            crate::leanh::lean_dec_ref_known(v_x_3589_, 2);
            return v_head_3593_;
        } else {
            let mut v_head_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3592_);
            v_head_3594_ = crate::leanh::lean_ctor_get(v_x_3589_, 0);
            crate::leanh::lean_inc(v_head_3594_);
            crate::leanh::lean_dec_ref_known(v_x_3589_, 2);
            v___x_3595_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7_spec__10(v_x_3590_, v_head_3594_, v_tail_3592_);
            return v___x_3595_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__0;
    v___x_3599_ = lean_string_length(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3600_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__2);
    v___x_3601_ = lean_nat_to_int(v___x_3600_);
    return v___x_3601_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(
    mut v_x_3606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3607_ = crate::leanh::lean_ctor_get(v_x_3606_, 0);
                v_snd_3608_ = crate::leanh::lean_ctor_get(v_x_3606_, 1);
                v_isSharedCheck_3631_ = (!crate::leanh::lean_is_exclusive(v_x_3606_)) as u8;
                if v_isSharedCheck_3631_ == 0 {
                    v___x_3610_ = v_x_3606_;
                    v_isShared_3611_ = v_isSharedCheck_3631_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3608_);
                    crate::leanh::lean_inc(v_fst_3607_);
                    crate::leanh::lean_dec(v_x_3606_);
                    v___x_3610_ = crate::leanh::lean_box(0);
                    v_isShared_3611_ = v_isSharedCheck_3631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3612_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3613_ = l_Lean_Name_reprPrec(v_fst_3607_, v___x_3612_);
                v___x_3614_ = crate::leanh::lean_box(0);
                if v_isShared_3611_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3610_, 1);
                    crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3614_);
                    crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3613_);
                    v___x_3616_ = v___x_3610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___x_3614_);
                    v___x_3616_ = v_reuseFailAlloc_3630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3617_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(v_snd_3608_);
                v___x_3618_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3618_, 0, v___x_3617_);
                crate::leanh::lean_ctor_set(v___x_3618_, 1, v___x_3616_);
                v___x_3619_ = l_List_reverse___redArg(v___x_3618_);
                v___x_3620_ = l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3;
                v___x_3621_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__7(v___x_3619_, v___x_3620_);
                v___x_3622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__3);
                v___x_3623_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__4;
                v___x_3624_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
                crate::leanh::lean_ctor_set(v___x_3624_, 1, v___x_3621_);
                v___x_3625_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg___closed__5;
                v___x_3626_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3624_);
                crate::leanh::lean_ctor_set(v___x_3626_, 1, v___x_3625_);
                v___x_3627_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3627_, 0, v___x_3622_);
                crate::leanh::lean_ctor_set(v___x_3627_, 1, v___x_3626_);
                v___x_3628_ = 0;
                v___x_3629_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3629_, 0, v___x_3627_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3628_,
                );
                return v___x_3629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9_spec__13(
    mut v_x_3632_: *mut crate::leanh::LeanObject,
    mut v_x_3633_: *mut crate::leanh::LeanObject,
    mut v_x_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3634_) == 0 {
                    crate::leanh::lean_dec(v_x_3632_);
                    return v_x_3633_;
                } else {
                    v_head_3635_ = crate::leanh::lean_ctor_get(v_x_3634_, 0);
                    v_tail_3636_ = crate::leanh::lean_ctor_get(v_x_3634_, 1);
                    v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v_x_3634_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3638_ = v_x_3634_;
                        v_isShared_3639_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3636_);
                        crate::leanh::lean_inc(v_head_3635_);
                        crate::leanh::lean_dec(v_x_3634_);
                        v___x_3638_ = crate::leanh::lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3632_);
                if v_isShared_3639_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3638_, 5);
                    crate::leanh::lean_ctor_set(v___x_3638_, 1, v_x_3632_);
                    crate::leanh::lean_ctor_set(v___x_3638_, 0, v_x_3633_);
                    v___x_3641_ = v___x_3638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_x_3633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_x_3632_);
                    v___x_3641_ = v_reuseFailAlloc_3645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3642_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_3635_);
                v___x_3643_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                crate::leanh::lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                v_x_3633_ = v___x_3643_;
                v_x_3634_ = v_tail_3636_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9(
    mut v_x_3647_: *mut crate::leanh::LeanObject,
    mut v_x_3648_: *mut crate::leanh::LeanObject,
    mut v_x_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3649_) == 0 {
                    crate::leanh::lean_dec(v_x_3647_);
                    return v_x_3648_;
                } else {
                    v_head_3650_ = crate::leanh::lean_ctor_get(v_x_3649_, 0);
                    v_tail_3651_ = crate::leanh::lean_ctor_get(v_x_3649_, 1);
                    v_isSharedCheck_3661_ = (!crate::leanh::lean_is_exclusive(v_x_3649_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3653_ = v_x_3649_;
                        v_isShared_3654_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3651_);
                        crate::leanh::lean_inc(v_head_3650_);
                        crate::leanh::lean_dec(v_x_3649_);
                        v___x_3653_ = crate::leanh::lean_box(0);
                        v_isShared_3654_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3647_);
                if v_isShared_3654_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3653_, 5);
                    crate::leanh::lean_ctor_set(v___x_3653_, 1, v_x_3647_);
                    crate::leanh::lean_ctor_set(v___x_3653_, 0, v_x_3648_);
                    v___x_3656_ = v___x_3653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_x_3648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_x_3647_);
                    v___x_3656_ = v_reuseFailAlloc_3660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3657_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_3650_);
                v___x_3658_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3658_, 0, v___x_3656_);
                crate::leanh::lean_ctor_set(v___x_3658_, 1, v___x_3657_);
                v___x_3659_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9_spec__13(v_x_3647_, v___x_3658_, v_tail_3651_);
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3(
    mut v_x_3662_: *mut crate::leanh::LeanObject,
    mut v_x_3663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3662_) == 0 {
        let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3663_);
        v___x_3664_ = crate::leanh::lean_box(0);
        return v___x_3664_;
    } else {
        let mut v_tail_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3665_ = crate::leanh::lean_ctor_get(v_x_3662_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3665_) == 0 {
            let mut v_head_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3663_);
            v_head_3666_ = crate::leanh::lean_ctor_get(v_x_3662_, 0);
            crate::leanh::lean_inc(v_head_3666_);
            crate::leanh::lean_dec_ref_known(v_x_3662_, 2);
            v___x_3667_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_3666_);
            return v___x_3667_;
        } else {
            let mut v_head_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3665_);
            v_head_3668_ = crate::leanh::lean_ctor_get(v_x_3662_, 0);
            crate::leanh::lean_inc(v_head_3668_);
            crate::leanh::lean_dec_ref_known(v_x_3662_, 2);
            v___x_3669_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_head_3668_);
            v___x_3670_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3_spec__9(v_x_3663_, v___x_3669_, v_tail_3665_);
            return v___x_3670_;
        }
    }
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(
    mut v_a_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3671_) == 0 {
        let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3672_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__1;
        return v___x_3672_;
    } else {
        let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3681_: u8 = 0;
        let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3673_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__3;
        v___x_3674_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__3(v_a_3671_, v___x_3673_);
        v___x_3675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4_once), _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__4);
        v___x_3676_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg___closed__5;
        v___x_3677_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3677_, 0, v___x_3676_);
        crate::leanh::lean_ctor_set(v___x_3677_, 1, v___x_3674_);
        v___x_3678_ =
            l_Array_repr___at___00Lean_Meta_instReprSimpCongrTheorem_repr_spec__0___closed__8;
        v___x_3679_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3679_, 0, v___x_3677_);
        crate::leanh::lean_ctor_set(v___x_3679_, 1, v___x_3678_);
        v___x_3680_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3680_, 0, v___x_3675_);
        crate::leanh::lean_ctor_set(v___x_3680_, 1, v___x_3679_);
        v___x_3681_ = 0;
        v___x_3682_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_3682_, 0, v___x_3680_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_3682_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_3681_,
        );
        return v___x_3682_;
    }
}
pub unsafe fn _init_l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_3693_ = lean_nat_to_int(v___x_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(
    mut v_x_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: u8 = 0;
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3698_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__3;
    v___x_3699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__4,
    );
    v___x_3700_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3701_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(
            v_x_3697_,
        );
    v___x_3702_ =
        l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(v___x_3701_);
    v___x_3703_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___closed__6;
    v___x_3704_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3704_, 0, v___x_3702_);
    crate::leanh::lean_ctor_set(v___x_3704_, 1, v___x_3703_);
    v___x_3705_ = l_Repr_addAppParen(v___x_3704_, v___x_3700_);
    v___x_3706_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3706_, 0, v___x_3699_);
    crate::leanh::lean_ctor_set(v___x_3706_, 1, v___x_3705_);
    v___x_3707_ = 0;
    v___x_3708_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3708_, 0, v___x_3706_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3708_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3707_,
    );
    v___x_3709_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3709_, 0, v___x_3698_);
    crate::leanh::lean_ctor_set(v___x_3709_, 1, v___x_3708_);
    v___x_3710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19_once
        ),
        _init_l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__19,
    );
    v___x_3711_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__20;
    v___x_3712_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3712_, 0, v___x_3711_);
    crate::leanh::lean_ctor_set(v___x_3712_, 1, v___x_3709_);
    v___x_3713_ = l_Lean_Meta_instReprSimpCongrTheorem_repr___redArg___closed__21;
    v___x_3714_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3714_, 0, v___x_3712_);
    crate::leanh::lean_ctor_set(v___x_3714_, 1, v___x_3713_);
    v___x_3715_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3715_, 0, v___x_3710_);
    crate::leanh::lean_ctor_set(v___x_3715_, 1, v___x_3714_);
    v___x_3716_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3715_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3716_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3707_,
    );
    return v___x_3716_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg___boxed(
    mut v_x_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3718_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(v_x_3717_);
    crate::leanh::lean_dec_ref(v_x_3717_);
    return v_res_3718_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorems_repr(
    mut v_x_3719_: *mut crate::leanh::LeanObject,
    mut v_prec_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_Lean_Meta_instReprSimpCongrTheorems_repr___redArg(v_x_3719_);
    return v___x_3721_;
}
pub unsafe fn l_Lean_Meta_instReprSimpCongrTheorems_repr___boxed(
    mut v_x_3722_: *mut crate::leanh::LeanObject,
    mut v_prec_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_Lean_Meta_instReprSimpCongrTheorems_repr(v_x_3722_, v_prec_3723_);
    crate::leanh::lean_dec(v_prec_3723_);
    crate::leanh::lean_dec_ref(v_x_3722_);
    return v_res_3724_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0(
    mut v_00_u03b2_3725_: *mut crate::leanh::LeanObject,
    mut v_m_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ =
        l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___redArg(
            v_m_3726_,
        );
    return v___x_3727_;
}
pub unsafe fn l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0___boxed(
    mut v_00_u03b2_3728_: *mut crate::leanh::LeanObject,
    mut v_m_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0(
        v_00_u03b2_3728_,
        v_m_3729_,
    );
    crate::leanh::lean_dec_ref(v_m_3729_);
    return v_res_3730_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1(
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v_n_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ =
        l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___redArg(v_a_3731_);
    return v___x_3733_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1___boxed(
    mut v_a_3734_: *mut crate::leanh::LeanObject,
    mut v_n_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3736_ =
        l_List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1(v_a_3734_, v_n_3735_);
    crate::leanh::lean_dec(v_n_3735_);
    return v_res_3736_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0(
    mut v_00_u03b2_3737_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3738_: *mut crate::leanh::LeanObject,
    mut v_f_3739_: *mut crate::leanh::LeanObject,
    mut v_init_3740_: *mut crate::leanh::LeanObject,
    mut v_m_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3742_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___redArg(v_f_3739_, v_init_3740_, v_m_3741_);
    return v___x_3742_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0___boxed(
    mut v_00_u03b2_3743_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3744_: *mut crate::leanh::LeanObject,
    mut v_f_3745_: *mut crate::leanh::LeanObject,
    mut v_init_3746_: *mut crate::leanh::LeanObject,
    mut v_m_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3748_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0(v_00_u03b2_3743_, v_00_u03c3_3744_, v_f_3745_, v_init_3746_, v_m_3747_);
    crate::leanh::lean_dec_ref(v_m_3747_);
    return v_res_3748_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2(
    mut v_x_3749_: *mut crate::leanh::LeanObject,
    mut v_x_3750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___redArg(v_x_3749_);
    return v___x_3751_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2___boxed(
    mut v_x_3752_: *mut crate::leanh::LeanObject,
    mut v_x_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2(v_x_3752_, v_x_3753_);
    crate::leanh::lean_dec(v_x_3753_);
    return v_res_3754_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3755_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3756_: *mut crate::leanh::LeanObject,
    mut v_f_3757_: *mut crate::leanh::LeanObject,
    mut v_x_3758_: *mut crate::leanh::LeanObject,
    mut v_x_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3760_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__1___redArg(v_f_3757_, v_x_3758_, v_x_3759_);
    return v___x_3760_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2(
    mut v_00_u03c3_3761_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3762_: *mut crate::leanh::LeanObject,
    mut v_map_3763_: *mut crate::leanh::LeanObject,
    mut v_f_3764_: *mut crate::leanh::LeanObject,
    mut v_init_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___redArg(v_map_3763_, v_f_3764_, v_init_3765_);
    return v___x_3766_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03c3_3767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3768_: *mut crate::leanh::LeanObject,
    mut v_map_3769_: *mut crate::leanh::LeanObject,
    mut v_f_3770_: *mut crate::leanh::LeanObject,
    mut v_init_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2(v_00_u03c3_3767_, v_00_u03b2_3768_, v_map_3769_, v_f_3770_, v_init_3771_);
    crate::leanh::lean_dec_ref(v_map_3769_);
    return v_res_3772_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3(
    mut v_00_u03b2_3773_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3774_: *mut crate::leanh::LeanObject,
    mut v_f_3775_: *mut crate::leanh::LeanObject,
    mut v_as_3776_: *mut crate::leanh::LeanObject,
    mut v_i_3777_: usize,
    mut v_stop_3778_: usize,
    mut v_b_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___redArg(v_f_3775_, v_as_3776_, v_i_3777_, v_stop_3778_, v_b_3779_);
    return v___x_3780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_3781_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3782_: *mut crate::leanh::LeanObject,
    mut v_f_3783_: *mut crate::leanh::LeanObject,
    mut v_as_3784_: *mut crate::leanh::LeanObject,
    mut v_i_3785_: *mut crate::leanh::LeanObject,
    mut v_stop_3786_: *mut crate::leanh::LeanObject,
    mut v_b_3787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3788_: usize = 0;
    let mut v_stop_boxed_3789_: usize = 0;
    let mut v_res_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3788_ = crate::leanh::lean_unbox_usize(v_i_3785_);
    crate::leanh::lean_dec(v_i_3785_);
    v_stop_boxed_3789_ = crate::leanh::lean_unbox_usize(v_stop_3786_);
    crate::leanh::lean_dec(v_stop_3786_);
    v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__3(v_00_u03b2_3781_, v_00_u03c3_3782_, v_f_3783_, v_as_3784_, v_i_boxed_3788_, v_stop_boxed_3789_, v_b_3787_);
    crate::leanh::lean_dec_ref(v_as_3784_);
    return v_res_3790_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6(
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_n_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___redArg(v_a_3791_);
    return v___x_3793_;
}
pub unsafe fn l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6___boxed(
    mut v_a_3794_: *mut crate::leanh::LeanObject,
    mut v_n_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3796_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__1_spec__2_spec__6(v_a_3794_, v_n_3795_);
    crate::leanh::lean_dec(v_n_3795_);
    return v_res_3796_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_map_3797_: *mut crate::leanh::LeanObject,
    mut v_f_3798_: *mut crate::leanh::LeanObject,
    mut v_init_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_3798_, v_map_3797_, v_init_3799_);
    return v___x_3800_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_map_3801_: *mut crate::leanh::LeanObject,
    mut v_f_3802_: *mut crate::leanh::LeanObject,
    mut v_init_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_3801_, v_f_3802_, v_init_3803_);
    crate::leanh::lean_dec_ref(v_map_3801_);
    return v_res_3804_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03c3_3805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3806_: *mut crate::leanh::LeanObject,
    mut v_map_3807_: *mut crate::leanh::LeanObject,
    mut v_f_3808_: *mut crate::leanh::LeanObject,
    mut v_init_3809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_3808_, v_map_3807_, v_init_3809_);
    return v___x_3810_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03c3_3811_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3812_: *mut crate::leanh::LeanObject,
    mut v_map_3813_: *mut crate::leanh::LeanObject,
    mut v_f_3814_: *mut crate::leanh::LeanObject,
    mut v_init_3815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3816_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_3811_, v_00_u03b2_3812_, v_map_3813_, v_f_3814_, v_init_3815_);
    crate::leanh::lean_dec_ref(v_map_3813_);
    return v_res_3816_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7(
    mut v_00_u03c3_3817_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3818_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3819_: *mut crate::leanh::LeanObject,
    mut v_f_3820_: *mut crate::leanh::LeanObject,
    mut v_x_3821_: *mut crate::leanh::LeanObject,
    mut v_x_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_3820_, v_x_3821_, v_x_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03c3_3824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3826_: *mut crate::leanh::LeanObject,
    mut v_f_3827_: *mut crate::leanh::LeanObject,
    mut v_x_3828_: *mut crate::leanh::LeanObject,
    mut v_x_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3830_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_3824_, v_00_u03b1_3825_, v_00_u03b2_3826_, v_f_3827_, v_x_3828_, v_x_3829_);
    crate::leanh::lean_dec_ref(v_x_3828_);
    return v_res_3830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(
    mut v_00_u03b1_3831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3832_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3833_: *mut crate::leanh::LeanObject,
    mut v_f_3834_: *mut crate::leanh::LeanObject,
    mut v_as_3835_: *mut crate::leanh::LeanObject,
    mut v_i_3836_: usize,
    mut v_stop_3837_: usize,
    mut v_b_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_3834_, v_as_3835_, v_i_3836_, v_stop_3837_, v_b_3838_);
    return v___x_3839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(
    mut v_00_u03b1_3840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3841_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3842_: *mut crate::leanh::LeanObject,
    mut v_f_3843_: *mut crate::leanh::LeanObject,
    mut v_as_3844_: *mut crate::leanh::LeanObject,
    mut v_i_3845_: *mut crate::leanh::LeanObject,
    mut v_stop_3846_: *mut crate::leanh::LeanObject,
    mut v_b_3847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3848_: usize = 0;
    let mut v_stop_boxed_3849_: usize = 0;
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3848_ = crate::leanh::lean_unbox_usize(v_i_3845_);
    crate::leanh::lean_dec(v_i_3845_);
    v_stop_boxed_3849_ = crate::leanh::lean_unbox_usize(v_stop_3846_);
    crate::leanh::lean_dec(v_stop_3846_);
    v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_3840_, v_00_u03b2_3841_, v_00_u03c3_3842_, v_f_3843_, v_as_3844_, v_i_boxed_3848_, v_stop_boxed_3849_, v_b_3847_);
    crate::leanh::lean_dec_ref(v_as_3844_);
    return v_res_3850_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(
    mut v_00_u03c3_3851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3852_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3853_: *mut crate::leanh::LeanObject,
    mut v_f_3854_: *mut crate::leanh::LeanObject,
    mut v_keys_3855_: *mut crate::leanh::LeanObject,
    mut v_vals_3856_: *mut crate::leanh::LeanObject,
    mut v_heq_3857_: *mut crate::leanh::LeanObject,
    mut v_i_3858_: *mut crate::leanh::LeanObject,
    mut v_acc_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_3854_, v_keys_3855_, v_vals_3856_, v_i_3858_, v_acc_3859_);
    return v___x_3860_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(
    mut v_00_u03c3_3861_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3863_: *mut crate::leanh::LeanObject,
    mut v_f_3864_: *mut crate::leanh::LeanObject,
    mut v_keys_3865_: *mut crate::leanh::LeanObject,
    mut v_vals_3866_: *mut crate::leanh::LeanObject,
    mut v_heq_3867_: *mut crate::leanh::LeanObject,
    mut v_i_3868_: *mut crate::leanh::LeanObject,
    mut v_acc_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprSimpCongrTheorems_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_3861_, v_00_u03b1_3862_, v_00_u03b2_3863_, v_f_3864_, v_keys_3865_, v_vals_3866_, v_heq_3867_, v_i_3868_, v_acc_3869_);
    crate::leanh::lean_dec_ref(v_vals_3866_);
    crate::leanh::lean_dec_ref(v_keys_3865_);
    return v_res_3870_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_x_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3874_) == 0 {
                    v___x_3875_ = crate::leanh::lean_box(0);
                    return v___x_3875_;
                } else {
                    v_key_3876_ = crate::leanh::lean_ctor_get(v_x_3874_, 0);
                    v_value_3877_ = crate::leanh::lean_ctor_get(v_x_3874_, 1);
                    v_tail_3878_ = crate::leanh::lean_ctor_get(v_x_3874_, 2);
                    v___x_3879_ = lean_name_eq(v_key_3876_, v_a_3873_);
                    if v___x_3879_ == 0 {
                        v_x_3874_ = v_tail_3878_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3877_);
                        v___x_3881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3881_, 0, v_value_3877_);
                        return v___x_3881_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3882_: *mut crate::leanh::LeanObject,
    mut v_x_3883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_3882_, v_x_3883_);
    crate::leanh::lean_dec(v_x_3883_);
    crate::leanh::lean_dec(v_a_3882_);
    return v_res_3884_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: u64 = 0;
    v___x_3885_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3886_ = lean_uint64_of_nat(v___x_3885_);
    return v___x_3886_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(
    mut v_m_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: u64 = 0;
    let mut v___x_3893_: u64 = 0;
    let mut v___x_3894_: u64 = 0;
    let mut v_fold_3895_: u64 = 0;
    let mut v___x_3896_: u64 = 0;
    let mut v___x_3897_: u64 = 0;
    let mut v___x_3898_: u64 = 0;
    let mut v___x_3899_: usize = 0;
    let mut v___x_3900_: usize = 0;
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v___x_3903_: usize = 0;
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u64 = 0;
    let mut v_hash_3907_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3889_ = crate::leanh::lean_ctor_get(v_m_3887_, 1);
                v___x_3890_ = lean_array_get_size(v_buckets_3889_);
                if crate::leanh::lean_obj_tag(v_a_3888_) == 0 {
                    v___x_3906_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                    v___y_3892_ = v___x_3906_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3907_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3888_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3892_ = v_hash_3907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3893_ = 32u64;
                v___x_3894_ = lean_uint64_shift_right(v___y_3892_, v___x_3893_);
                v_fold_3895_ = lean_uint64_xor(v___y_3892_, v___x_3894_);
                v___x_3896_ = 16u64;
                v___x_3897_ = lean_uint64_shift_right(v_fold_3895_, v___x_3896_);
                v___x_3898_ = lean_uint64_xor(v_fold_3895_, v___x_3897_);
                v___x_3899_ = lean_uint64_to_usize(v___x_3898_);
                v___x_3900_ = lean_usize_of_nat(v___x_3890_);
                v___x_3901_ = 1usize;
                v___x_3902_ = lean_usize_sub(v___x_3900_, v___x_3901_);
                v___x_3903_ = lean_usize_land(v___x_3899_, v___x_3902_);
                v___x_3904_ = lean_array_uget_borrowed(v_buckets_3889_, v___x_3903_);
                v___x_3905_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_3888_, v___x_3904_);
                return v___x_3905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___boxed(
    mut v_m_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_m_3908_, v_a_3909_);
    crate::leanh::lean_dec(v_a_3909_);
    crate::leanh::lean_dec_ref(v_m_3908_);
    return v_res_3910_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_3911_: *mut crate::leanh::LeanObject,
    mut v_vals_3912_: *mut crate::leanh::LeanObject,
    mut v_i_3913_: *mut crate::leanh::LeanObject,
    mut v_k_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3915_ = lean_array_get_size(v_keys_3911_);
                v___x_3916_ = lean_nat_dec_lt(v_i_3913_, v___x_3915_);
                if v___x_3916_ == 0 {
                    crate::leanh::lean_dec(v_i_3913_);
                    v___x_3917_ = crate::leanh::lean_box(0);
                    return v___x_3917_;
                } else {
                    v_k_x27_3918_ = lean_array_fget_borrowed(v_keys_3911_, v_i_3913_);
                    v___x_3919_ = lean_name_eq(v_k_3914_, v_k_x27_3918_);
                    if v___x_3919_ == 0 {
                        v___x_3920_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3921_ = lean_nat_add(v_i_3913_, v___x_3920_);
                        crate::leanh::lean_dec(v_i_3913_);
                        v_i_3913_ = v___x_3921_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3923_ = lean_array_fget_borrowed(v_vals_3912_, v_i_3913_);
                        crate::leanh::lean_dec(v_i_3913_);
                        crate::leanh::lean_inc(v___x_3923_);
                        v___x_3924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3923_);
                        return v___x_3924_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_3925_: *mut crate::leanh::LeanObject,
    mut v_vals_3926_: *mut crate::leanh::LeanObject,
    mut v_i_3927_: *mut crate::leanh::LeanObject,
    mut v_k_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_3925_, v_vals_3926_, v_i_3927_, v_k_3928_);
    crate::leanh::lean_dec(v_k_3928_);
    crate::leanh::lean_dec_ref(v_vals_3926_);
    crate::leanh::lean_dec_ref(v_keys_3925_);
    return v_res_3929_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_3930_: usize = 0;
    let mut v___x_3931_: usize = 0;
    let mut v___x_3932_: usize = 0;
    v___x_3930_ = 5usize;
    v___x_3931_ = 1usize;
    v___x_3932_ = lean_usize_shift_left(v___x_3931_, v___x_3930_);
    return v___x_3932_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_3933_: usize = 0;
    let mut v___x_3934_: usize = 0;
    let mut v___x_3935_: usize = 0;
    v___x_3933_ = 1usize;
    v___x_3934_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_3935_ = lean_usize_sub(v___x_3934_, v___x_3933_);
    return v___x_3935_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(
    mut v_x_3936_: *mut crate::leanh::LeanObject,
    mut v_x_3937_: usize,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: usize = 0;
    let mut v___x_3942_: usize = 0;
    let mut v___x_3943_: usize = 0;
    let mut v_j_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: usize = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3936_) == 0 {
                    v_es_3939_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                    v___x_3940_ = crate::leanh::lean_box(2);
                    v___x_3941_ = 5usize;
                    v___x_3942_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3943_ = lean_usize_land(v_x_3937_, v___x_3942_);
                    v_j_3944_ = lean_usize_to_nat(v___x_3943_);
                    v___x_3945_ = lean_array_get_borrowed(v___x_3940_, v_es_3939_, v_j_3944_);
                    crate::leanh::lean_dec(v_j_3944_);
                    match crate::leanh::lean_obj_tag(v___x_3945_) {
                        0 => {
                            v_key_3946_ = crate::leanh::lean_ctor_get(v___x_3945_, 0);
                            v_val_3947_ = crate::leanh::lean_ctor_get(v___x_3945_, 1);
                            v___x_3948_ = lean_name_eq(v_x_3938_, v_key_3946_);
                            if v___x_3948_ == 0 {
                                v___x_3949_ = crate::leanh::lean_box(0);
                                return v___x_3949_;
                            } else {
                                crate::leanh::lean_inc(v_val_3947_);
                                v___x_3950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3950_, 0, v_val_3947_);
                                return v___x_3950_;
                            }
                        }
                        1 => {
                            v_node_3951_ = crate::leanh::lean_ctor_get(v___x_3945_, 0);
                            v___x_3952_ = lean_usize_shift_right(v_x_3937_, v___x_3941_);
                            v_x_3936_ = v_node_3951_;
                            v_x_3937_ = v___x_3952_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3954_ = crate::leanh::lean_box(0);
                            return v___x_3954_;
                        }
                    }
                } else {
                    v_ks_3955_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                    v_vs_3956_ = crate::leanh::lean_ctor_get(v_x_3936_, 1);
                    v___x_3957_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_3955_, v_vs_3956_, v___x_3957_, v_x_3938_);
                    return v___x_3958_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3959_: *mut crate::leanh::LeanObject,
    mut v_x_3960_: *mut crate::leanh::LeanObject,
    mut v_x_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_337__boxed_3962_: usize = 0;
    let mut v_res_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_337__boxed_3962_ = crate::leanh::lean_unbox_usize(v_x_3960_);
    crate::leanh::lean_dec(v_x_3960_);
    v_res_3963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_3959_, v_x_337__boxed_3962_, v_x_3961_);
    crate::leanh::lean_dec(v_x_3961_);
    crate::leanh::lean_dec_ref(v_x_3959_);
    return v_res_3963_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(
    mut v_x_3964_: *mut crate::leanh::LeanObject,
    mut v_x_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3967_: u64 = 0;
    let mut v___x_3968_: usize = 0;
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: u64 = 0;
    let mut v_hash_3971_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3965_) == 0 {
                    v___x_3970_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                    v___y_3967_ = v___x_3970_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3971_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3967_ = v_hash_3971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3968_ = lean_uint64_to_usize(v___y_3967_);
                v___x_3969_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_3964_, v___x_3968_, v_x_3965_);
                return v___x_3969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg___boxed(
    mut v_x_3972_: *mut crate::leanh::LeanObject,
    mut v_x_3973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_3972_, v_x_3973_);
    crate::leanh::lean_dec(v_x_3973_);
    crate::leanh::lean_dec_ref(v_x_3972_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_3977_: u8 = 0;
    v_stage_u2081_3977_ = crate::leanh::lean_ctor_get_uint8(
        v_x_3975_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_3977_ == 0 {
        let mut v_map_u2081_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_3978_ = crate::leanh::lean_ctor_get(v_x_3975_, 0);
        v_map_u2082_3979_ = crate::leanh::lean_ctor_get(v_x_3975_, 1);
        v___x_3980_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_map_u2082_3979_, v_x_3976_);
        if crate::leanh::lean_obj_tag(v___x_3980_) == 0 {
            let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_3978_, v_x_3976_);
            return v___x_3981_;
        } else {
            return v___x_3980_;
        }
    } else {
        let mut v_map_u2081_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_3982_ = crate::leanh::lean_ctor_get(v_x_3975_, 0);
        v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_map_u2081_3982_, v_x_3976_);
        return v___x_3983_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg___boxed(
    mut v_x_3984_: *mut crate::leanh::LeanObject,
    mut v_x_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(
        v_x_3984_, v_x_3985_,
    );
    crate::leanh::lean_dec(v_x_3985_);
    crate::leanh::lean_dec_ref(v_x_3984_);
    return v_res_3986_;
}
pub unsafe fn l_Lean_Meta_SimpCongrTheorems_get(
    mut v_d_3987_: *mut crate::leanh::LeanObject,
    mut v_declName_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3989_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(
        v_d_3987_,
        v_declName_3988_,
    );
    if crate::leanh::lean_obj_tag(v___x_3989_) == 0 {
        let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3990_ = crate::leanh::lean_box(0);
        return v___x_3990_;
    } else {
        let mut v_val_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3991_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
        crate::leanh::lean_inc(v_val_3991_);
        crate::leanh::lean_dec_ref_known(v___x_3989_, 1);
        return v_val_3991_;
    }
}
pub unsafe fn l_Lean_Meta_SimpCongrTheorems_get___boxed(
    mut v_d_3992_: *mut crate::leanh::LeanObject,
    mut v_declName_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3994_ = l_Lean_Meta_SimpCongrTheorems_get(v_d_3992_, v_declName_3993_);
    crate::leanh::lean_dec(v_declName_3993_);
    crate::leanh::lean_dec_ref(v_d_3992_);
    return v_res_3994_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(
    mut v_00_u03b2_3995_: *mut crate::leanh::LeanObject,
    mut v_x_3996_: *mut crate::leanh::LeanObject,
    mut v_x_3997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(
        v_x_3996_, v_x_3997_,
    );
    return v___x_3998_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___boxed(
    mut v_00_u03b2_3999_: *mut crate::leanh::LeanObject,
    mut v_x_4000_: *mut crate::leanh::LeanObject,
    mut v_x_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4002_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0(
        v_00_u03b2_3999_,
        v_x_4000_,
        v_x_4001_,
    );
    crate::leanh::lean_dec(v_x_4001_);
    crate::leanh::lean_dec_ref(v_x_4000_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(
    mut v_00_u03b2_4003_: *mut crate::leanh::LeanObject,
    mut v_x_4004_: *mut crate::leanh::LeanObject,
    mut v_x_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4006_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___redArg(v_x_4004_, v_x_4005_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0___boxed(
    mut v_00_u03b2_4007_: *mut crate::leanh::LeanObject,
    mut v_x_4008_: *mut crate::leanh::LeanObject,
    mut v_x_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4010_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0(v_00_u03b2_4007_, v_x_4008_, v_x_4009_);
    crate::leanh::lean_dec(v_x_4009_);
    crate::leanh::lean_dec_ref(v_x_4008_);
    return v_res_4010_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(
    mut v_00_u03b2_4011_: *mut crate::leanh::LeanObject,
    mut v_m_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg(v_m_4012_, v_a_4013_);
    return v___x_4014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___boxed(
    mut v_00_u03b2_4015_: *mut crate::leanh::LeanObject,
    mut v_m_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1(v_00_u03b2_4015_, v_m_4016_, v_a_4017_);
    crate::leanh::lean_dec(v_a_4017_);
    crate::leanh::lean_dec_ref(v_m_4016_);
    return v_res_4018_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4019_: *mut crate::leanh::LeanObject,
    mut v_x_4020_: *mut crate::leanh::LeanObject,
    mut v_x_4021_: usize,
    mut v_x_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg(v_x_4020_, v_x_4021_, v_x_4022_);
    return v___x_4023_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4024_: *mut crate::leanh::LeanObject,
    mut v_x_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_454__boxed_4028_: usize = 0;
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_454__boxed_4028_ = crate::leanh::lean_unbox_usize(v_x_4026_);
    crate::leanh::lean_dec(v_x_4026_);
    v_res_4029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1(v_00_u03b2_4024_, v_x_4025_, v_x_454__boxed_4028_, v_x_4027_);
    crate::leanh::lean_dec(v_x_4027_);
    crate::leanh::lean_dec_ref(v_x_4025_);
    return v_res_4029_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_x_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___redArg(v_a_4031_, v_x_4032_);
    return v___x_4033_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_x_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1_spec__3(v_00_u03b2_4034_, v_a_4035_, v_x_4036_);
    crate::leanh::lean_dec(v_x_4036_);
    crate::leanh::lean_dec(v_a_4035_);
    return v_res_4037_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4038_: *mut crate::leanh::LeanObject,
    mut v_keys_4039_: *mut crate::leanh::LeanObject,
    mut v_vals_4040_: *mut crate::leanh::LeanObject,
    mut v_heq_4041_: *mut crate::leanh::LeanObject,
    mut v_i_4042_: *mut crate::leanh::LeanObject,
    mut v_k_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4039_, v_vals_4040_, v_i_4042_, v_k_4043_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4045_: *mut crate::leanh::LeanObject,
    mut v_keys_4046_: *mut crate::leanh::LeanObject,
    mut v_vals_4047_: *mut crate::leanh::LeanObject,
    mut v_heq_4048_: *mut crate::leanh::LeanObject,
    mut v_i_4049_: *mut crate::leanh::LeanObject,
    mut v_k_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4045_, v_keys_4046_, v_vals_4047_, v_heq_4048_, v_i_4049_, v_k_4050_);
    crate::leanh::lean_dec(v_k_4050_);
    crate::leanh::lean_dec_ref(v_vals_4047_);
    crate::leanh::lean_dec_ref(v_keys_4046_);
    return v_res_4051_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(
    mut v_e_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_unused_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4053_) == 0 {
                    v___x_4054_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4054_, 0, v_e_4052_);
                    crate::leanh::lean_ctor_set(v___x_4054_, 1, v_a_4053_);
                    return v___x_4054_;
                } else {
                    v_head_4055_ = crate::leanh::lean_ctor_get(v_a_4053_, 0);
                    v_tail_4056_ = crate::leanh::lean_ctor_get(v_a_4053_, 1);
                    v_priority_4057_ = crate::leanh::lean_ctor_get(v_head_4055_, 3);
                    v_priority_4058_ = crate::leanh::lean_ctor_get(v_e_4052_, 3);
                    v___x_4059_ = lean_nat_dec_le(v_priority_4057_, v_priority_4058_);
                    if v___x_4059_ == 0 {
                        crate::leanh::lean_inc(v_tail_4056_);
                        crate::leanh::lean_inc(v_head_4055_);
                        v_isSharedCheck_4067_ = (!crate::leanh::lean_is_exclusive(v_a_4053_)) as u8;
                        if v_isSharedCheck_4067_ == 0 {
                            v_unused_4068_ = crate::leanh::lean_ctor_get(v_a_4053_, 1);
                            crate::leanh::lean_dec(v_unused_4068_);
                            v_unused_4069_ = crate::leanh::lean_ctor_get(v_a_4053_, 0);
                            crate::leanh::lean_dec(v_unused_4069_);
                            v___x_4061_ = v_a_4053_;
                            v_isShared_4062_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4053_);
                            v___x_4061_ = crate::leanh::lean_box(0);
                            v_isShared_4062_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4070_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4070_, 0, v_e_4052_);
                        crate::leanh::lean_ctor_set(v___x_4070_, 1, v_a_4053_);
                        return v___x_4070_;
                    }
                }
            }
            1 => {
                v___x_4063_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_4052_, v_tail_4056_);
                if v_isShared_4062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4061_, 1, v___x_4063_);
                    v___x_4065_ = v___x_4061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_head_4055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(
    mut v_a_4071_: *mut crate::leanh::LeanObject,
    mut v_b_4072_: *mut crate::leanh::LeanObject,
    mut v_x_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4073_) == 0 {
                    crate::leanh::lean_dec(v_b_4072_);
                    crate::leanh::lean_dec(v_a_4071_);
                    return v_x_4073_;
                } else {
                    v_key_4074_ = crate::leanh::lean_ctor_get(v_x_4073_, 0);
                    v_value_4075_ = crate::leanh::lean_ctor_get(v_x_4073_, 1);
                    v_tail_4076_ = crate::leanh::lean_ctor_get(v_x_4073_, 2);
                    v_isSharedCheck_4088_ = (!crate::leanh::lean_is_exclusive(v_x_4073_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4078_ = v_x_4073_;
                        v_isShared_4079_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4076_);
                        crate::leanh::lean_inc(v_value_4075_);
                        crate::leanh::lean_inc(v_key_4074_);
                        crate::leanh::lean_dec(v_x_4073_);
                        v___x_4078_ = crate::leanh::lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4080_ = lean_name_eq(v_key_4074_, v_a_4071_);
                if v___x_4080_ == 0 {
                    v___x_4081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_4071_, v_b_4072_, v_tail_4076_);
                    if v_isShared_4079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4078_, 2, v___x_4081_);
                        v___x_4083_ = v___x_4078_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_key_4074_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_value_4075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 2, v___x_4081_);
                        v___x_4083_ = v_reuseFailAlloc_4084_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4075_);
                    crate::leanh::lean_dec(v_key_4074_);
                    if v_isShared_4079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4078_, 1, v_b_4072_);
                        crate::leanh::lean_ctor_set(v___x_4078_, 0, v_a_4071_);
                        v___x_4086_ = v___x_4078_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4087_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4071_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_b_4072_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_tail_4076_);
                        v___x_4086_ = v_reuseFailAlloc_4087_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4083_;
            }
            3 => {
                return v___x_4086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_4089_: *mut crate::leanh::LeanObject,
    mut v_x_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: u64 = 0;
    let mut v___x_4100_: u64 = 0;
    let mut v___x_4101_: u64 = 0;
    let mut v_fold_4102_: u64 = 0;
    let mut v___x_4103_: u64 = 0;
    let mut v___x_4104_: u64 = 0;
    let mut v___x_4105_: u64 = 0;
    let mut v___x_4106_: usize = 0;
    let mut v___x_4107_: usize = 0;
    let mut v___x_4108_: usize = 0;
    let mut v___x_4109_: usize = 0;
    let mut v___x_4110_: usize = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u64 = 0;
    let mut v_hash_4118_: u64 = 0;
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4090_) == 0 {
                    return v_x_4089_;
                } else {
                    v_key_4091_ = crate::leanh::lean_ctor_get(v_x_4090_, 0);
                    v_value_4092_ = crate::leanh::lean_ctor_get(v_x_4090_, 1);
                    v_tail_4093_ = crate::leanh::lean_ctor_get(v_x_4090_, 2);
                    v_isSharedCheck_4119_ = (!crate::leanh::lean_is_exclusive(v_x_4090_)) as u8;
                    if v_isSharedCheck_4119_ == 0 {
                        v___x_4095_ = v_x_4090_;
                        v_isShared_4096_ = v_isSharedCheck_4119_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4093_);
                        crate::leanh::lean_inc(v_value_4092_);
                        crate::leanh::lean_inc(v_key_4091_);
                        crate::leanh::lean_dec(v_x_4090_);
                        v___x_4095_ = crate::leanh::lean_box(0);
                        v_isShared_4096_ = v_isSharedCheck_4119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4097_ = lean_array_get_size(v_x_4089_);
                if crate::leanh::lean_obj_tag(v_key_4091_) == 0 {
                    v___x_4117_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                    v___y_4099_ = v___x_4117_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4118_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_4091_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4099_ = v_hash_4118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4100_ = 32u64;
                v___x_4101_ = lean_uint64_shift_right(v___y_4099_, v___x_4100_);
                v_fold_4102_ = lean_uint64_xor(v___y_4099_, v___x_4101_);
                v___x_4103_ = 16u64;
                v___x_4104_ = lean_uint64_shift_right(v_fold_4102_, v___x_4103_);
                v___x_4105_ = lean_uint64_xor(v_fold_4102_, v___x_4104_);
                v___x_4106_ = lean_uint64_to_usize(v___x_4105_);
                v___x_4107_ = lean_usize_of_nat(v___x_4097_);
                v___x_4108_ = 1usize;
                v___x_4109_ = lean_usize_sub(v___x_4107_, v___x_4108_);
                v___x_4110_ = lean_usize_land(v___x_4106_, v___x_4109_);
                v___x_4111_ = lean_array_uget_borrowed(v_x_4089_, v___x_4110_);
                crate::leanh::lean_inc(v___x_4111_);
                if v_isShared_4096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4095_, 2, v___x_4111_);
                    v___x_4113_ = v___x_4095_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_key_4091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_value_4092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 2, v___x_4111_);
                    v___x_4113_ = v_reuseFailAlloc_4116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4114_ = lean_array_uset(v_x_4089_, v___x_4110_, v___x_4113_);
                v_x_4089_ = v___x_4114_;
                v_x_4090_ = v_tail_4093_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_4120_: *mut crate::leanh::LeanObject,
    mut v_source_4121_: *mut crate::leanh::LeanObject,
    mut v_target_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: u8 = 0;
    let mut v_es_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4123_ = lean_array_get_size(v_source_4121_);
                v___x_4124_ = lean_nat_dec_lt(v_i_4120_, v___x_4123_);
                if v___x_4124_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4121_);
                    crate::leanh::lean_dec(v_i_4120_);
                    return v_target_4122_;
                } else {
                    v_es_4125_ = lean_array_fget(v_source_4121_, v_i_4120_);
                    v___x_4126_ = crate::leanh::lean_box(0);
                    v_source_4127_ = lean_array_fset(v_source_4121_, v_i_4120_, v___x_4126_);
                    v_target_4128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_4122_, v_es_4125_);
                    v___x_4129_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4130_ = lean_nat_add(v_i_4120_, v___x_4129_);
                    crate::leanh::lean_dec(v_i_4120_);
                    v_i_4120_ = v___x_4130_;
                    v_source_4121_ = v_source_4127_;
                    v_target_4122_ = v_target_4128_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(
    mut v_data_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = lean_array_get_size(v_data_4132_);
    v___x_4134_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4135_ = lean_nat_mul(v___x_4133_, v___x_4134_);
    v___x_4136_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4137_ = crate::leanh::lean_box(0);
    v___x_4138_ = lean_mk_array(v_nbuckets_4135_, v___x_4137_);
    v___x_4139_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_4136_, v_data_4132_, v___x_4138_);
    return v___x_4139_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_x_4141_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4142_: u8 = 0;
    let mut v_key_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4141_) == 0 {
                    v___x_4142_ = 0;
                    return v___x_4142_;
                } else {
                    v_key_4143_ = crate::leanh::lean_ctor_get(v_x_4141_, 0);
                    v_tail_4144_ = crate::leanh::lean_ctor_get(v_x_4141_, 2);
                    v___x_4145_ = lean_name_eq(v_key_4143_, v_a_4140_);
                    if v___x_4145_ == 0 {
                        v_x_4141_ = v_tail_4144_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4145_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v_x_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4149_: u8 = 0;
    let mut v_r_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_4147_, v_x_4148_);
    crate::leanh::lean_dec(v_x_4148_);
    crate::leanh::lean_dec(v_a_4147_);
    v_r_4150_ = crate::leanh::lean_box((v_res_4149_) as usize);
    return v_r_4150_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(
    mut v_m_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_b_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4158_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4161_: u64 = 0;
    let mut v___x_4162_: u64 = 0;
    let mut v___x_4163_: u64 = 0;
    let mut v_fold_4164_: u64 = 0;
    let mut v___x_4165_: u64 = 0;
    let mut v___x_4166_: u64 = 0;
    let mut v___x_4167_: u64 = 0;
    let mut v___x_4168_: usize = 0;
    let mut v___x_4169_: usize = 0;
    let mut v___x_4170_: usize = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: usize = 0;
    let mut v_bkt_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v_val_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u64 = 0;
    let mut v_hash_4200_: u64 = 0;
    let mut v_isSharedCheck_4201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4154_ = crate::leanh::lean_ctor_get(v_m_4151_, 0);
                v_buckets_4155_ = crate::leanh::lean_ctor_get(v_m_4151_, 1);
                v_isSharedCheck_4201_ = (!crate::leanh::lean_is_exclusive(v_m_4151_)) as u8;
                if v_isSharedCheck_4201_ == 0 {
                    v___x_4157_ = v_m_4151_;
                    v_isShared_4158_ = v_isSharedCheck_4201_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4155_);
                    crate::leanh::lean_inc(v_size_4154_);
                    crate::leanh::lean_dec(v_m_4151_);
                    v___x_4157_ = crate::leanh::lean_box(0);
                    v_isShared_4158_ = v_isSharedCheck_4201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4159_ = lean_array_get_size(v_buckets_4155_);
                if crate::leanh::lean_obj_tag(v_a_4152_) == 0 {
                    v___x_4199_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                    v___y_4161_ = v___x_4199_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4200_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4152_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4161_ = v_hash_4200_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4162_ = 32u64;
                v___x_4163_ = lean_uint64_shift_right(v___y_4161_, v___x_4162_);
                v_fold_4164_ = lean_uint64_xor(v___y_4161_, v___x_4163_);
                v___x_4165_ = 16u64;
                v___x_4166_ = lean_uint64_shift_right(v_fold_4164_, v___x_4165_);
                v___x_4167_ = lean_uint64_xor(v_fold_4164_, v___x_4166_);
                v___x_4168_ = lean_uint64_to_usize(v___x_4167_);
                v___x_4169_ = lean_usize_of_nat(v___x_4159_);
                v___x_4170_ = 1usize;
                v___x_4171_ = lean_usize_sub(v___x_4169_, v___x_4170_);
                v___x_4172_ = lean_usize_land(v___x_4168_, v___x_4171_);
                v_bkt_4173_ = lean_array_uget_borrowed(v_buckets_4155_, v___x_4172_);
                v___x_4174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_4152_, v_bkt_4173_);
                if v___x_4174_ == 0 {
                    v___x_4175_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4176_ = lean_nat_add(v_size_4154_, v___x_4175_);
                    crate::leanh::lean_dec(v_size_4154_);
                    crate::leanh::lean_inc(v_bkt_4173_);
                    v___x_4177_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4177_, 0, v_a_4152_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 1, v_b_4153_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 2, v_bkt_4173_);
                    v_buckets_x27_4178_ =
                        lean_array_uset(v_buckets_4155_, v___x_4172_, v___x_4177_);
                    v___x_4179_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4180_ = lean_nat_mul(v_size_x27_4176_, v___x_4179_);
                    v___x_4181_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4182_ = lean_nat_div(v___x_4180_, v___x_4181_);
                    crate::leanh::lean_dec(v___x_4180_);
                    v___x_4183_ = lean_array_get_size(v_buckets_x27_4178_);
                    v___x_4184_ = lean_nat_dec_le(v___x_4182_, v___x_4183_);
                    crate::leanh::lean_dec(v___x_4182_);
                    if v___x_4184_ == 0 {
                        v_val_4185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_4178_);
                        if v_isShared_4158_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4157_, 1, v_val_4185_);
                            crate::leanh::lean_ctor_set(v___x_4157_, 0, v_size_x27_4176_);
                            v___x_4187_ = v___x_4157_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4188_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4188_,
                                0,
                                v_size_x27_4176_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_val_4185_);
                            v___x_4187_ = v_reuseFailAlloc_4188_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4158_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4157_, 1, v_buckets_x27_4178_);
                            crate::leanh::lean_ctor_set(v___x_4157_, 0, v_size_x27_4176_);
                            v___x_4190_ = v___x_4157_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4191_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4191_,
                                0,
                                v_size_x27_4176_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4191_,
                                1,
                                v_buckets_x27_4178_,
                            );
                            v___x_4190_ = v_reuseFailAlloc_4191_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4173_);
                    v___x_4192_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4193_ =
                        lean_array_uset(v_buckets_4155_, v___x_4172_, v___x_4192_);
                    v___x_4194_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_4152_, v_b_4153_, v_bkt_4173_);
                    v___x_4195_ = lean_array_uset(v_buckets_x27_4193_, v___x_4172_, v___x_4194_);
                    if v_isShared_4158_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4157_, 1, v___x_4195_);
                        v___x_4197_ = v___x_4157_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4198_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_size_4154_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 1, v___x_4195_);
                        v___x_4197_ = v_reuseFailAlloc_4198_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4187_;
            }
            4 => {
                return v___x_4190_;
            }
            5 => {
                return v___x_4197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_4202_: *mut crate::leanh::LeanObject,
    mut v_x_4203_: *mut crate::leanh::LeanObject,
    mut v_x_4204_: *mut crate::leanh::LeanObject,
    mut v_x_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4210_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: u8 = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: u8 = 0;
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4206_ = crate::leanh::lean_ctor_get(v_x_4202_, 0);
                v_vs_4207_ = crate::leanh::lean_ctor_get(v_x_4202_, 1);
                v_isSharedCheck_4231_ = (!crate::leanh::lean_is_exclusive(v_x_4202_)) as u8;
                if v_isSharedCheck_4231_ == 0 {
                    v___x_4209_ = v_x_4202_;
                    v_isShared_4210_ = v_isSharedCheck_4231_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4207_);
                    crate::leanh::lean_inc(v_ks_4206_);
                    crate::leanh::lean_dec(v_x_4202_);
                    v___x_4209_ = crate::leanh::lean_box(0);
                    v_isShared_4210_ = v_isSharedCheck_4231_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4211_ = lean_array_get_size(v_ks_4206_);
                v___x_4212_ = lean_nat_dec_lt(v_x_4203_, v___x_4211_);
                if v___x_4212_ == 0 {
                    crate::leanh::lean_dec(v_x_4203_);
                    v___x_4213_ = lean_array_push(v_ks_4206_, v_x_4204_);
                    v___x_4214_ = lean_array_push(v_vs_4207_, v_x_4205_);
                    if v_isShared_4210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4214_);
                        crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4213_);
                        v___x_4216_ = v___x_4209_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4217_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4213_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 1, v___x_4214_);
                        v___x_4216_ = v_reuseFailAlloc_4217_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4218_ = lean_array_fget_borrowed(v_ks_4206_, v_x_4203_);
                    v___x_4219_ = lean_name_eq(v_x_4204_, v_k_x27_4218_);
                    if v___x_4219_ == 0 {
                        if v_isShared_4210_ == 0 {
                            v___x_4221_ = v___x_4209_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4225_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_ks_4206_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_vs_4207_);
                            v___x_4221_ = v_reuseFailAlloc_4225_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4226_ = lean_array_fset(v_ks_4206_, v_x_4203_, v_x_4204_);
                        v___x_4227_ = lean_array_fset(v_vs_4207_, v_x_4203_, v_x_4205_);
                        crate::leanh::lean_dec(v_x_4203_);
                        if v_isShared_4210_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4227_);
                            crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4226_);
                            v___x_4229_ = v___x_4209_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4230_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4226_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
                            v___x_4229_ = v_reuseFailAlloc_4230_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4216_;
            }
            3 => {
                v___x_4222_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4223_ = lean_nat_add(v_x_4203_, v___x_4222_);
                crate::leanh::lean_dec(v_x_4203_);
                v_x_4202_ = v___x_4221_;
                v_x_4203_ = v___x_4223_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_4232_: *mut crate::leanh::LeanObject,
    mut v_k_4233_: *mut crate::leanh::LeanObject,
    mut v_v_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4236_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_4232_, v___x_4235_, v_k_4233_, v_v_4234_);
    return v___x_4236_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4237_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4237_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_4238_: *mut crate::leanh::LeanObject,
    mut v_x_4239_: usize,
    mut v_x_4240_: usize,
    mut v_x_4241_: *mut crate::leanh::LeanObject,
    mut v_x_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: usize = 0;
    let mut v___x_4245_: usize = 0;
    let mut v___x_4246_: usize = 0;
    let mut v___x_4247_: usize = 0;
    let mut v_j_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v_v_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4267_: u8 = 0;
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4274_: u8 = 0;
    let mut v_node_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4279_: usize = 0;
    let mut v___x_4280_: usize = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut v_unused_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: u8 = 0;
    let mut v_ks_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: usize = 0;
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: u8 = 0;
    let mut v_reuseFailAlloc_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4238_) == 0 {
                    v_es_4243_ = crate::leanh::lean_ctor_get(v_x_4238_, 0);
                    v___x_4244_ = 5usize;
                    v___x_4245_ = 1usize;
                    v___x_4246_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4247_ = lean_usize_land(v_x_4239_, v___x_4246_);
                    v_j_4248_ = lean_usize_to_nat(v___x_4247_);
                    v___x_4249_ = lean_array_get_size(v_es_4243_);
                    v___x_4250_ = lean_nat_dec_lt(v_j_4248_, v___x_4249_);
                    if v___x_4250_ == 0 {
                        crate::leanh::lean_dec(v_j_4248_);
                        crate::leanh::lean_dec(v_x_4242_);
                        crate::leanh::lean_dec(v_x_4241_);
                        return v_x_4238_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4243_);
                        v_isSharedCheck_4287_ = (!crate::leanh::lean_is_exclusive(v_x_4238_)) as u8;
                        if v_isSharedCheck_4287_ == 0 {
                            v_unused_4288_ = crate::leanh::lean_ctor_get(v_x_4238_, 0);
                            crate::leanh::lean_dec(v_unused_4288_);
                            v___x_4252_ = v_x_4238_;
                            v_isShared_4253_ = v_isSharedCheck_4287_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4238_);
                            v___x_4252_ = crate::leanh::lean_box(0);
                            v_isShared_4253_ = v_isSharedCheck_4287_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4289_ = crate::leanh::lean_ctor_get(v_x_4238_, 0);
                    v_vs_4290_ = crate::leanh::lean_ctor_get(v_x_4238_, 1);
                    v_isSharedCheck_4310_ = (!crate::leanh::lean_is_exclusive(v_x_4238_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4292_ = v_x_4238_;
                        v_isShared_4293_ = v_isSharedCheck_4310_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4290_);
                        crate::leanh::lean_inc(v_ks_4289_);
                        crate::leanh::lean_dec(v_x_4238_);
                        v___x_4292_ = crate::leanh::lean_box(0);
                        v_isShared_4293_ = v_isSharedCheck_4310_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4254_ = lean_array_fget(v_es_4243_, v_j_4248_);
                v___x_4255_ = crate::leanh::lean_box(0);
                v_xs_x27_4256_ = lean_array_fset(v_es_4243_, v_j_4248_, v___x_4255_);
                match crate::leanh::lean_obj_tag(v_v_4254_) {
                    0 => {
                        v_key_4263_ = crate::leanh::lean_ctor_get(v_v_4254_, 0);
                        v_val_4264_ = crate::leanh::lean_ctor_get(v_v_4254_, 1);
                        v_isSharedCheck_4274_ = (!crate::leanh::lean_is_exclusive(v_v_4254_)) as u8;
                        if v_isSharedCheck_4274_ == 0 {
                            v___x_4266_ = v_v_4254_;
                            v_isShared_4267_ = v_isSharedCheck_4274_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4264_);
                            crate::leanh::lean_inc(v_key_4263_);
                            crate::leanh::lean_dec(v_v_4254_);
                            v___x_4266_ = crate::leanh::lean_box(0);
                            v_isShared_4267_ = v_isSharedCheck_4274_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4275_ = crate::leanh::lean_ctor_get(v_v_4254_, 0);
                        v_isSharedCheck_4285_ = (!crate::leanh::lean_is_exclusive(v_v_4254_)) as u8;
                        if v_isSharedCheck_4285_ == 0 {
                            v___x_4277_ = v_v_4254_;
                            v_isShared_4278_ = v_isSharedCheck_4285_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4275_);
                            crate::leanh::lean_dec(v_v_4254_);
                            v___x_4277_ = crate::leanh::lean_box(0);
                            v_isShared_4278_ = v_isSharedCheck_4285_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4286_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4286_, 0, v_x_4241_);
                        crate::leanh::lean_ctor_set(v___x_4286_, 1, v_x_4242_);
                        v___y_4258_ = v___x_4286_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4259_ = lean_array_fset(v_xs_x27_4256_, v_j_4248_, v___y_4258_);
                crate::leanh::lean_dec(v_j_4248_);
                if v_isShared_4253_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4252_, 0, v___x_4259_);
                    v___x_4261_ = v___x_4252_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
                    v___x_4261_ = v_reuseFailAlloc_4262_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4261_;
            }
            4 => {
                v___x_4268_ = lean_name_eq(v_x_4241_, v_key_4263_);
                if v___x_4268_ == 0 {
                    crate::leanh::lean_del_object(v___x_4266_);
                    v___x_4269_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4263_,
                        v_val_4264_,
                        v_x_4241_,
                        v_x_4242_,
                    );
                    v___x_4270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4269_);
                    v___y_4258_ = v___x_4270_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4264_);
                    crate::leanh::lean_dec(v_key_4263_);
                    if v_isShared_4267_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4266_, 1, v_x_4242_);
                        crate::leanh::lean_ctor_set(v___x_4266_, 0, v_x_4241_);
                        v___x_4272_ = v___x_4266_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_x_4241_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_x_4242_);
                        v___x_4272_ = v_reuseFailAlloc_4273_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4258_ = v___x_4272_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4279_ = lean_usize_shift_right(v_x_4239_, v___x_4244_);
                v___x_4280_ = lean_usize_add(v_x_4240_, v___x_4245_);
                v___x_4281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_node_4275_, v___x_4279_, v___x_4280_, v_x_4241_, v_x_4242_);
                if v_isShared_4278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4277_, 0, v___x_4281_);
                    v___x_4283_ = v___x_4277_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
                    v___x_4283_ = v_reuseFailAlloc_4284_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4258_ = v___x_4283_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4293_ == 0 {
                    v___x_4295_ = v___x_4292_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_ks_4289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 1, v_vs_4290_);
                    v___x_4295_ = v_reuseFailAlloc_4309_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4296_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_4295_, v_x_4241_, v_x_4242_);
                v___x_4304_ = 7usize;
                v___x_4305_ = lean_usize_dec_le(v___x_4304_, v_x_4240_);
                if v___x_4305_ == 0 {
                    v___x_4306_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4296_);
                    v___x_4307_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4308_ = lean_nat_dec_lt(v___x_4306_, v___x_4307_);
                    crate::leanh::lean_dec(v___x_4306_);
                    v___y_4298_ = v___x_4308_;
                    state = 10;
                    continue;
                } else {
                    v___y_4298_ = v___x_4305_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4298_ == 0 {
                    v_ks_4299_ = crate::leanh::lean_ctor_get(v_newNode_4296_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4299_);
                    v_vs_4300_ = crate::leanh::lean_ctor_get(v_newNode_4296_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4300_);
                    crate::leanh::lean_dec_ref(v_newNode_4296_);
                    v___x_4301_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___closed__0);
                    v___x_4303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4240_, v_ks_4299_, v_vs_4300_, v___x_4301_, v___x_4302_);
                    crate::leanh::lean_dec_ref(v_vs_4300_);
                    crate::leanh::lean_dec_ref(v_ks_4299_);
                    return v___x_4303_;
                } else {
                    return v_newNode_4296_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_4311_: usize,
    mut v_keys_4312_: *mut crate::leanh::LeanObject,
    mut v_vals_4313_: *mut crate::leanh::LeanObject,
    mut v_i_4314_: *mut crate::leanh::LeanObject,
    mut v_entries_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u8 = 0;
    let mut v_k_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: u64 = 0;
    let mut v_h_4322_: usize = 0;
    let mut v___x_4323_: usize = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: usize = 0;
    let mut v___x_4326_: usize = 0;
    let mut v___x_4327_: usize = 0;
    let mut v_h_4328_: usize = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: u64 = 0;
    let mut v_hash_4333_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4316_ = lean_array_get_size(v_keys_4312_);
                v___x_4317_ = lean_nat_dec_lt(v_i_4314_, v___x_4316_);
                if v___x_4317_ == 0 {
                    crate::leanh::lean_dec(v_i_4314_);
                    return v_entries_4315_;
                } else {
                    v_k_4318_ = lean_array_fget_borrowed(v_keys_4312_, v_i_4314_);
                    v_v_4319_ = lean_array_fget_borrowed(v_vals_4313_, v_i_4314_);
                    if crate::leanh::lean_obj_tag(v_k_4318_) == 0 {
                        v___x_4332_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                        v___y_4321_ = v___x_4332_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4333_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_4318_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4321_ = v_hash_4333_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4322_ = lean_uint64_to_usize(v___y_4321_);
                v___x_4323_ = 5usize;
                v___x_4324_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4325_ = 1usize;
                v___x_4326_ = lean_usize_sub(v_depth_4311_, v___x_4325_);
                v___x_4327_ = lean_usize_mul(v___x_4323_, v___x_4326_);
                v_h_4328_ = lean_usize_shift_right(v_h_4322_, v___x_4327_);
                v___x_4329_ = lean_nat_add(v_i_4314_, v___x_4324_);
                crate::leanh::lean_dec(v_i_4314_);
                crate::leanh::lean_inc(v_v_4319_);
                crate::leanh::lean_inc(v_k_4318_);
                v___x_4330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_entries_4315_, v_h_4328_, v_depth_4311_, v_k_4318_, v_v_4319_);
                v_i_4314_ = v___x_4329_;
                v_entries_4315_ = v___x_4330_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_4334_: *mut crate::leanh::LeanObject,
    mut v_keys_4335_: *mut crate::leanh::LeanObject,
    mut v_vals_4336_: *mut crate::leanh::LeanObject,
    mut v_i_4337_: *mut crate::leanh::LeanObject,
    mut v_entries_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4339_: usize = 0;
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4339_ = crate::leanh::lean_unbox_usize(v_depth_4334_);
    crate::leanh::lean_dec(v_depth_4334_);
    v_res_4340_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_4339_, v_keys_4335_, v_vals_4336_, v_i_4337_, v_entries_4338_);
    crate::leanh::lean_dec_ref(v_vals_4336_);
    crate::leanh::lean_dec_ref(v_keys_4335_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4341_: *mut crate::leanh::LeanObject,
    mut v_x_4342_: *mut crate::leanh::LeanObject,
    mut v_x_4343_: *mut crate::leanh::LeanObject,
    mut v_x_4344_: *mut crate::leanh::LeanObject,
    mut v_x_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1056__boxed_4346_: usize = 0;
    let mut v_x_1057__boxed_4347_: usize = 0;
    let mut v_res_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1056__boxed_4346_ = crate::leanh::lean_unbox_usize(v_x_4342_);
    crate::leanh::lean_dec(v_x_4342_);
    v_x_1057__boxed_4347_ = crate::leanh::lean_unbox_usize(v_x_4343_);
    crate::leanh::lean_dec(v_x_4343_);
    v_res_4348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_4341_, v_x_1056__boxed_4346_, v_x_1057__boxed_4347_, v_x_4344_, v_x_4345_);
    return v_res_4348_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(
    mut v_x_4349_: *mut crate::leanh::LeanObject,
    mut v_x_4350_: *mut crate::leanh::LeanObject,
    mut v_x_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4353_: u64 = 0;
    let mut v___x_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u64 = 0;
    let mut v_hash_4358_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4350_) == 0 {
                    v___x_4357_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0_spec__1___redArg___closed__0);
                    v___y_4353_ = v___x_4357_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4358_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4350_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4353_ = v_hash_4358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4354_ = lean_uint64_to_usize(v___y_4353_);
                v___x_4355_ = 1usize;
                v___x_4356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_4349_, v___x_4354_, v___x_4355_, v_x_4350_, v_x_4351_);
                return v___x_4356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(
    mut v_x_4359_: *mut crate::leanh::LeanObject,
    mut v_x_4360_: *mut crate::leanh::LeanObject,
    mut v_x_4361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_4362_: u8 = 0;
    let mut v_map_u2081_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_map_u2081_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4362_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_4359_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4362_ == 0 {
                    v_map_u2081_4363_ = crate::leanh::lean_ctor_get(v_x_4359_, 0);
                    v_map_u2082_4364_ = crate::leanh::lean_ctor_get(v_x_4359_, 1);
                    v_isSharedCheck_4372_ = (!crate::leanh::lean_is_exclusive(v_x_4359_)) as u8;
                    if v_isSharedCheck_4372_ == 0 {
                        v___x_4366_ = v_x_4359_;
                        v_isShared_4367_ = v_isSharedCheck_4372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_4364_);
                        crate::leanh::lean_inc(v_map_u2081_4363_);
                        crate::leanh::lean_dec(v_x_4359_);
                        v___x_4366_ = crate::leanh::lean_box(0);
                        v_isShared_4367_ = v_isSharedCheck_4372_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_4373_ = crate::leanh::lean_ctor_get(v_x_4359_, 0);
                    v_map_u2082_4374_ = crate::leanh::lean_ctor_get(v_x_4359_, 1);
                    v_isSharedCheck_4382_ = (!crate::leanh::lean_is_exclusive(v_x_4359_)) as u8;
                    if v_isSharedCheck_4382_ == 0 {
                        v___x_4376_ = v_x_4359_;
                        v_isShared_4377_ = v_isSharedCheck_4382_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_4374_);
                        crate::leanh::lean_inc(v_map_u2081_4373_);
                        crate::leanh::lean_dec(v_x_4359_);
                        v___x_4376_ = crate::leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4382_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4368_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_map_u2082_4364_, v_x_4360_, v_x_4361_);
                if v_isShared_4367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4366_, 1, v___x_4368_);
                    v___x_4370_ = v___x_4366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_map_u2081_4363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 1, v___x_4368_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4371_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_4362_,
                    );
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4370_;
            }
            3 => {
                v___x_4378_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_map_u2081_4373_, v_x_4360_, v_x_4361_);
                if v_isShared_4377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                    v___x_4380_ = v___x_4376_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 1, v_map_u2082_4374_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_4362_,
                    );
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addSimpCongrTheoremEntry(
    mut v_d_4383_: *mut crate::leanh::LeanObject,
    mut v_e_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_funName_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_funName_4385_ = crate::leanh::lean_ctor_get(v_e_4384_, 1);
    crate::leanh::lean_inc(v_funName_4385_);
    v___x_4386_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_SimpCongrTheorems_get_spec__0___redArg(
        v_d_4383_,
        v_funName_4385_,
    );
    if crate::leanh::lean_obj_tag(v___x_4386_) == 0 {
        let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4387_ = crate::leanh::lean_box(0);
        v___x_4388_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4388_, 0, v_e_4384_);
        crate::leanh::lean_ctor_set(v___x_4388_, 1, v___x_4387_);
        v___x_4389_ =
            l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(
                v_d_4383_,
                v_funName_4385_,
                v___x_4388_,
            );
        return v___x_4389_;
    } else {
        let mut v_val_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4390_ = crate::leanh::lean_ctor_get(v___x_4386_, 0);
        crate::leanh::lean_inc(v_val_4390_);
        crate::leanh::lean_dec_ref_known(v___x_4386_, 1);
        v___x_4391_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_addSimpCongrTheoremEntry_insert(v_e_4384_, v_val_4390_);
        v___x_4392_ =
            l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(
                v_d_4383_,
                v_funName_4385_,
                v___x_4391_,
            );
        return v___x_4392_;
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0(
    mut v_00_u03b2_4393_: *mut crate::leanh::LeanObject,
    mut v_x_4394_: *mut crate::leanh::LeanObject,
    mut v_x_4395_: *mut crate::leanh::LeanObject,
    mut v_x_4396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0___redArg(
        v_x_4394_, v_x_4395_, v_x_4396_,
    );
    return v___x_4397_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0(
    mut v_00_u03b2_4398_: *mut crate::leanh::LeanObject,
    mut v_x_4399_: *mut crate::leanh::LeanObject,
    mut v_x_4400_: *mut crate::leanh::LeanObject,
    mut v_x_4401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4402_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0___redArg(v_x_4399_, v_x_4400_, v_x_4401_);
    return v___x_4402_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1(
    mut v_00_u03b2_4403_: *mut crate::leanh::LeanObject,
    mut v_m_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
    mut v_b_4406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1___redArg(v_m_4404_, v_a_4405_, v_b_4406_);
    return v___x_4407_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4408_: *mut crate::leanh::LeanObject,
    mut v_x_4409_: *mut crate::leanh::LeanObject,
    mut v_x_4410_: usize,
    mut v_x_4411_: usize,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
    mut v_x_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___redArg(v_x_4409_, v_x_4410_, v_x_4411_, v_x_4412_, v_x_4413_);
    return v___x_4414_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4415_: *mut crate::leanh::LeanObject,
    mut v_x_4416_: *mut crate::leanh::LeanObject,
    mut v_x_4417_: *mut crate::leanh::LeanObject,
    mut v_x_4418_: *mut crate::leanh::LeanObject,
    mut v_x_4419_: *mut crate::leanh::LeanObject,
    mut v_x_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1315__boxed_4421_: usize = 0;
    let mut v_x_1316__boxed_4422_: usize = 0;
    let mut v_res_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1315__boxed_4421_ = crate::leanh::lean_unbox_usize(v_x_4417_);
    crate::leanh::lean_dec(v_x_4417_);
    v_x_1316__boxed_4422_ = crate::leanh::lean_unbox_usize(v_x_4418_);
    crate::leanh::lean_dec(v_x_4418_);
    v_res_4423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1(v_00_u03b2_4415_, v_x_4416_, v_x_1315__boxed_4421_, v_x_1316__boxed_4422_, v_x_4419_, v_x_4420_);
    return v_res_4423_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_x_4426_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4427_: u8 = 0;
    v___x_4427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___redArg(v_a_4425_, v_x_4426_);
    return v___x_4427_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_x_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4431_: u8 = 0;
    let mut v_r_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__3(v_00_u03b2_4428_, v_a_4429_, v_x_4430_);
    crate::leanh::lean_dec(v_x_4430_);
    crate::leanh::lean_dec(v_a_4429_);
    v_r_4432_ = crate::leanh::lean_box((v_res_4431_) as usize);
    return v_r_4432_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4433_: *mut crate::leanh::LeanObject,
    mut v_data_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4___redArg(v_data_4434_);
    return v___x_4435_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_b_4438_: *mut crate::leanh::LeanObject,
    mut v_x_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4440_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__5___redArg(v_a_4437_, v_b_4438_, v_x_4439_);
    return v___x_4440_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4441_: *mut crate::leanh::LeanObject,
    mut v_n_4442_: *mut crate::leanh::LeanObject,
    mut v_k_4443_: *mut crate::leanh::LeanObject,
    mut v_v_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4442_, v_k_4443_, v_v_4444_);
    return v___x_4445_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4446_: *mut crate::leanh::LeanObject,
    mut v_depth_4447_: usize,
    mut v_keys_4448_: *mut crate::leanh::LeanObject,
    mut v_vals_4449_: *mut crate::leanh::LeanObject,
    mut v_heq_4450_: *mut crate::leanh::LeanObject,
    mut v_i_4451_: *mut crate::leanh::LeanObject,
    mut v_entries_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_4447_, v_keys_4448_, v_vals_4449_, v_i_4451_, v_entries_4452_);
    return v___x_4453_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4454_: *mut crate::leanh::LeanObject,
    mut v_depth_4455_: *mut crate::leanh::LeanObject,
    mut v_keys_4456_: *mut crate::leanh::LeanObject,
    mut v_vals_4457_: *mut crate::leanh::LeanObject,
    mut v_heq_4458_: *mut crate::leanh::LeanObject,
    mut v_i_4459_: *mut crate::leanh::LeanObject,
    mut v_entries_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4461_: usize = 0;
    let mut v_res_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4461_ = crate::leanh::lean_unbox_usize(v_depth_4455_);
    crate::leanh::lean_dec(v_depth_4455_);
    v_res_4462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4454_, v_depth_boxed_4461_, v_keys_4456_, v_vals_4457_, v_heq_4458_, v_i_4459_, v_entries_4460_);
    crate::leanh::lean_dec_ref(v_vals_4457_);
    crate::leanh::lean_dec_ref(v_keys_4456_);
    return v_res_4462_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_4463_: *mut crate::leanh::LeanObject,
    mut v_i_4464_: *mut crate::leanh::LeanObject,
    mut v_source_4465_: *mut crate::leanh::LeanObject,
    mut v_target_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_4464_, v_source_4465_, v_target_4466_);
    return v___x_4467_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4468_: *mut crate::leanh::LeanObject,
    mut v_x_4469_: *mut crate::leanh::LeanObject,
    mut v_x_4470_: *mut crate::leanh::LeanObject,
    mut v_x_4471_: *mut crate::leanh::LeanObject,
    mut v_x_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4473_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4469_, v_x_4470_, v_x_4471_, v_x_4472_);
    return v___x_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_4474_: *mut crate::leanh::LeanObject,
    mut v_x_4475_: *mut crate::leanh::LeanObject,
    mut v_x_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addSimpCongrTheoremEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_4475_, v_x_4476_);
    return v___x_4477_;
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_4478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_4479_: u8 = 0;
    let mut v_map_u2081_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4479_ = crate::leanh::lean_ctor_get_uint8(
                    v_m_4478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4479_ == 0 {
                    return v_m_4478_;
                } else {
                    v_map_u2081_4480_ = crate::leanh::lean_ctor_get(v_m_4478_, 0);
                    v_map_u2082_4481_ = crate::leanh::lean_ctor_get(v_m_4478_, 1);
                    v_isSharedCheck_4489_ = (!crate::leanh::lean_is_exclusive(v_m_4478_)) as u8;
                    if v_isSharedCheck_4489_ == 0 {
                        v___x_4483_ = v_m_4478_;
                        v_isShared_4484_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_4481_);
                        crate::leanh::lean_inc(v_map_u2081_4480_);
                        crate::leanh::lean_dec(v_m_4478_);
                        v___x_4483_ = crate::leanh::lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4485_ = 0;
                if v_isShared_4484_ == 0 {
                    v___x_4487_ = v___x_4483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_map_u2081_4480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_map_u2082_4481_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4485_,
                );
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_4490_: *mut crate::leanh::LeanObject,
    mut v_m_4491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4492_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__spec__0___redArg(v_m_4491_);
    return v___x_4492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(
    mut v_x_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4495_, 0, v_a_4494_);
    crate::leanh::lean_inc_ref_n(v___x_4495_, 2);
    v___x_4496_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4496_, 0, v___x_4495_);
    crate::leanh::lean_ctor_set(v___x_4496_, 1, v___x_4495_);
    crate::leanh::lean_ctor_set(v___x_4496_, 2, v___x_4495_);
    return v___x_4496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(
    mut v_x_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4499_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_(v_x_4497_, v_a_4498_);
    crate::leanh::lean_dec_ref(v_x_4497_);
    return v_res_4499_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4510_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_;
    v___f_4511_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_;
    v___x_4512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4_once
        ),
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default___closed__4,
    );
    v___x_4513_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_;
    v___x_4514_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_;
    v___x_4515_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4515_, 0, v___x_4514_);
    crate::leanh::lean_ctor_set(v___x_4515_, 1, v___x_4513_);
    crate::leanh::lean_ctor_set(v___x_4515_, 2, v___x_4512_);
    crate::leanh::lean_ctor_set(v___x_4515_, 3, v___f_4511_);
    crate::leanh::lean_ctor_set(v___x_4515_, 4, v___f_4510_);
    return v___x_4515_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_);
    v___x_4518_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_4517_);
    return v___x_4518_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2____boxed(
    mut v_a_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4520_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
    return v_res_4520_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(
    mut v_k_4521_: *mut crate::leanh::LeanObject,
    mut v_t_4522_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4522_) == 0 {
                    v_k_4523_ = crate::leanh::lean_ctor_get(v_t_4522_, 1);
                    v_l_4524_ = crate::leanh::lean_ctor_get(v_t_4522_, 3);
                    v_r_4525_ = crate::leanh::lean_ctor_get(v_t_4522_, 4);
                    v___x_4526_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4521_, v_k_4523_);
                    match v___x_4526_ {
                        0 => {
                            v_t_4522_ = v_l_4524_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_4528_ = 1;
                            return v___x_4528_;
                        }
                        _ => {
                            v_t_4522_ = v_r_4525_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_4530_ = 0;
                    return v___x_4530_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg___boxed(
    mut v_k_4531_: *mut crate::leanh::LeanObject,
    mut v_t_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4533_: u8 = 0;
    let mut v_r_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4533_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_4531_, v_t_4532_);
    crate::leanh::lean_dec(v_t_4532_);
    crate::leanh::lean_dec(v_k_4531_);
    v_r_4534_ = crate::leanh::lean_box((v_res_4533_) as usize);
    return v_r_4534_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(
    mut v_mvarSet_4535_: *mut crate::leanh::LeanObject,
    mut v_e_4536_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4537_: u8 = 0;
    v___x_4537_ = l_Lean_Expr_isMVar(v_e_4536_);
    if v___x_4537_ == 0 {
        return v___x_4537_;
    } else {
        let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4539_: u8 = 0;
        v___x_4538_ = l_Lean_Expr_mvarId_x21(v_e_4536_);
        v___x_4539_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_4538_, v_mvarSet_4535_);
        crate::leanh::lean_dec(v___x_4538_);
        if v___x_4539_ == 0 {
            return v___x_4537_;
        } else {
            let mut v___x_4540_: u8 = 0;
            v___x_4540_ = 0;
            return v___x_4540_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed(
    mut v_mvarSet_4541_: *mut crate::leanh::LeanObject,
    mut v_e_4542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4543_: u8 = 0;
    let mut v_r_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4543_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0(v_mvarSet_4541_, v_e_4542_);
    crate::leanh::lean_dec_ref(v_e_4542_);
    crate::leanh::lean_dec(v_mvarSet_4541_);
    v_r_4544_ = crate::leanh::lean_box((v_res_4543_) as usize);
    return v_r_4544_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(
    mut v_t_4545_: *mut crate::leanh::LeanObject,
    mut v_mvarSet_4546_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4547_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_4547_, 0, v_mvarSet_4546_);
    v___x_4548_ = lean_find_expr(v___f_4547_, v_t_4545_);
    crate::leanh::lean_dec_ref(v___f_4547_);
    if crate::leanh::lean_obj_tag(v___x_4548_) == 0 {
        let mut v___x_4549_: u8 = 0;
        v___x_4549_ = 1;
        return v___x_4549_;
    } else {
        let mut v___x_4550_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_4548_, 1);
        v___x_4550_ = 0;
        return v___x_4550_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt___boxed(
    mut v_t_4551_: *mut crate::leanh::LeanObject,
    mut v_mvarSet_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4553_: u8 = 0;
    let mut v_r_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4553_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_t_4551_, v_mvarSet_4552_);
    crate::leanh::lean_dec_ref(v_t_4551_);
    v_r_4554_ = crate::leanh::lean_box((v_res_4553_) as usize);
    return v_r_4554_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(
    mut v_00_u03b2_4555_: *mut crate::leanh::LeanObject,
    mut v_k_4556_: *mut crate::leanh::LeanObject,
    mut v_t_4557_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4558_: u8 = 0;
    v___x_4558_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v_k_4556_, v_t_4557_);
    return v___x_4558_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___boxed(
    mut v_00_u03b2_4559_: *mut crate::leanh::LeanObject,
    mut v_k_4560_: *mut crate::leanh::LeanObject,
    mut v_t_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4562_: u8 = 0;
    let mut v_r_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4562_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0(v_00_u03b2_4559_, v_k_4560_, v_t_4561_);
    crate::leanh::lean_dec(v_t_4561_);
    crate::leanh::lean_dec(v_k_4560_);
    v_r_4563_ = crate::leanh::lean_box((v_res_4562_) as usize);
    return v_r_4563_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(
    mut v_k_4564_: *mut crate::leanh::LeanObject,
    mut v_b_4565_: *mut crate::leanh::LeanObject,
    mut v_c_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4570_);
    crate::leanh::lean_inc_ref(v___y_4569_);
    crate::leanh::lean_inc(v___y_4568_);
    crate::leanh::lean_inc_ref(v___y_4567_);
    v___x_4572_ = crate::leanh::lean_apply_7(
        v_k_4564_,
        v_b_4565_,
        v_c_4566_,
        v___y_4567_,
        v___y_4568_,
        v___y_4569_,
        v___y_4570_,
        crate::leanh::lean_box(0),
    );
    return v___x_4572_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed(
    mut v_k_4573_: *mut crate::leanh::LeanObject,
    mut v_b_4574_: *mut crate::leanh::LeanObject,
    mut v_c_4575_: *mut crate::leanh::LeanObject,
    mut v___y_4576_: *mut crate::leanh::LeanObject,
    mut v___y_4577_: *mut crate::leanh::LeanObject,
    mut v___y_4578_: *mut crate::leanh::LeanObject,
    mut v___y_4579_: *mut crate::leanh::LeanObject,
    mut v___y_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0(v_k_4573_, v_b_4574_, v_c_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
    crate::leanh::lean_dec(v___y_4579_);
    crate::leanh::lean_dec_ref(v___y_4578_);
    crate::leanh::lean_dec(v___y_4577_);
    crate::leanh::lean_dec_ref(v___y_4576_);
    return v_res_4581_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(
    mut v_type_4582_: *mut crate::leanh::LeanObject,
    mut v_k_4583_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4584_: u8,
    mut v_whnfType_4585_: u8,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
    mut v___y_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_a_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4591_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4591_, 0, v_k_4583_);
                v___x_4592_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_4582_,
                    v___f_4591_,
                    v_cleanupAnnotations_4584_,
                    v_whnfType_4585_,
                    v___y_4586_,
                    v___y_4587_,
                    v___y_4588_,
                    v___y_4589_,
                );
                if crate::leanh::lean_obj_tag(v___x_4592_) == 0 {
                    v_a_4593_ = crate::leanh::lean_ctor_get(v___x_4592_, 0);
                    v_isSharedCheck_4600_ = (!crate::leanh::lean_is_exclusive(v___x_4592_)) as u8;
                    if v_isSharedCheck_4600_ == 0 {
                        v___x_4595_ = v___x_4592_;
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4593_);
                        crate::leanh::lean_dec(v___x_4592_);
                        v___x_4595_ = crate::leanh::lean_box(0);
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4601_ = crate::leanh::lean_ctor_get(v___x_4592_, 0);
                    v_isSharedCheck_4608_ = (!crate::leanh::lean_is_exclusive(v___x_4592_)) as u8;
                    if v_isSharedCheck_4608_ == 0 {
                        v___x_4603_ = v___x_4592_;
                        v_isShared_4604_ = v_isSharedCheck_4608_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4601_);
                        crate::leanh::lean_dec(v___x_4592_);
                        v___x_4603_ = crate::leanh::lean_box(0);
                        v_isShared_4604_ = v_isSharedCheck_4608_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4596_ == 0 {
                    v___x_4598_ = v___x_4595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
                    v___x_4598_ = v_reuseFailAlloc_4599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4598_;
            }
            3 => {
                if v_isShared_4604_ == 0 {
                    v___x_4606_ = v___x_4603_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
                    v___x_4606_ = v_reuseFailAlloc_4607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg___boxed(
    mut v_type_4609_: *mut crate::leanh::LeanObject,
    mut v_k_4610_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4611_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4618_: u8 = 0;
    let mut v_whnfType_boxed_4619_: u8 = 0;
    let mut v_res_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4618_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4611_) as u8);
    v_whnfType_boxed_4619_ = (crate::leanh::lean_unbox(v_whnfType_4612_) as u8);
    v_res_4620_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(
            v_type_4609_,
            v_k_4610_,
            v_cleanupAnnotations_boxed_4618_,
            v_whnfType_boxed_4619_,
            v___y_4613_,
            v___y_4614_,
            v___y_4615_,
            v___y_4616_,
        );
    crate::leanh::lean_dec(v___y_4616_);
    crate::leanh::lean_dec_ref(v___y_4615_);
    crate::leanh::lean_dec(v___y_4614_);
    crate::leanh::lean_dec_ref(v___y_4613_);
    return v_res_4620_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(
    mut v_00_u03b1_4621_: *mut crate::leanh::LeanObject,
    mut v_type_4622_: *mut crate::leanh::LeanObject,
    mut v_k_4623_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4624_: u8,
    mut v_whnfType_4625_: u8,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4631_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(
            v_type_4622_,
            v_k_4623_,
            v_cleanupAnnotations_4624_,
            v_whnfType_4625_,
            v___y_4626_,
            v___y_4627_,
            v___y_4628_,
            v___y_4629_,
        );
    return v___x_4631_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___boxed(
    mut v_00_u03b1_4632_: *mut crate::leanh::LeanObject,
    mut v_type_4633_: *mut crate::leanh::LeanObject,
    mut v_k_4634_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4635_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4642_: u8 = 0;
    let mut v_whnfType_boxed_4643_: u8 = 0;
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4642_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4635_) as u8);
    v_whnfType_boxed_4643_ = (crate::leanh::lean_unbox(v_whnfType_4636_) as u8);
    v_res_4644_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6(
        v_00_u03b1_4632_,
        v_type_4633_,
        v_k_4634_,
        v_cleanupAnnotations_boxed_4642_,
        v_whnfType_boxed_4643_,
        v___y_4637_,
        v___y_4638_,
        v___y_4639_,
        v___y_4640_,
    );
    crate::leanh::lean_dec(v___y_4640_);
    crate::leanh::lean_dec_ref(v___y_4639_);
    crate::leanh::lean_dec(v___y_4638_);
    crate::leanh::lean_dec_ref(v___y_4637_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(
    mut v_msgData_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4651_ = lean_st_ref_get(v___y_4649_);
    v_env_4652_ = crate::leanh::lean_ctor_get(v___x_4651_, 0);
    crate::leanh::lean_inc_ref(v_env_4652_);
    crate::leanh::lean_dec(v___x_4651_);
    v___x_4653_ = lean_st_ref_get(v___y_4647_);
    v_mctx_4654_ = crate::leanh::lean_ctor_get(v___x_4653_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4654_);
    crate::leanh::lean_dec(v___x_4653_);
    v_lctx_4655_ = crate::leanh::lean_ctor_get(v___y_4646_, 2);
    v_options_4656_ = crate::leanh::lean_ctor_get(v___y_4648_, 2);
    crate::leanh::lean_inc_ref(v_options_4656_);
    crate::leanh::lean_inc_ref(v_lctx_4655_);
    v___x_4657_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4657_, 0, v_env_4652_);
    crate::leanh::lean_ctor_set(v___x_4657_, 1, v_mctx_4654_);
    crate::leanh::lean_ctor_set(v___x_4657_, 2, v_lctx_4655_);
    crate::leanh::lean_ctor_set(v___x_4657_, 3, v_options_4656_);
    v___x_4658_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4658_, 0, v___x_4657_);
    crate::leanh::lean_ctor_set(v___x_4658_, 1, v_msgData_4645_);
    v___x_4659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4659_, 0, v___x_4658_);
    return v___x_4659_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5___boxed(
    mut v_msgData_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msgData_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
    crate::leanh::lean_dec(v___y_4664_);
    crate::leanh::lean_dec_ref(v___y_4663_);
    crate::leanh::lean_dec(v___y_4662_);
    crate::leanh::lean_dec_ref(v___y_4661_);
    return v_res_4666_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
    mut v_msg_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v___y_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4673_ = crate::leanh::lean_ctor_get(v___y_4670_, 5);
                v___x_4674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3_spec__5(v_msg_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
                v_a_4675_ = crate::leanh::lean_ctor_get(v___x_4674_, 0);
                v_isSharedCheck_4683_ = (!crate::leanh::lean_is_exclusive(v___x_4674_)) as u8;
                if v_isSharedCheck_4683_ == 0 {
                    v___x_4677_ = v___x_4674_;
                    v_isShared_4678_ = v_isSharedCheck_4683_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4675_);
                    crate::leanh::lean_dec(v___x_4674_);
                    v___x_4677_ = crate::leanh::lean_box(0);
                    v_isShared_4678_ = v_isSharedCheck_4683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4673_);
                v___x_4679_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4679_, 0, v_ref_4673_);
                crate::leanh::lean_ctor_set(v___x_4679_, 1, v_a_4675_);
                if v_isShared_4678_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4677_, 1);
                    crate::leanh::lean_ctor_set(v___x_4677_, 0, v___x_4679_);
                    v___x_4681_ = v___x_4677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
                    v___x_4681_ = v_reuseFailAlloc_4682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg___boxed(
    mut v_msg_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
        v_msg_4684_,
        v___y_4685_,
        v___y_4686_,
        v___y_4687_,
        v___y_4688_,
    );
    crate::leanh::lean_dec(v___y_4688_);
    crate::leanh::lean_dec_ref(v___y_4687_);
    crate::leanh::lean_dec(v___y_4686_);
    crate::leanh::lean_dec_ref(v___y_4685_);
    return v_res_4690_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__0;
    v___x_4693_ = l_Lean_stringToMessageData(v___x_4692_);
    return v___x_4693_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__2;
    v___x_4696_ = l_Lean_stringToMessageData(v___x_4695_);
    return v___x_4696_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(
    mut v___x_4697_: *mut crate::leanh::LeanObject,
    mut v_snd_4698_: *mut crate::leanh::LeanObject,
    mut v_as_4699_: *mut crate::leanh::LeanObject,
    mut v_sz_4700_: usize,
    mut v_i_4701_: usize,
    mut v_b_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: usize = 0;
    let mut v___x_4711_: usize = 0;
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4713_ = lean_usize_dec_lt(v_i_4701_, v_sz_4700_);
                if v___x_4713_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_4698_);
                    v___x_4714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4714_, 0, v_b_4702_);
                    return v___x_4714_;
                } else {
                    v___x_4715_ = crate::leanh::lean_box(0);
                    v_a_4716_ = lean_array_uget_borrowed(v_as_4699_, v_i_4701_);
                    v___x_4717_ = l_Lean_Expr_isFVar(v_a_4716_);
                    if v___x_4717_ == 0 {
                        v___x_4718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
                        v___x_4719_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4720_ = lean_nat_add(v___x_4697_, v___x_4719_);
                        v___x_4721_ = l_Nat_reprFast(v___x_4720_);
                        v___x_4722_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4722_, 0, v___x_4721_);
                        v___x_4723_ = l_Lean_MessageData_ofFormat(v___x_4722_);
                        v___x_4724_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4724_, 0, v___x_4718_);
                        crate::leanh::lean_ctor_set(v___x_4724_, 1, v___x_4723_);
                        v___x_4725_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__3);
                        v___x_4726_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4726_, 0, v___x_4724_);
                        crate::leanh::lean_ctor_set(v___x_4726_, 1, v___x_4725_);
                        crate::leanh::lean_inc_ref(v_snd_4698_);
                        v___x_4727_ = l_Lean_indentExpr(v_snd_4698_);
                        v___x_4728_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4728_, 0, v___x_4726_);
                        crate::leanh::lean_ctor_set(v___x_4728_, 1, v___x_4727_);
                        v___x_4729_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_4728_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
                        if crate::leanh::lean_obj_tag(v___x_4729_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4729_, 1);
                            v_a_4709_ = v___x_4715_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_4698_);
                            return v___x_4729_;
                        }
                    } else {
                        v_a_4709_ = v___x_4715_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4710_ = 1usize;
                v___x_4711_ = lean_usize_add(v_i_4701_, v___x_4710_);
                v_i_4701_ = v___x_4711_;
                v_b_4702_ = v_a_4709_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___boxed(
    mut v___x_4730_: *mut crate::leanh::LeanObject,
    mut v_snd_4731_: *mut crate::leanh::LeanObject,
    mut v_as_4732_: *mut crate::leanh::LeanObject,
    mut v_sz_4733_: *mut crate::leanh::LeanObject,
    mut v_i_4734_: *mut crate::leanh::LeanObject,
    mut v_b_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4741_: usize = 0;
    let mut v_i_boxed_4742_: usize = 0;
    let mut v_res_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4741_ = crate::leanh::lean_unbox_usize(v_sz_4733_);
    crate::leanh::lean_dec(v_sz_4733_);
    v_i_boxed_4742_ = crate::leanh::lean_unbox_usize(v_i_4734_);
    crate::leanh::lean_dec(v_i_4734_);
    v_res_4743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v___x_4730_, v_snd_4731_, v_as_4732_, v_sz_boxed_4741_, v_i_boxed_4742_, v_b_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
    crate::leanh::lean_dec(v___y_4739_);
    crate::leanh::lean_dec_ref(v___y_4738_);
    crate::leanh::lean_dec(v___y_4737_);
    crate::leanh::lean_dec_ref(v___y_4736_);
    crate::leanh::lean_dec_ref(v_as_4732_);
    crate::leanh::lean_dec(v___x_4730_);
    return v_res_4743_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__0;
    v___x_4746_ = l_Lean_stringToMessageData(v___x_4745_);
    return v___x_4746_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__2;
    v___x_4749_ = l_Lean_stringToMessageData(v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__4;
    v___x_4752_ = l_Lean_stringToMessageData(v___x_4751_);
    return v___x_4752_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(
    mut v___x_4753_: *mut crate::leanh::LeanObject,
    mut v___x_4754_: *mut crate::leanh::LeanObject,
    mut v_as_4755_: *mut crate::leanh::LeanObject,
    mut v_sz_4756_: usize,
    mut v_i_4757_: usize,
    mut v_b_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: usize = 0;
    let mut v___x_4768_: usize = 0;
    let mut v___x_4770_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: u8 = 0;
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4802_: u8 = 0;
    let mut v_a_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4770_ = lean_usize_dec_lt(v_i_4757_, v_sz_4756_);
                if v___x_4770_ == 0 {
                    crate::leanh::lean_dec(v___x_4753_);
                    v___x_4771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4771_, 0, v_b_4758_);
                    return v___x_4771_;
                } else {
                    v_a_4772_ = lean_array_uget_borrowed(v_as_4755_, v_i_4757_);
                    crate::leanh::lean_inc(v___y_4762_);
                    crate::leanh::lean_inc_ref(v___y_4761_);
                    crate::leanh::lean_inc(v___y_4760_);
                    crate::leanh::lean_inc_ref(v___y_4759_);
                    crate::leanh::lean_inc(v_a_4772_);
                    v___x_4773_ = lean_infer_type(
                        v_a_4772_,
                        v___y_4759_,
                        v___y_4760_,
                        v___y_4761_,
                        v___y_4762_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4773_) == 0 {
                        v_a_4774_ = crate::leanh::lean_ctor_get(v___x_4773_, 0);
                        crate::leanh::lean_inc(v_a_4774_);
                        crate::leanh::lean_dec_ref_known(v___x_4773_, 1);
                        crate::leanh::lean_inc(v___x_4753_);
                        v___x_4775_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_a_4774_, v___x_4753_);
                        if v___x_4775_ == 0 {
                            v___x_4776_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__1);
                            v___x_4777_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4778_ = lean_nat_add(v_b_4758_, v___x_4777_);
                            v___x_4779_ = l_Nat_reprFast(v___x_4778_);
                            v___x_4780_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4780_, 0, v___x_4779_);
                            v___x_4781_ = l_Lean_MessageData_ofFormat(v___x_4780_);
                            v___x_4782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4782_, 0, v___x_4776_);
                            crate::leanh::lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                            v___x_4783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__3);
                            v___x_4784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4782_);
                            crate::leanh::lean_ctor_set(v___x_4784_, 1, v___x_4783_);
                            v___x_4785_ = lean_nat_add(v___x_4754_, v___x_4777_);
                            v___x_4786_ = l_Nat_reprFast(v___x_4785_);
                            v___x_4787_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                            v___x_4788_ = l_Lean_MessageData_ofFormat(v___x_4787_);
                            v___x_4789_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4789_, 0, v___x_4784_);
                            crate::leanh::lean_ctor_set(v___x_4789_, 1, v___x_4788_);
                            v___x_4790_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___closed__5);
                            v___x_4791_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4791_, 0, v___x_4789_);
                            crate::leanh::lean_ctor_set(v___x_4791_, 1, v___x_4790_);
                            v___x_4792_ = l_Lean_indentExpr(v_a_4774_);
                            v___x_4793_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4793_, 0, v___x_4791_);
                            crate::leanh::lean_ctor_set(v___x_4793_, 1, v___x_4792_);
                            v___x_4794_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_4793_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
                            if crate::leanh::lean_obj_tag(v___x_4794_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4794_, 1);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_b_4758_);
                                crate::leanh::lean_dec(v___x_4753_);
                                v_a_4795_ = crate::leanh::lean_ctor_get(v___x_4794_, 0);
                                v_isSharedCheck_4802_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4794_)) as u8;
                                if v_isSharedCheck_4802_ == 0 {
                                    v___x_4797_ = v___x_4794_;
                                    v_isShared_4798_ = v_isSharedCheck_4802_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4795_);
                                    crate::leanh::lean_dec(v___x_4794_);
                                    v___x_4797_ = crate::leanh::lean_box(0);
                                    v_isShared_4798_ = v_isSharedCheck_4802_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4774_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_4758_);
                        crate::leanh::lean_dec(v___x_4753_);
                        v_a_4803_ = crate::leanh::lean_ctor_get(v___x_4773_, 0);
                        v_isSharedCheck_4810_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4773_)) as u8;
                        if v_isSharedCheck_4810_ == 0 {
                            v___x_4805_ = v___x_4773_;
                            v_isShared_4806_ = v_isSharedCheck_4810_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4803_);
                            crate::leanh::lean_dec(v___x_4773_);
                            v___x_4805_ = crate::leanh::lean_box(0);
                            v_isShared_4806_ = v_isSharedCheck_4810_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4765_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4766_ = lean_nat_add(v_b_4758_, v___x_4765_);
                crate::leanh::lean_dec(v_b_4758_);
                v___x_4767_ = 1usize;
                v___x_4768_ = lean_usize_add(v_i_4757_, v___x_4767_);
                v_i_4757_ = v___x_4768_;
                v_b_4758_ = v___x_4766_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4798_ == 0 {
                    v___x_4800_ = v___x_4797_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
                    v___x_4800_ = v_reuseFailAlloc_4801_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4800_;
            }
            4 => {
                if v_isShared_4806_ == 0 {
                    v___x_4808_ = v___x_4805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
                    v___x_4808_ = v_reuseFailAlloc_4809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5___boxed(
    mut v___x_4811_: *mut crate::leanh::LeanObject,
    mut v___x_4812_: *mut crate::leanh::LeanObject,
    mut v_as_4813_: *mut crate::leanh::LeanObject,
    mut v_sz_4814_: *mut crate::leanh::LeanObject,
    mut v_i_4815_: *mut crate::leanh::LeanObject,
    mut v_b_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4822_: usize = 0;
    let mut v_i_boxed_4823_: usize = 0;
    let mut v_res_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4822_ = crate::leanh::lean_unbox_usize(v_sz_4814_);
    crate::leanh::lean_dec(v_sz_4814_);
    v_i_boxed_4823_ = crate::leanh::lean_unbox_usize(v_i_4815_);
    crate::leanh::lean_dec(v_i_4815_);
    v_res_4824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v___x_4811_, v___x_4812_, v_as_4813_, v_sz_boxed_4822_, v_i_boxed_4823_, v_b_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec_ref(v___y_4817_);
    crate::leanh::lean_dec_ref(v_as_4813_);
    crate::leanh::lean_dec(v___x_4812_);
    return v_res_4824_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4825_ = crate::leanh::lean_box(0);
    v_dummy_4826_ = l_Lean_Expr_sort___override(v___x_4825_);
    return v_dummy_4826_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__1;
    v___x_4829_ = l_Lean_stringToMessageData(v___x_4828_);
    return v___x_4829_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__3;
    v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
    return v___x_4832_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__5;
    v___x_4835_ = l_Lean_stringToMessageData(v___x_4834_);
    return v___x_4835_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(
    mut v_fst_4842_: *mut crate::leanh::LeanObject,
    mut v_fst_4843_: *mut crate::leanh::LeanObject,
    mut v___x_4844_: *mut crate::leanh::LeanObject,
    mut v_ys_4845_: *mut crate::leanh::LeanObject,
    mut v_xType_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4866_: usize = 0;
    let mut v___x_4867_: usize = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4871_: u8 = 0;
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v_unused_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4885_: u8 = 0;
    let mut v___y_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4910_: u8 = 0;
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v___y_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_fst_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4942_: usize = 0;
    let mut v___x_4943_: usize = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: u8 = 0;
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_a_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4969_: u8 = 0;
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4973_: u8 = 0;
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8;
                v___x_4975_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4976_ = l_Lean_Expr_isAppOfArity(v_xType_4846_, v___x_4974_, v___x_4975_);
                if v___x_4976_ == 0 {
                    v___x_4977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10;
                    v___x_4978_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4979_ = l_Lean_Expr_isAppOfArity(v_xType_4846_, v___x_4977_, v___x_4978_);
                    if v___x_4979_ == 0 {
                        crate::leanh::lean_dec(v___x_4844_);
                        crate::leanh::lean_dec(v_fst_4843_);
                        v___x_4980_ = crate::leanh::lean_box(0);
                        v___x_4981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4981_, 0, v___x_4980_);
                        return v___x_4981_;
                    } else {
                        v___x_4982_ = l_Lean_Expr_appFn_x21(v_xType_4846_);
                        v___x_4983_ = l_Lean_Expr_appArg_x21(v___x_4982_);
                        crate::leanh::lean_dec_ref(v___x_4982_);
                        v___x_4984_ = l_Lean_Expr_appArg_x21(v_xType_4846_);
                        v_fst_4940_ = v___x_4983_;
                        v_snd_4941_ = v___x_4984_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_4985_ = l_Lean_Expr_appFn_x21(v_xType_4846_);
                    v___x_4986_ = l_Lean_Expr_appArg_x21(v___x_4985_);
                    crate::leanh::lean_dec_ref(v___x_4985_);
                    v___x_4987_ = l_Lean_Expr_appArg_x21(v_xType_4846_);
                    v_fst_4940_ = v___x_4986_;
                    v_snd_4941_ = v___x_4987_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v_dummy_4859_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
                v_nargs_4860_ = l_Lean_Expr_getAppNumArgs(v___y_4854_);
                crate::leanh::lean_inc(v_nargs_4860_);
                v___x_4861_ = lean_mk_array(v_nargs_4860_, v_dummy_4859_);
                v___x_4862_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4863_ = lean_nat_sub(v_nargs_4860_, v___x_4862_);
                crate::leanh::lean_dec(v_nargs_4860_);
                crate::leanh::lean_inc_ref(v___y_4854_);
                v___x_4864_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v___y_4854_,
                    v___x_4861_,
                    v___x_4863_,
                );
                v___x_4865_ = crate::leanh::lean_box(0);
                v_sz_4866_ = lean_array_size(v___x_4864_);
                v___x_4867_ = 0usize;
                v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4(v_fst_4842_, v___y_4854_, v___x_4864_, v_sz_4866_, v___x_4867_, v___x_4865_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
                crate::leanh::lean_dec_ref(v___x_4864_);
                if crate::leanh::lean_obj_tag(v___x_4868_) == 0 {
                    v_isSharedCheck_4876_ = (!crate::leanh::lean_is_exclusive(v___x_4868_)) as u8;
                    if v_isSharedCheck_4876_ == 0 {
                        v_unused_4877_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                        crate::leanh::lean_dec(v_unused_4877_);
                        v___x_4870_ = v___x_4868_;
                        v_isShared_4871_ = v_isSharedCheck_4876_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4868_);
                        v___x_4870_ = crate::leanh::lean_box(0);
                        v_isShared_4871_ = v_isSharedCheck_4876_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4853_);
                    v_a_4878_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                    v_isSharedCheck_4885_ = (!crate::leanh::lean_is_exclusive(v___x_4868_)) as u8;
                    if v_isSharedCheck_4885_ == 0 {
                        v___x_4880_ = v___x_4868_;
                        v_isShared_4881_ = v_isSharedCheck_4885_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4878_);
                        crate::leanh::lean_dec(v___x_4868_);
                        v___x_4880_ = crate::leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_4885_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4872_, 0, v___y_4853_);
                if v_isShared_4871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4870_, 0, v___x_4872_);
                    v___x_4874_ = v___x_4870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4872_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4874_;
            }
            4 => {
                if v_isShared_4881_ == 0 {
                    v___x_4883_ = v___x_4880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
                    v___x_4883_ = v_reuseFailAlloc_4884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4883_;
            }
            6 => {
                v___x_4893_ = l_Lean_Expr_mvarId_x21(v___y_4887_);
                v___x_4894_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_4893_, v_fst_4843_);
                crate::leanh::lean_dec(v_fst_4843_);
                crate::leanh::lean_dec(v___x_4893_);
                if v___x_4894_ == 0 {
                    v___y_4853_ = v___y_4887_;
                    v___y_4854_ = v___y_4888_;
                    v___y_4855_ = v___y_4889_;
                    v___y_4856_ = v___y_4890_;
                    v___y_4857_ = v___y_4891_;
                    v___y_4858_ = v___y_4892_;
                    state = 1;
                    continue;
                } else {
                    v___x_4895_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
                    v___x_4896_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4897_ = lean_nat_add(v_fst_4842_, v___x_4896_);
                    v___x_4898_ = l_Nat_reprFast(v___x_4897_);
                    v___x_4899_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4899_, 0, v___x_4898_);
                    v___x_4900_ = l_Lean_MessageData_ofFormat(v___x_4899_);
                    v___x_4901_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4895_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 1, v___x_4900_);
                    v___x_4902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__2);
                    v___x_4903_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4901_);
                    crate::leanh::lean_ctor_set(v___x_4903_, 1, v___x_4902_);
                    crate::leanh::lean_inc_ref(v___y_4888_);
                    v___x_4904_ = l_Lean_indentExpr(v___y_4888_);
                    v___x_4905_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4903_);
                    crate::leanh::lean_ctor_set(v___x_4905_, 1, v___x_4904_);
                    v___x_4906_ =
                        l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
                            v___x_4905_,
                            v___y_4889_,
                            v___y_4890_,
                            v___y_4891_,
                            v___y_4892_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4906_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4906_, 1);
                        v___y_4853_ = v___y_4887_;
                        v___y_4854_ = v___y_4888_;
                        v___y_4855_ = v___y_4889_;
                        v___y_4856_ = v___y_4890_;
                        v___y_4857_ = v___y_4891_;
                        v___y_4858_ = v___y_4892_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4888_);
                        crate::leanh::lean_dec_ref(v___y_4887_);
                        v_a_4907_ = crate::leanh::lean_ctor_get(v___x_4906_, 0);
                        v_isSharedCheck_4914_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4906_)) as u8;
                        if v_isSharedCheck_4914_ == 0 {
                            v___x_4909_ = v___x_4906_;
                            v_isShared_4910_ = v_isSharedCheck_4914_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4907_);
                            crate::leanh::lean_dec(v___x_4906_);
                            v___x_4909_ = crate::leanh::lean_box(0);
                            v_isShared_4910_ = v_isSharedCheck_4914_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_4910_ == 0 {
                    v___x_4912_ = v___x_4909_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
                    v___x_4912_ = v_reuseFailAlloc_4913_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4912_;
            }
            9 => {
                v___x_4917_ = l_Lean_Expr_getAppFn(v___y_4916_);
                v___x_4918_ = l_Lean_Expr_isMVar(v___x_4917_);
                if v___x_4918_ == 0 {
                    v___x_4919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
                    v___x_4920_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4921_ = lean_nat_add(v_fst_4842_, v___x_4920_);
                    v___x_4922_ = l_Nat_reprFast(v___x_4921_);
                    v___x_4923_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4922_);
                    v___x_4924_ = l_Lean_MessageData_ofFormat(v___x_4923_);
                    v___x_4925_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4925_, 0, v___x_4919_);
                    crate::leanh::lean_ctor_set(v___x_4925_, 1, v___x_4924_);
                    v___x_4926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__4);
                    v___x_4927_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4927_, 0, v___x_4925_);
                    crate::leanh::lean_ctor_set(v___x_4927_, 1, v___x_4926_);
                    crate::leanh::lean_inc_ref(v___y_4916_);
                    v___x_4928_ = l_Lean_indentExpr(v___y_4916_);
                    v___x_4929_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4929_, 0, v___x_4927_);
                    crate::leanh::lean_ctor_set(v___x_4929_, 1, v___x_4928_);
                    v___x_4930_ =
                        l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
                            v___x_4929_,
                            v___y_4847_,
                            v___y_4848_,
                            v___y_4849_,
                            v___y_4850_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4930_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4930_, 1);
                        v___y_4887_ = v___x_4917_;
                        v___y_4888_ = v___y_4916_;
                        v___y_4889_ = v___y_4847_;
                        v___y_4890_ = v___y_4848_;
                        v___y_4891_ = v___y_4849_;
                        v___y_4892_ = v___y_4850_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4917_);
                        crate::leanh::lean_dec_ref(v___y_4916_);
                        crate::leanh::lean_dec(v_fst_4843_);
                        v_a_4931_ = crate::leanh::lean_ctor_get(v___x_4930_, 0);
                        v_isSharedCheck_4938_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4930_)) as u8;
                        if v_isSharedCheck_4938_ == 0 {
                            v___x_4933_ = v___x_4930_;
                            v_isShared_4934_ = v_isSharedCheck_4938_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4931_);
                            crate::leanh::lean_dec(v___x_4930_);
                            v___x_4933_ = crate::leanh::lean_box(0);
                            v_isShared_4934_ = v_isSharedCheck_4938_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___y_4887_ = v___x_4917_;
                    v___y_4888_ = v___y_4916_;
                    v___y_4889_ = v___y_4847_;
                    v___y_4890_ = v___y_4848_;
                    v___y_4891_ = v___y_4849_;
                    v___y_4892_ = v___y_4850_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_isShared_4934_ == 0 {
                    v___x_4936_ = v___x_4933_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4936_;
            }
            12 => {
                v_sz_4942_ = lean_array_size(v_ys_4845_);
                v___x_4943_ = 0usize;
                crate::leanh::lean_inc(v_fst_4843_);
                v___x_4944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__5(v_fst_4843_, v_fst_4842_, v_ys_4845_, v_sz_4942_, v___x_4943_, v___x_4844_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
                if crate::leanh::lean_obj_tag(v___x_4944_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4944_, 1);
                    crate::leanh::lean_inc(v_fst_4843_);
                    v___x_4945_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt(v_fst_4940_, v_fst_4843_);
                    if v___x_4945_ == 0 {
                        v___x_4946_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__4___closed__1);
                        v___x_4947_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4948_ = lean_nat_add(v_fst_4842_, v___x_4947_);
                        v___x_4949_ = l_Nat_reprFast(v___x_4948_);
                        v___x_4950_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4949_);
                        v___x_4951_ = l_Lean_MessageData_ofFormat(v___x_4950_);
                        v___x_4952_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4952_, 0, v___x_4946_);
                        crate::leanh::lean_ctor_set(v___x_4952_, 1, v___x_4951_);
                        v___x_4953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__6);
                        v___x_4954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4954_, 0, v___x_4952_);
                        crate::leanh::lean_ctor_set(v___x_4954_, 1, v___x_4953_);
                        v___x_4955_ = l_Lean_indentExpr(v_fst_4940_);
                        v___x_4956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4956_, 0, v___x_4954_);
                        crate::leanh::lean_ctor_set(v___x_4956_, 1, v___x_4955_);
                        v___x_4957_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(v___x_4956_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
                        if crate::leanh::lean_obj_tag(v___x_4957_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4957_, 1);
                            v___y_4916_ = v_snd_4941_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_4941_);
                            crate::leanh::lean_dec(v_fst_4843_);
                            v_a_4958_ = crate::leanh::lean_ctor_get(v___x_4957_, 0);
                            v_isSharedCheck_4965_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4957_)) as u8;
                            if v_isSharedCheck_4965_ == 0 {
                                v___x_4960_ = v___x_4957_;
                                v_isShared_4961_ = v_isSharedCheck_4965_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4958_);
                                crate::leanh::lean_dec(v___x_4957_);
                                v___x_4960_ = crate::leanh::lean_box(0);
                                v_isShared_4961_ = v_isSharedCheck_4965_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fst_4940_);
                        v___y_4916_ = v_snd_4941_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_4941_);
                    crate::leanh::lean_dec_ref(v_fst_4940_);
                    crate::leanh::lean_dec(v_fst_4843_);
                    v_a_4966_ = crate::leanh::lean_ctor_get(v___x_4944_, 0);
                    v_isSharedCheck_4973_ = (!crate::leanh::lean_is_exclusive(v___x_4944_)) as u8;
                    if v_isSharedCheck_4973_ == 0 {
                        v___x_4968_ = v___x_4944_;
                        v_isShared_4969_ = v_isSharedCheck_4973_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4966_);
                        crate::leanh::lean_dec(v___x_4944_);
                        v___x_4968_ = crate::leanh::lean_box(0);
                        v_isShared_4969_ = v_isSharedCheck_4973_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_4961_ == 0 {
                    v___x_4963_ = v___x_4960_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4963_;
            }
            15 => {
                if v_isShared_4969_ == 0 {
                    v___x_4971_ = v___x_4968_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
                    v___x_4971_ = v_reuseFailAlloc_4972_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed(
    mut v_fst_4988_: *mut crate::leanh::LeanObject,
    mut v_fst_4989_: *mut crate::leanh::LeanObject,
    mut v___x_4990_: *mut crate::leanh::LeanObject,
    mut v_ys_4991_: *mut crate::leanh::LeanObject,
    mut v_xType_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0(v_fst_4988_, v_fst_4989_, v___x_4990_, v_ys_4991_, v_xType_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    crate::leanh::lean_dec(v___y_4996_);
    crate::leanh::lean_dec_ref(v___y_4995_);
    crate::leanh::lean_dec(v___y_4994_);
    crate::leanh::lean_dec_ref(v___y_4993_);
    crate::leanh::lean_dec_ref(v_xType_4992_);
    crate::leanh::lean_dec_ref(v_ys_4991_);
    crate::leanh::lean_dec(v_fst_4988_);
    return v_res_4998_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(
    mut v_as_4999_: *mut crate::leanh::LeanObject,
    mut v_sz_5000_: usize,
    mut v_i_5001_: usize,
    mut v_b_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5008_: u8 = 0;
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v_fst_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v_fst_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5024_: u8 = 0;
    let mut v_array_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: u8 = 0;
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundMVars_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hypothesesPos_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: usize = 0;
    let mut v___x_5061_: usize = 0;
    let mut v_reuseFailAlloc_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5067_: u8 = 0;
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: u8 = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_a_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut v___x_5095_: u8 = 0;
    let mut v___x_5096_: u8 = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: u8 = 0;
    let mut v_reuseFailAlloc_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5100_: u8 = 0;
    let mut v_unused_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5104_: u8 = 0;
    let mut v_unused_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut v_unused_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v_unused_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5008_ = lean_usize_dec_lt(v_i_5001_, v_sz_5000_);
                if v___x_5008_ == 0 {
                    v___x_5009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5009_, 0, v_b_5002_);
                    return v___x_5009_;
                } else {
                    v_snd_5010_ = crate::leanh::lean_ctor_get(v_b_5002_, 1);
                    crate::leanh::lean_inc(v_snd_5010_);
                    v_snd_5011_ = crate::leanh::lean_ctor_get(v_snd_5010_, 1);
                    crate::leanh::lean_inc(v_snd_5011_);
                    v_snd_5012_ = crate::leanh::lean_ctor_get(v_snd_5011_, 1);
                    crate::leanh::lean_inc(v_snd_5012_);
                    v_fst_5013_ = crate::leanh::lean_ctor_get(v_b_5002_, 0);
                    v_isSharedCheck_5108_ = (!crate::leanh::lean_is_exclusive(v_b_5002_)) as u8;
                    if v_isSharedCheck_5108_ == 0 {
                        v_unused_5109_ = crate::leanh::lean_ctor_get(v_b_5002_, 1);
                        crate::leanh::lean_dec(v_unused_5109_);
                        v___x_5015_ = v_b_5002_;
                        v_isShared_5016_ = v_isSharedCheck_5108_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_5013_);
                        crate::leanh::lean_dec(v_b_5002_);
                        v___x_5015_ = crate::leanh::lean_box(0);
                        v_isShared_5016_ = v_isSharedCheck_5108_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5017_ = crate::leanh::lean_ctor_get(v_snd_5010_, 0);
                v_isSharedCheck_5106_ = (!crate::leanh::lean_is_exclusive(v_snd_5010_)) as u8;
                if v_isSharedCheck_5106_ == 0 {
                    v_unused_5107_ = crate::leanh::lean_ctor_get(v_snd_5010_, 1);
                    crate::leanh::lean_dec(v_unused_5107_);
                    v___x_5019_ = v_snd_5010_;
                    v_isShared_5020_ = v_isSharedCheck_5106_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5017_);
                    crate::leanh::lean_dec(v_snd_5010_);
                    v___x_5019_ = crate::leanh::lean_box(0);
                    v_isShared_5020_ = v_isSharedCheck_5106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_5021_ = crate::leanh::lean_ctor_get(v_snd_5011_, 0);
                v_isSharedCheck_5104_ = (!crate::leanh::lean_is_exclusive(v_snd_5011_)) as u8;
                if v_isSharedCheck_5104_ == 0 {
                    v_unused_5105_ = crate::leanh::lean_ctor_get(v_snd_5011_, 1);
                    crate::leanh::lean_dec(v_unused_5105_);
                    v___x_5023_ = v_snd_5011_;
                    v_isShared_5024_ = v_isSharedCheck_5104_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5021_);
                    crate::leanh::lean_dec(v_snd_5011_);
                    v___x_5023_ = crate::leanh::lean_box(0);
                    v_isShared_5024_ = v_isSharedCheck_5104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_5025_ = crate::leanh::lean_ctor_get(v_snd_5012_, 0);
                v_start_5026_ = crate::leanh::lean_ctor_get(v_snd_5012_, 1);
                v_stop_5027_ = crate::leanh::lean_ctor_get(v_snd_5012_, 2);
                v___x_5028_ = lean_nat_dec_lt(v_start_5026_, v_stop_5027_);
                if v___x_5028_ == 0 {
                    if v_isShared_5024_ == 0 {
                        v___x_5030_ = v___x_5023_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_fst_5021_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 1, v_snd_5012_);
                        v___x_5030_ = v_reuseFailAlloc_5038_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_5027_);
                    crate::leanh::lean_inc(v_start_5026_);
                    crate::leanh::lean_inc_ref(v_array_5025_);
                    v_isSharedCheck_5100_ = (!crate::leanh::lean_is_exclusive(v_snd_5012_)) as u8;
                    if v_isSharedCheck_5100_ == 0 {
                        v_unused_5101_ = crate::leanh::lean_ctor_get(v_snd_5012_, 2);
                        crate::leanh::lean_dec(v_unused_5101_);
                        v_unused_5102_ = crate::leanh::lean_ctor_get(v_snd_5012_, 1);
                        crate::leanh::lean_dec(v_unused_5102_);
                        v_unused_5103_ = crate::leanh::lean_ctor_get(v_snd_5012_, 0);
                        crate::leanh::lean_dec(v_unused_5103_);
                        v___x_5040_ = v_snd_5012_;
                        v_isShared_5041_ = v_isSharedCheck_5100_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_5012_);
                        v___x_5040_ = crate::leanh::lean_box(0);
                        v_isShared_5041_ = v_isSharedCheck_5100_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5019_, 1, v___x_5030_);
                    v___x_5032_ = v___x_5019_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_fst_5017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5030_);
                    v___x_5032_ = v_reuseFailAlloc_5037_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5015_, 1, v___x_5032_);
                    v___x_5034_ = v___x_5015_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5036_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_fst_5013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5032_);
                    v___x_5034_ = v_reuseFailAlloc_5036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5035_, 0, v___x_5034_);
                return v___x_5035_;
            }
            7 => {
                v___x_5042_ = crate::leanh::lean_unsigned_to_nat(0);
                v_a_5043_ = lean_array_uget_borrowed(v_as_4999_, v_i_5001_);
                crate::leanh::lean_inc(v_fst_5013_);
                crate::leanh::lean_inc(v_fst_5017_);
                v___f_5044_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_5044_, 0, v_fst_5017_);
                crate::leanh::lean_closure_set(v___f_5044_, 1, v_fst_5013_);
                crate::leanh::lean_closure_set(v___f_5044_, 2, v___x_5042_);
                v___x_5045_ = lean_array_fget(v_array_5025_, v_start_5026_);
                v___x_5046_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5047_ = lean_nat_add(v_start_5026_, v___x_5046_);
                crate::leanh::lean_dec(v_start_5026_);
                if v_isShared_5041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5040_, 1, v___x_5047_);
                    v___x_5049_ = v___x_5040_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5099_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_array_5025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 2, v_stop_5027_);
                    v___x_5049_ = v_reuseFailAlloc_5099_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5095_ = (crate::leanh::lean_unbox(v___x_5045_) as u8);
                crate::leanh::lean_dec(v___x_5045_);
                v___x_5096_ = l_Lean_BinderInfo_isExplicit(v___x_5095_);
                if v___x_5096_ == 0 {
                    v___y_5067_ = v___x_5096_;
                    state = 13;
                    continue;
                } else {
                    v___x_5097_ = l_Lean_Expr_mvarId_x21(v_a_5043_);
                    v___x_5098_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_mkSimpCongrTheorem_onlyMVarsAt_spec__0___redArg(v___x_5097_, v_fst_5013_);
                    crate::leanh::lean_dec(v___x_5097_);
                    if v___x_5098_ == 0 {
                        v___y_5067_ = v___x_5096_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5044_);
                        v_foundMVars_5051_ = v_fst_5013_;
                        v_hypothesesPos_5052_ = v_fst_5021_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_5053_ = lean_nat_add(v_fst_5017_, v___x_5046_);
                crate::leanh::lean_dec(v_fst_5017_);
                if v_isShared_5024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5023_, 1, v___x_5049_);
                    crate::leanh::lean_ctor_set(v___x_5023_, 0, v_hypothesesPos_5052_);
                    v___x_5055_ = v___x_5023_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_hypothesesPos_5052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 1, v___x_5049_);
                    v___x_5055_ = v_reuseFailAlloc_5065_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5019_, 1, v___x_5055_);
                    crate::leanh::lean_ctor_set(v___x_5019_, 0, v___x_5053_);
                    v___x_5057_ = v___x_5019_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5055_);
                    v___x_5057_ = v_reuseFailAlloc_5064_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5015_, 1, v___x_5057_);
                    crate::leanh::lean_ctor_set(v___x_5015_, 0, v_foundMVars_5051_);
                    v___x_5059_ = v___x_5015_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_foundMVars_5051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 1, v___x_5057_);
                    v___x_5059_ = v_reuseFailAlloc_5063_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5060_ = 1usize;
                v___x_5061_ = lean_usize_add(v_i_5001_, v___x_5060_);
                v_i_5001_ = v___x_5061_;
                v_b_5002_ = v___x_5059_;
                state = 0;
                continue;
            }
            13 => {
                if v___y_5067_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_5044_);
                    v_foundMVars_5051_ = v_fst_5013_;
                    v_hypothesesPos_5052_ = v_fst_5021_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_5006_);
                    crate::leanh::lean_inc_ref(v___y_5005_);
                    crate::leanh::lean_inc(v___y_5004_);
                    crate::leanh::lean_inc_ref(v___y_5003_);
                    crate::leanh::lean_inc(v_a_5043_);
                    v___x_5068_ = lean_infer_type(
                        v_a_5043_,
                        v___y_5003_,
                        v___y_5004_,
                        v___y_5005_,
                        v___y_5006_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5068_) == 0 {
                        v_a_5069_ = crate::leanh::lean_ctor_get(v___x_5068_, 0);
                        crate::leanh::lean_inc(v_a_5069_);
                        crate::leanh::lean_dec_ref_known(v___x_5068_, 1);
                        v___x_5070_ = 0;
                        v___x_5071_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_mkSimpCongrTheorem_spec__6___redArg(v_a_5069_, v___f_5044_, v___x_5070_, v___x_5070_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
                        if crate::leanh::lean_obj_tag(v___x_5071_) == 0 {
                            v_a_5072_ = crate::leanh::lean_ctor_get(v___x_5071_, 0);
                            crate::leanh::lean_inc(v_a_5072_);
                            crate::leanh::lean_dec_ref_known(v___x_5071_, 1);
                            if crate::leanh::lean_obj_tag(v_a_5072_) == 0 {
                                v_foundMVars_5051_ = v_fst_5013_;
                                v_hypothesesPos_5052_ = v_fst_5021_;
                                state = 9;
                                continue;
                            } else {
                                v_val_5073_ = crate::leanh::lean_ctor_get(v_a_5072_, 0);
                                crate::leanh::lean_inc(v_val_5073_);
                                crate::leanh::lean_dec_ref_known(v_a_5072_, 1);
                                v___x_5074_ = l_Lean_Expr_mvarId_x21(v_a_5043_);
                                v___x_5075_ = l_Lean_MVarIdSet_insert(v_fst_5013_, v___x_5074_);
                                v___x_5076_ = l_Lean_Expr_mvarId_x21(v_val_5073_);
                                crate::leanh::lean_dec(v_val_5073_);
                                v___x_5077_ = l_Lean_MVarIdSet_insert(v___x_5075_, v___x_5076_);
                                crate::leanh::lean_inc(v_fst_5017_);
                                v___x_5078_ = lean_array_push(v_fst_5021_, v_fst_5017_);
                                v_foundMVars_5051_ = v___x_5077_;
                                v_hypothesesPos_5052_ = v___x_5078_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5049_);
                            crate::leanh::lean_del_object(v___x_5023_);
                            crate::leanh::lean_dec(v_fst_5021_);
                            crate::leanh::lean_del_object(v___x_5019_);
                            crate::leanh::lean_dec(v_fst_5017_);
                            crate::leanh::lean_del_object(v___x_5015_);
                            crate::leanh::lean_dec(v_fst_5013_);
                            v_a_5079_ = crate::leanh::lean_ctor_get(v___x_5071_, 0);
                            v_isSharedCheck_5086_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5071_)) as u8;
                            if v_isSharedCheck_5086_ == 0 {
                                v___x_5081_ = v___x_5071_;
                                v_isShared_5082_ = v_isSharedCheck_5086_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5079_);
                                crate::leanh::lean_dec(v___x_5071_);
                                v___x_5081_ = crate::leanh::lean_box(0);
                                v_isShared_5082_ = v_isSharedCheck_5086_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5049_);
                        crate::leanh::lean_dec_ref(v___f_5044_);
                        crate::leanh::lean_del_object(v___x_5023_);
                        crate::leanh::lean_dec(v_fst_5021_);
                        crate::leanh::lean_del_object(v___x_5019_);
                        crate::leanh::lean_dec(v_fst_5017_);
                        crate::leanh::lean_del_object(v___x_5015_);
                        crate::leanh::lean_dec(v_fst_5013_);
                        v_a_5087_ = crate::leanh::lean_ctor_get(v___x_5068_, 0);
                        v_isSharedCheck_5094_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5068_)) as u8;
                        if v_isSharedCheck_5094_ == 0 {
                            v___x_5089_ = v___x_5068_;
                            v_isShared_5090_ = v_isSharedCheck_5094_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5087_);
                            crate::leanh::lean_dec(v___x_5068_);
                            v___x_5089_ = crate::leanh::lean_box(0);
                            v_isShared_5090_ = v_isSharedCheck_5094_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_5082_ == 0 {
                    v___x_5084_ = v___x_5081_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
                    v___x_5084_ = v_reuseFailAlloc_5085_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5084_;
            }
            16 => {
                if v_isShared_5090_ == 0 {
                    v___x_5092_ = v___x_5089_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
                    v___x_5092_ = v_reuseFailAlloc_5093_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___boxed(
    mut v_as_5110_: *mut crate::leanh::LeanObject,
    mut v_sz_5111_: *mut crate::leanh::LeanObject,
    mut v_i_5112_: *mut crate::leanh::LeanObject,
    mut v_b_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5119_: usize = 0;
    let mut v_i_boxed_5120_: usize = 0;
    let mut v_res_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5119_ = crate::leanh::lean_unbox_usize(v_sz_5111_);
    crate::leanh::lean_dec(v_sz_5111_);
    v_i_boxed_5120_ = crate::leanh::lean_unbox_usize(v_i_5112_);
    crate::leanh::lean_dec(v_i_5112_);
    v_res_5121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_as_5110_, v_sz_boxed_5119_, v_i_boxed_5120_, v_b_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
    crate::leanh::lean_dec(v___y_5117_);
    crate::leanh::lean_dec_ref(v___y_5116_);
    crate::leanh::lean_dec(v___y_5115_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    crate::leanh::lean_dec_ref(v_as_5110_);
    return v_res_5121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(
    mut v_as_5122_: *mut crate::leanh::LeanObject,
    mut v_sz_5123_: usize,
    mut v_i_5124_: usize,
    mut v_b_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: usize = 0;
    let mut v___x_5132_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5127_ = lean_usize_dec_lt(v_i_5124_, v_sz_5123_);
                if v___x_5127_ == 0 {
                    v___x_5128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5128_, 0, v_b_5125_);
                    return v___x_5128_;
                } else {
                    v_a_5129_ = lean_array_uget_borrowed(v_as_5122_, v_i_5124_);
                    crate::leanh::lean_inc(v_a_5129_);
                    v___x_5130_ = l_Lean_MVarIdSet_insert(v_b_5125_, v_a_5129_);
                    v___x_5131_ = 1usize;
                    v___x_5132_ = lean_usize_add(v_i_5124_, v___x_5131_);
                    v_i_5124_ = v___x_5132_;
                    v_b_5125_ = v___x_5130_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg___boxed(
    mut v_as_5134_: *mut crate::leanh::LeanObject,
    mut v_sz_5135_: *mut crate::leanh::LeanObject,
    mut v_i_5136_: *mut crate::leanh::LeanObject,
    mut v_b_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5139_: usize = 0;
    let mut v_i_boxed_5140_: usize = 0;
    let mut v_res_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5139_ = crate::leanh::lean_unbox_usize(v_sz_5135_);
    crate::leanh::lean_dec(v_sz_5135_);
    v_i_boxed_5140_ = crate::leanh::lean_unbox_usize(v_i_5136_);
    crate::leanh::lean_dec(v_i_5136_);
    v_res_5141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_5134_, v_sz_boxed_5139_, v_i_boxed_5140_, v_b_5137_);
    crate::leanh::lean_dec_ref(v_as_5134_);
    return v_res_5141_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5142_ = crate::leanh::lean_box(0);
    v___x_5143_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5144_ = lean_mk_array(v___x_5143_, v___x_5142_);
    return v___x_5144_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5145_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__0);
    v___x_5146_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5146_);
    crate::leanh::lean_ctor_set(v___x_5147_, 1, v___x_5145_);
    return v___x_5147_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__2;
    v___x_5151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__1);
    v___x_5152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
    crate::leanh::lean_ctor_set(v___x_5152_, 1, v___x_5150_);
    return v___x_5152_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(
    mut v_as_5153_: *mut crate::leanh::LeanObject,
    mut v_sz_5154_: usize,
    mut v_i_5155_: usize,
    mut v_b_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5162_: u8 = 0;
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5168_: usize = 0;
    let mut v___x_5169_: usize = 0;
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: usize = 0;
    let mut v___x_5173_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5162_ = lean_usize_dec_lt(v_i_5155_, v_sz_5154_);
                if v___x_5162_ == 0 {
                    v___x_5163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5163_, 0, v_b_5156_);
                    return v___x_5163_;
                } else {
                    v_a_5164_ = lean_array_uget_borrowed(v_as_5153_, v_i_5155_);
                    v___x_5165_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___closed__3);
                    crate::leanh::lean_inc(v_a_5164_);
                    v___x_5166_ = l_Lean_Expr_collectMVars(v___x_5165_, v_a_5164_);
                    v_result_5167_ = crate::leanh::lean_ctor_get(v___x_5166_, 1);
                    crate::leanh::lean_inc_ref(v_result_5167_);
                    crate::leanh::lean_dec_ref(v___x_5166_);
                    v_sz_5168_ = lean_array_size(v_result_5167_);
                    v___x_5169_ = 0usize;
                    v___x_5170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_result_5167_, v_sz_5168_, v___x_5169_, v_b_5156_);
                    crate::leanh::lean_dec_ref(v_result_5167_);
                    if crate::leanh::lean_obj_tag(v___x_5170_) == 0 {
                        v_a_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                        crate::leanh::lean_inc(v_a_5171_);
                        crate::leanh::lean_dec_ref_known(v___x_5170_, 1);
                        v___x_5172_ = 1usize;
                        v___x_5173_ = lean_usize_add(v_i_5155_, v___x_5172_);
                        v_i_5155_ = v___x_5173_;
                        v_b_5156_ = v_a_5171_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5170_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2___boxed(
    mut v_as_5175_: *mut crate::leanh::LeanObject,
    mut v_sz_5176_: *mut crate::leanh::LeanObject,
    mut v_i_5177_: *mut crate::leanh::LeanObject,
    mut v_b_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5184_: usize = 0;
    let mut v_i_boxed_5185_: usize = 0;
    let mut v_res_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5184_ = crate::leanh::lean_unbox_usize(v_sz_5176_);
    crate::leanh::lean_dec(v_sz_5176_);
    v_i_boxed_5185_ = crate::leanh::lean_unbox_usize(v_i_5177_);
    crate::leanh::lean_dec(v_i_5177_);
    v_res_5186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_as_5175_, v_sz_boxed_5184_, v_i_boxed_5185_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
    crate::leanh::lean_dec(v___y_5182_);
    crate::leanh::lean_dec_ref(v___y_5181_);
    crate::leanh::lean_dec(v___y_5180_);
    crate::leanh::lean_dec_ref(v___y_5179_);
    crate::leanh::lean_dec_ref(v_as_5175_);
    return v_res_5186_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__1;
    v___x_5191_ = l_Lean_stringToMessageData(v___x_5190_);
    return v___x_5191_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(
    mut v_lhsArgs_5192_: *mut crate::leanh::LeanObject,
    mut v_fst_5193_: *mut crate::leanh::LeanObject,
    mut v_fst_5194_: *mut crate::leanh::LeanObject,
    mut v_lhsFn_5195_: *mut crate::leanh::LeanObject,
    mut v_declName_5196_: *mut crate::leanh::LeanObject,
    mut v_prio_5197_: *mut crate::leanh::LeanObject,
    mut v_snd_5198_: *mut crate::leanh::LeanObject,
    mut v_x_5199_: *mut crate::leanh::LeanObject,
    mut v_x_5200_: *mut crate::leanh::LeanObject,
    mut v_x_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5219_: usize = 0;
    let mut v___x_5220_: usize = 0;
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5230_: usize = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5235_: u8 = 0;
    let mut v_snd_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5244_: u8 = 0;
    let mut v_a_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5248_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5252_: u8 = 0;
    let mut v_a_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5256_: u8 = 0;
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5260_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut v___y_5275_: u8 = 0;
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: u8 = 0;
    let mut v___x_5282_: u8 = 0;
    let mut v___x_5283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5199_) == 5 {
                    v_fn_5207_ = crate::leanh::lean_ctor_get(v_x_5199_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5207_);
                    v_arg_5208_ = crate::leanh::lean_ctor_get(v_x_5199_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5208_);
                    crate::leanh::lean_dec_ref_known(v_x_5199_, 2);
                    v___x_5209_ = lean_array_set(v_x_5200_, v_x_5201_, v_arg_5208_);
                    v___x_5210_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5211_ = lean_nat_sub(v_x_5201_, v___x_5210_);
                    crate::leanh::lean_dec(v_x_5201_);
                    v_x_5199_ = v_fn_5207_;
                    v_x_5200_ = v___x_5209_;
                    v_x_5201_ = v___x_5211_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_5201_);
                    v___x_5213_ = crate::leanh::lean_box(1);
                    v___x_5282_ = l_Lean_Expr_isConst(v_lhsFn_5195_);
                    if v___x_5282_ == 0 {
                        v___y_5275_ = v___x_5282_;
                        state = 11;
                        continue;
                    } else {
                        v___x_5283_ = l_Lean_Expr_isConst(v_x_5199_);
                        v___y_5275_ = v___x_5283_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5219_ = lean_array_size(v_lhsArgs_5192_);
                v___x_5220_ = 0usize;
                v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__2(v_lhsArgs_5192_, v_sz_5219_, v___x_5220_, v___x_5213_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
                if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                    v_a_5222_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                    crate::leanh::lean_inc(v_a_5222_);
                    crate::leanh::lean_dec_ref_known(v___x_5221_, 1);
                    v___x_5223_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5224_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__0;
                    v___x_5225_ = lean_array_get_size(v_fst_5193_);
                    v___x_5226_ =
                        l_Array_toSubarray___redArg(v_fst_5193_, v___x_5223_, v___x_5225_);
                    v___x_5227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5227_, 0, v___x_5224_);
                    crate::leanh::lean_ctor_set(v___x_5227_, 1, v___x_5226_);
                    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5228_, 0, v___x_5223_);
                    crate::leanh::lean_ctor_set(v___x_5228_, 1, v___x_5227_);
                    v___x_5229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5229_, 0, v_a_5222_);
                    crate::leanh::lean_ctor_set(v___x_5229_, 1, v___x_5228_);
                    v_sz_5230_ = lean_array_size(v_fst_5194_);
                    v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7(v_fst_5194_, v_sz_5230_, v___x_5220_, v___x_5229_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
                    if crate::leanh::lean_obj_tag(v___x_5231_) == 0 {
                        v_a_5232_ = crate::leanh::lean_ctor_get(v___x_5231_, 0);
                        v_isSharedCheck_5244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5231_)) as u8;
                        if v_isSharedCheck_5244_ == 0 {
                            v___x_5234_ = v___x_5231_;
                            v_isShared_5235_ = v_isSharedCheck_5244_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5232_);
                            crate::leanh::lean_dec(v___x_5231_);
                            v___x_5234_ = crate::leanh::lean_box(0);
                            v_isShared_5235_ = v_isSharedCheck_5244_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_prio_5197_);
                        crate::leanh::lean_dec(v_declName_5196_);
                        v_a_5245_ = crate::leanh::lean_ctor_get(v___x_5231_, 0);
                        v_isSharedCheck_5252_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5231_)) as u8;
                        if v_isSharedCheck_5252_ == 0 {
                            v___x_5247_ = v___x_5231_;
                            v_isShared_5248_ = v_isSharedCheck_5252_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5245_);
                            crate::leanh::lean_dec(v___x_5231_);
                            v___x_5247_ = crate::leanh::lean_box(0);
                            v_isShared_5248_ = v_isSharedCheck_5252_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_5197_);
                    crate::leanh::lean_dec(v_declName_5196_);
                    crate::leanh::lean_dec_ref(v_fst_5193_);
                    v_a_5253_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                    v_isSharedCheck_5260_ = (!crate::leanh::lean_is_exclusive(v___x_5221_)) as u8;
                    if v_isSharedCheck_5260_ == 0 {
                        v___x_5255_ = v___x_5221_;
                        v_isShared_5256_ = v_isSharedCheck_5260_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5253_);
                        crate::leanh::lean_dec(v___x_5221_);
                        v___x_5255_ = crate::leanh::lean_box(0);
                        v_isShared_5256_ = v_isSharedCheck_5260_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5236_ = crate::leanh::lean_ctor_get(v_a_5232_, 1);
                crate::leanh::lean_inc(v_snd_5236_);
                crate::leanh::lean_dec(v_a_5232_);
                v_snd_5237_ = crate::leanh::lean_ctor_get(v_snd_5236_, 1);
                crate::leanh::lean_inc(v_snd_5237_);
                crate::leanh::lean_dec(v_snd_5236_);
                v_fst_5238_ = crate::leanh::lean_ctor_get(v_snd_5237_, 0);
                crate::leanh::lean_inc(v_fst_5238_);
                crate::leanh::lean_dec(v_snd_5237_);
                v___x_5239_ = l_Lean_Expr_constName_x21(v_lhsFn_5195_);
                v___x_5240_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5240_, 0, v_declName_5196_);
                crate::leanh::lean_ctor_set(v___x_5240_, 1, v___x_5239_);
                crate::leanh::lean_ctor_set(v___x_5240_, 2, v_fst_5238_);
                crate::leanh::lean_ctor_set(v___x_5240_, 3, v_prio_5197_);
                if v_isShared_5235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5234_, 0, v___x_5240_);
                    v___x_5242_ = v___x_5234_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5240_);
                    v___x_5242_ = v_reuseFailAlloc_5243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5242_;
            }
            4 => {
                if v_isShared_5248_ == 0 {
                    v___x_5250_ = v___x_5247_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
                    v___x_5250_ = v_reuseFailAlloc_5251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5250_;
            }
            6 => {
                if v_isShared_5256_ == 0 {
                    v___x_5258_ = v___x_5255_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5253_);
                    v___x_5258_ = v_reuseFailAlloc_5259_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5258_;
            }
            8 => {
                v___x_5262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___closed__2);
                v___x_5263_ = l_Lean_indentExpr(v_snd_5198_);
                v___x_5264_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5264_, 0, v___x_5262_);
                crate::leanh::lean_ctor_set(v___x_5264_, 1, v___x_5263_);
                v___x_5265_ =
                    l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
                        v___x_5264_,
                        v___y_5202_,
                        v___y_5203_,
                        v___y_5204_,
                        v___y_5205_,
                    );
                v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5265_, 0);
                v_isSharedCheck_5273_ = (!crate::leanh::lean_is_exclusive(v___x_5265_)) as u8;
                if v_isSharedCheck_5273_ == 0 {
                    v___x_5268_ = v___x_5265_;
                    v_isShared_5269_ = v_isSharedCheck_5273_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5266_);
                    crate::leanh::lean_dec(v___x_5265_);
                    v___x_5268_ = crate::leanh::lean_box(0);
                    v_isShared_5269_ = v_isSharedCheck_5273_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5269_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
                    v___x_5271_ = v_reuseFailAlloc_5272_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5271_;
            }
            11 => {
                if v___y_5275_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_5200_);
                    crate::leanh::lean_dec_ref(v_x_5199_);
                    crate::leanh::lean_dec(v_prio_5197_);
                    crate::leanh::lean_dec(v_declName_5196_);
                    crate::leanh::lean_dec_ref(v_fst_5193_);
                    state = 8;
                    continue;
                } else {
                    v___x_5276_ = l_Lean_Expr_constName_x21(v_lhsFn_5195_);
                    v___x_5277_ = l_Lean_Expr_constName_x21(v_x_5199_);
                    crate::leanh::lean_dec_ref(v_x_5199_);
                    v___x_5278_ = lean_name_eq(v___x_5276_, v___x_5277_);
                    crate::leanh::lean_dec(v___x_5277_);
                    crate::leanh::lean_dec(v___x_5276_);
                    if v___x_5278_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_5200_);
                        crate::leanh::lean_dec(v_prio_5197_);
                        crate::leanh::lean_dec(v_declName_5196_);
                        crate::leanh::lean_dec_ref(v_fst_5193_);
                        state = 8;
                        continue;
                    } else {
                        v___x_5279_ = lean_array_get_size(v_lhsArgs_5192_);
                        v___x_5280_ = lean_array_get_size(v_x_5200_);
                        crate::leanh::lean_dec_ref(v_x_5200_);
                        v___x_5281_ = lean_nat_dec_eq(v___x_5279_, v___x_5280_);
                        if v___x_5281_ == 0 {
                            crate::leanh::lean_dec(v_prio_5197_);
                            crate::leanh::lean_dec(v_declName_5196_);
                            crate::leanh::lean_dec_ref(v_fst_5193_);
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_5198_);
                            v___y_5215_ = v___y_5202_;
                            v___y_5216_ = v___y_5203_;
                            v___y_5217_ = v___y_5204_;
                            v___y_5218_ = v___y_5205_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8___boxed(
    mut v_lhsArgs_5284_: *mut crate::leanh::LeanObject,
    mut v_fst_5285_: *mut crate::leanh::LeanObject,
    mut v_fst_5286_: *mut crate::leanh::LeanObject,
    mut v_lhsFn_5287_: *mut crate::leanh::LeanObject,
    mut v_declName_5288_: *mut crate::leanh::LeanObject,
    mut v_prio_5289_: *mut crate::leanh::LeanObject,
    mut v_snd_5290_: *mut crate::leanh::LeanObject,
    mut v_x_5291_: *mut crate::leanh::LeanObject,
    mut v_x_5292_: *mut crate::leanh::LeanObject,
    mut v_x_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(
        v_lhsArgs_5284_,
        v_fst_5285_,
        v_fst_5286_,
        v_lhsFn_5287_,
        v_declName_5288_,
        v_prio_5289_,
        v_snd_5290_,
        v_x_5291_,
        v_x_5292_,
        v_x_5293_,
        v___y_5294_,
        v___y_5295_,
        v___y_5296_,
        v___y_5297_,
    );
    crate::leanh::lean_dec(v___y_5297_);
    crate::leanh::lean_dec_ref(v___y_5296_);
    crate::leanh::lean_dec(v___y_5295_);
    crate::leanh::lean_dec_ref(v___y_5294_);
    crate::leanh::lean_dec_ref(v_lhsFn_5287_);
    crate::leanh::lean_dec_ref(v_fst_5286_);
    crate::leanh::lean_dec_ref(v_lhsArgs_5284_);
    return v_res_5299_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(
    mut v_snd_5300_: *mut crate::leanh::LeanObject,
    mut v_fst_5301_: *mut crate::leanh::LeanObject,
    mut v_fst_5302_: *mut crate::leanh::LeanObject,
    mut v_declName_5303_: *mut crate::leanh::LeanObject,
    mut v_prio_5304_: *mut crate::leanh::LeanObject,
    mut v_snd_5305_: *mut crate::leanh::LeanObject,
    mut v_x_5306_: *mut crate::leanh::LeanObject,
    mut v_x_5307_: *mut crate::leanh::LeanObject,
    mut v_x_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5306_) == 5 {
                    v_fn_5314_ = crate::leanh::lean_ctor_get(v_x_5306_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5314_);
                    v_arg_5315_ = crate::leanh::lean_ctor_get(v_x_5306_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5315_);
                    crate::leanh::lean_dec_ref_known(v_x_5306_, 2);
                    v___x_5316_ = lean_array_set(v_x_5307_, v_x_5308_, v_arg_5315_);
                    v___x_5317_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5318_ = lean_nat_sub(v_x_5308_, v___x_5317_);
                    crate::leanh::lean_dec(v_x_5308_);
                    v_x_5306_ = v_fn_5314_;
                    v_x_5307_ = v___x_5316_;
                    v_x_5308_ = v___x_5318_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_5308_);
                    v_dummy_5320_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
                    v_nargs_5321_ = l_Lean_Expr_getAppNumArgs(v_snd_5300_);
                    crate::leanh::lean_inc(v_nargs_5321_);
                    v___x_5322_ = lean_mk_array(v_nargs_5321_, v_dummy_5320_);
                    v___x_5323_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5324_ = lean_nat_sub(v_nargs_5321_, v___x_5323_);
                    crate::leanh::lean_dec(v_nargs_5321_);
                    v___x_5325_ =
                        l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(
                            v_x_5307_,
                            v_fst_5301_,
                            v_fst_5302_,
                            v_x_5306_,
                            v_declName_5303_,
                            v_prio_5304_,
                            v_snd_5305_,
                            v_snd_5300_,
                            v___x_5322_,
                            v___x_5324_,
                            v___y_5309_,
                            v___y_5310_,
                            v___y_5311_,
                            v___y_5312_,
                        );
                    crate::leanh::lean_dec_ref(v_x_5306_);
                    crate::leanh::lean_dec_ref(v_x_5307_);
                    return v___x_5325_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12___boxed(
    mut v_snd_5326_: *mut crate::leanh::LeanObject,
    mut v_fst_5327_: *mut crate::leanh::LeanObject,
    mut v_fst_5328_: *mut crate::leanh::LeanObject,
    mut v_declName_5329_: *mut crate::leanh::LeanObject,
    mut v_prio_5330_: *mut crate::leanh::LeanObject,
    mut v_snd_5331_: *mut crate::leanh::LeanObject,
    mut v_x_5332_: *mut crate::leanh::LeanObject,
    mut v_x_5333_: *mut crate::leanh::LeanObject,
    mut v_x_5334_: *mut crate::leanh::LeanObject,
    mut v___y_5335_: *mut crate::leanh::LeanObject,
    mut v___y_5336_: *mut crate::leanh::LeanObject,
    mut v___y_5337_: *mut crate::leanh::LeanObject,
    mut v___y_5338_: *mut crate::leanh::LeanObject,
    mut v___y_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_5326_, v_fst_5327_, v_fst_5328_, v_declName_5329_, v_prio_5330_, v_snd_5331_, v_x_5332_, v_x_5333_, v_x_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
    crate::leanh::lean_dec(v___y_5338_);
    crate::leanh::lean_dec_ref(v___y_5337_);
    crate::leanh::lean_dec(v___y_5336_);
    crate::leanh::lean_dec_ref(v___y_5335_);
    crate::leanh::lean_dec_ref(v_fst_5328_);
    return v_res_5340_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(
    mut v_fst_5341_: *mut crate::leanh::LeanObject,
    mut v_fst_5342_: *mut crate::leanh::LeanObject,
    mut v_declName_5343_: *mut crate::leanh::LeanObject,
    mut v_prio_5344_: *mut crate::leanh::LeanObject,
    mut v_snd_5345_: *mut crate::leanh::LeanObject,
    mut v_snd_5346_: *mut crate::leanh::LeanObject,
    mut v_x_5347_: *mut crate::leanh::LeanObject,
    mut v_x_5348_: *mut crate::leanh::LeanObject,
    mut v_x_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5347_) == 5 {
        let mut v_fn_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fn_5355_ = crate::leanh::lean_ctor_get(v_x_5347_, 0);
        crate::leanh::lean_inc_ref(v_fn_5355_);
        v_arg_5356_ = crate::leanh::lean_ctor_get(v_x_5347_, 1);
        crate::leanh::lean_inc_ref(v_arg_5356_);
        crate::leanh::lean_dec_ref_known(v_x_5347_, 2);
        v___x_5357_ = lean_array_set(v_x_5348_, v_x_5349_, v_arg_5356_);
        v___x_5358_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5359_ = lean_nat_sub(v_x_5349_, v___x_5358_);
        v___x_5360_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9_spec__12(v_snd_5346_, v_fst_5341_, v_fst_5342_, v_declName_5343_, v_prio_5344_, v_snd_5345_, v_fn_5355_, v___x_5357_, v___x_5359_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_);
        return v___x_5360_;
    } else {
        let mut v_dummy_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nargs_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dummy_5361_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
        v_nargs_5362_ = l_Lean_Expr_getAppNumArgs(v_snd_5346_);
        crate::leanh::lean_inc(v_nargs_5362_);
        v___x_5363_ = lean_mk_array(v_nargs_5362_, v_dummy_5361_);
        v___x_5364_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5365_ = lean_nat_sub(v_nargs_5362_, v___x_5364_);
        crate::leanh::lean_dec(v_nargs_5362_);
        v___x_5366_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__8(
            v_x_5348_,
            v_fst_5341_,
            v_fst_5342_,
            v_x_5347_,
            v_declName_5343_,
            v_prio_5344_,
            v_snd_5345_,
            v_snd_5346_,
            v___x_5363_,
            v___x_5365_,
            v___y_5350_,
            v___y_5351_,
            v___y_5352_,
            v___y_5353_,
        );
        crate::leanh::lean_dec_ref(v_x_5347_);
        crate::leanh::lean_dec_ref(v_x_5348_);
        return v___x_5366_;
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9___boxed(
    mut v_fst_5367_: *mut crate::leanh::LeanObject,
    mut v_fst_5368_: *mut crate::leanh::LeanObject,
    mut v_declName_5369_: *mut crate::leanh::LeanObject,
    mut v_prio_5370_: *mut crate::leanh::LeanObject,
    mut v_snd_5371_: *mut crate::leanh::LeanObject,
    mut v_snd_5372_: *mut crate::leanh::LeanObject,
    mut v_x_5373_: *mut crate::leanh::LeanObject,
    mut v_x_5374_: *mut crate::leanh::LeanObject,
    mut v_x_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(
        v_fst_5367_,
        v_fst_5368_,
        v_declName_5369_,
        v_prio_5370_,
        v_snd_5371_,
        v_snd_5372_,
        v_x_5373_,
        v_x_5374_,
        v_x_5375_,
        v___y_5376_,
        v___y_5377_,
        v___y_5378_,
        v___y_5379_,
    );
    crate::leanh::lean_dec(v___y_5379_);
    crate::leanh::lean_dec_ref(v___y_5378_);
    crate::leanh::lean_dec(v___y_5377_);
    crate::leanh::lean_dec_ref(v___y_5376_);
    crate::leanh::lean_dec(v_x_5375_);
    crate::leanh::lean_dec_ref(v_fst_5368_);
    return v_res_5381_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(
    mut v_a_5382_: *mut crate::leanh::LeanObject,
    mut v_a_5383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5389_: u8 = 0;
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5382_) == 0 {
                    v___x_5384_ = l_List_reverse___redArg(v_a_5383_);
                    return v___x_5384_;
                } else {
                    v_head_5385_ = crate::leanh::lean_ctor_get(v_a_5382_, 0);
                    v_tail_5386_ = crate::leanh::lean_ctor_get(v_a_5382_, 1);
                    v_isSharedCheck_5395_ = (!crate::leanh::lean_is_exclusive(v_a_5382_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v___x_5388_ = v_a_5382_;
                        v_isShared_5389_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5386_);
                        crate::leanh::lean_inc(v_head_5385_);
                        crate::leanh::lean_dec(v_a_5382_);
                        v___x_5388_ = crate::leanh::lean_box(0);
                        v_isShared_5389_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5390_ = l_Lean_mkLevelParam(v_head_5385_);
                if v_isShared_5389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5388_, 1, v_a_5383_);
                    crate::leanh::lean_ctor_set(v___x_5388_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5394_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 1, v_a_5383_);
                    v___x_5392_ = v_reuseFailAlloc_5394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5382_ = v_tail_5386_;
                v_a_5383_ = v___x_5392_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5396_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5396_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5397_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__0);
    v___x_5398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5397_);
    return v___x_5398_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
    v___x_5400_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5401_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5401_, 0, v___x_5400_);
    crate::leanh::lean_ctor_set(v___x_5401_, 1, v___x_5400_);
    crate::leanh::lean_ctor_set(v___x_5401_, 2, v___x_5400_);
    crate::leanh::lean_ctor_set(v___x_5401_, 3, v___x_5400_);
    crate::leanh::lean_ctor_set(v___x_5401_, 4, v___x_5399_);
    crate::leanh::lean_ctor_set(v___x_5401_, 5, v___x_5399_);
    crate::leanh::lean_ctor_set(v___x_5401_, 6, v___x_5399_);
    crate::leanh::lean_ctor_set(v___x_5401_, 7, v___x_5399_);
    crate::leanh::lean_ctor_set(v___x_5401_, 8, v___x_5399_);
    crate::leanh::lean_ctor_set(v___x_5401_, 9, v___x_5399_);
    return v___x_5401_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5402_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5403_ = lean_mk_empty_array_with_capacity(v___x_5402_);
    v___x_5404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5404_, 0, v___x_5403_);
    return v___x_5404_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5405_: usize = 0;
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5405_ = 5usize;
    v___x_5406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5407_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5408_ = lean_mk_empty_array_with_capacity(v___x_5407_);
    v___x_5409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
    v___x_5410_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5409_);
    crate::leanh::lean_ctor_set(v___x_5410_, 1, v___x_5408_);
    crate::leanh::lean_ctor_set(v___x_5410_, 2, v___x_5406_);
    crate::leanh::lean_ctor_set(v___x_5410_, 3, v___x_5406_);
    crate::leanh::lean_ctor_set_usize(v___x_5410_, 4, v___x_5405_);
    return v___x_5410_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5411_ = crate::leanh::lean_box(1);
    v___x_5412_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__4);
    v___x_5413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__1);
    v___x_5414_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5413_);
    crate::leanh::lean_ctor_set(v___x_5414_, 1, v___x_5412_);
    crate::leanh::lean_ctor_set(v___x_5414_, 2, v___x_5411_);
    return v___x_5414_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__6;
    v___x_5417_ = l_Lean_stringToMessageData(v___x_5416_);
    return v___x_5417_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__8;
    v___x_5420_ = l_Lean_stringToMessageData(v___x_5419_);
    return v___x_5420_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5422_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__10;
    v___x_5423_ = l_Lean_stringToMessageData(v___x_5422_);
    return v___x_5423_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__12;
    v___x_5426_ = l_Lean_stringToMessageData(v___x_5425_);
    return v___x_5426_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5428_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__14;
    v___x_5429_ = l_Lean_stringToMessageData(v___x_5428_);
    return v___x_5429_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5431_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__16;
    v___x_5432_ = l_Lean_stringToMessageData(v___x_5431_);
    return v___x_5432_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5434_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__18;
    v___x_5435_ = l_Lean_stringToMessageData(v___x_5434_);
    return v___x_5435_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(
    mut v_msg_5436_: *mut crate::leanh::LeanObject,
    mut v_declHint_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: u8 = 0;
    let mut v_isExporting_5443_: u8 = 0;
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5497_: u8 = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5440_ = lean_st_ref_get(v___y_5438_);
                v_env_5441_ = crate::leanh::lean_ctor_get(v___x_5440_, 0);
                crate::leanh::lean_inc_ref(v_env_5441_);
                crate::leanh::lean_dec(v___x_5440_);
                v___x_5442_ = l_Lean_Name_isAnonymous(v_declHint_5437_);
                if v___x_5442_ == 0 {
                    v_isExporting_5443_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5441_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5443_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5441_);
                        crate::leanh::lean_dec(v_declHint_5437_);
                        v___x_5444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5444_, 0, v_msg_5436_);
                        return v___x_5444_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5441_);
                        v___x_5445_ = l_Lean_Environment_setExporting(v_env_5441_, v___x_5442_);
                        crate::leanh::lean_inc(v_declHint_5437_);
                        crate::leanh::lean_inc_ref(v___x_5445_);
                        v___x_5446_ = l_Lean_Environment_contains(
                            v___x_5445_,
                            v_declHint_5437_,
                            v_isExporting_5443_,
                        );
                        if v___x_5446_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5445_);
                            crate::leanh::lean_dec_ref(v_env_5441_);
                            crate::leanh::lean_dec(v_declHint_5437_);
                            v___x_5447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5447_, 0, v_msg_5436_);
                            return v___x_5447_;
                        } else {
                            v___x_5448_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
                            v___x_5449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
                            v___x_5450_ = l_Lean_Options_empty;
                            v___x_5451_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5451_, 0, v___x_5445_);
                            crate::leanh::lean_ctor_set(v___x_5451_, 1, v___x_5448_);
                            crate::leanh::lean_ctor_set(v___x_5451_, 2, v___x_5449_);
                            crate::leanh::lean_ctor_set(v___x_5451_, 3, v___x_5450_);
                            crate::leanh::lean_inc(v_declHint_5437_);
                            v___x_5452_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5437_, v___x_5442_);
                            v_c_5453_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5453_, 0, v___x_5451_);
                            crate::leanh::lean_ctor_set(v_c_5453_, 1, v___x_5452_);
                            v___x_5454_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5441_,
                                v_declHint_5437_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5454_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5441_);
                                crate::leanh::lean_dec(v_declHint_5437_);
                                v___x_5455_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
                                v___x_5456_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5456_, 0, v___x_5455_);
                                crate::leanh::lean_ctor_set(v___x_5456_, 1, v_c_5453_);
                                v___x_5457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__9);
                                v___x_5458_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5458_, 0, v___x_5456_);
                                crate::leanh::lean_ctor_set(v___x_5458_, 1, v___x_5457_);
                                v___x_5459_ = l_Lean_MessageData_note(v___x_5458_);
                                v___x_5460_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5460_, 0, v_msg_5436_);
                                crate::leanh::lean_ctor_set(v___x_5460_, 1, v___x_5459_);
                                v___x_5461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5461_, 0, v___x_5460_);
                                return v___x_5461_;
                            } else {
                                v_val_5462_ = crate::leanh::lean_ctor_get(v___x_5454_, 0);
                                v_isSharedCheck_5497_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5454_)) as u8;
                                if v_isSharedCheck_5497_ == 0 {
                                    v___x_5464_ = v___x_5454_;
                                    v_isShared_5465_ = v_isSharedCheck_5497_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5462_);
                                    crate::leanh::lean_dec(v___x_5454_);
                                    v___x_5464_ = crate::leanh::lean_box(0);
                                    v_isShared_5465_ = v_isSharedCheck_5497_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5441_);
                    crate::leanh::lean_dec(v_declHint_5437_);
                    v___x_5498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5498_, 0, v_msg_5436_);
                    return v___x_5498_;
                }
            }
            1 => {
                v___x_5466_ = crate::leanh::lean_box(0);
                v___x_5467_ = l_Lean_Environment_header(v_env_5441_);
                crate::leanh::lean_dec_ref(v_env_5441_);
                v___x_5468_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5467_);
                v_mod_5469_ = lean_array_get(v___x_5466_, v___x_5468_, v_val_5462_);
                crate::leanh::lean_dec(v_val_5462_);
                crate::leanh::lean_dec_ref(v___x_5468_);
                v___x_5470_ = l_Lean_isPrivateName(v_declHint_5437_);
                crate::leanh::lean_dec(v_declHint_5437_);
                if v___x_5470_ == 0 {
                    v___x_5471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__11);
                    v___x_5472_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5472_, 0, v___x_5471_);
                    crate::leanh::lean_ctor_set(v___x_5472_, 1, v_c_5453_);
                    v___x_5473_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__13);
                    v___x_5474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5474_, 0, v___x_5472_);
                    crate::leanh::lean_ctor_set(v___x_5474_, 1, v___x_5473_);
                    v___x_5475_ = l_Lean_MessageData_ofName(v_mod_5469_);
                    v___x_5476_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5476_, 0, v___x_5474_);
                    crate::leanh::lean_ctor_set(v___x_5476_, 1, v___x_5475_);
                    v___x_5477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__15);
                    v___x_5478_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5478_, 0, v___x_5476_);
                    crate::leanh::lean_ctor_set(v___x_5478_, 1, v___x_5477_);
                    v___x_5479_ = l_Lean_MessageData_note(v___x_5478_);
                    v___x_5480_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5480_, 0, v_msg_5436_);
                    crate::leanh::lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                    if v_isShared_5465_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5464_, 0);
                        crate::leanh::lean_ctor_set(v___x_5464_, 0, v___x_5480_);
                        v___x_5482_ = v___x_5464_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
                        v___x_5482_ = v_reuseFailAlloc_5483_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5484_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__7);
                    v___x_5485_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5484_);
                    crate::leanh::lean_ctor_set(v___x_5485_, 1, v_c_5453_);
                    v___x_5486_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__17);
                    v___x_5487_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5487_, 0, v___x_5485_);
                    crate::leanh::lean_ctor_set(v___x_5487_, 1, v___x_5486_);
                    v___x_5488_ = l_Lean_MessageData_ofName(v_mod_5469_);
                    v___x_5489_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5489_, 0, v___x_5487_);
                    crate::leanh::lean_ctor_set(v___x_5489_, 1, v___x_5488_);
                    v___x_5490_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__19);
                    v___x_5491_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5491_, 0, v___x_5489_);
                    crate::leanh::lean_ctor_set(v___x_5491_, 1, v___x_5490_);
                    v___x_5492_ = l_Lean_MessageData_note(v___x_5491_);
                    v___x_5493_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5493_, 0, v_msg_5436_);
                    crate::leanh::lean_ctor_set(v___x_5493_, 1, v___x_5492_);
                    if v_isShared_5465_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5464_, 0);
                        crate::leanh::lean_ctor_set(v___x_5464_, 0, v___x_5493_);
                        v___x_5495_ = v___x_5464_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
                        v___x_5495_ = v_reuseFailAlloc_5496_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5482_;
            }
            3 => {
                return v___x_5495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___boxed(
    mut v_msg_5499_: *mut crate::leanh::LeanObject,
    mut v_declHint_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5503_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_5499_, v_declHint_5500_, v___y_5501_);
    crate::leanh::lean_dec(v___y_5501_);
    return v_res_5503_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(
    mut v_msg_5504_: *mut crate::leanh::LeanObject,
    mut v_declHint_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5511_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_5504_, v_declHint_5505_, v___y_5509_);
                v_a_5512_ = crate::leanh::lean_ctor_get(v___x_5511_, 0);
                v_isSharedCheck_5521_ = (!crate::leanh::lean_is_exclusive(v___x_5511_)) as u8;
                if v_isSharedCheck_5521_ == 0 {
                    v___x_5514_ = v___x_5511_;
                    v_isShared_5515_ = v_isSharedCheck_5521_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5512_);
                    crate::leanh::lean_dec(v___x_5511_);
                    v___x_5514_ = crate::leanh::lean_box(0);
                    v_isShared_5515_ = v_isSharedCheck_5521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5516_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5517_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5517_, 0, v___x_5516_);
                crate::leanh::lean_ctor_set(v___x_5517_, 1, v_a_5512_);
                if v_isShared_5515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5514_, 0, v___x_5517_);
                    v___x_5519_ = v___x_5514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5517_);
                    v___x_5519_ = v_reuseFailAlloc_5520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16___boxed(
    mut v_msg_5522_: *mut crate::leanh::LeanObject,
    mut v_declHint_5523_: *mut crate::leanh::LeanObject,
    mut v___y_5524_: *mut crate::leanh::LeanObject,
    mut v___y_5525_: *mut crate::leanh::LeanObject,
    mut v___y_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5529_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_5522_, v_declHint_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_);
    crate::leanh::lean_dec(v___y_5527_);
    crate::leanh::lean_dec_ref(v___y_5526_);
    crate::leanh::lean_dec(v___y_5525_);
    crate::leanh::lean_dec_ref(v___y_5524_);
    return v_res_5529_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(
    mut v_ref_5530_: *mut crate::leanh::LeanObject,
    mut v_msg_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5549_: u8 = 0;
    let mut v_cancelTk_x3f_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5551_: u8 = 0;
    let mut v_inheritedTraceOptions_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5537_ = crate::leanh::lean_ctor_get(v___y_5534_, 0);
    v_fileMap_5538_ = crate::leanh::lean_ctor_get(v___y_5534_, 1);
    v_options_5539_ = crate::leanh::lean_ctor_get(v___y_5534_, 2);
    v_currRecDepth_5540_ = crate::leanh::lean_ctor_get(v___y_5534_, 3);
    v_maxRecDepth_5541_ = crate::leanh::lean_ctor_get(v___y_5534_, 4);
    v_ref_5542_ = crate::leanh::lean_ctor_get(v___y_5534_, 5);
    v_currNamespace_5543_ = crate::leanh::lean_ctor_get(v___y_5534_, 6);
    v_openDecls_5544_ = crate::leanh::lean_ctor_get(v___y_5534_, 7);
    v_initHeartbeats_5545_ = crate::leanh::lean_ctor_get(v___y_5534_, 8);
    v_maxHeartbeats_5546_ = crate::leanh::lean_ctor_get(v___y_5534_, 9);
    v_quotContext_5547_ = crate::leanh::lean_ctor_get(v___y_5534_, 10);
    v_currMacroScope_5548_ = crate::leanh::lean_ctor_get(v___y_5534_, 11);
    v_diag_5549_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5534_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5550_ = crate::leanh::lean_ctor_get(v___y_5534_, 12);
    v_suppressElabErrors_5551_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5534_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5552_ = crate::leanh::lean_ctor_get(v___y_5534_, 13);
    v_ref_5553_ = l_Lean_replaceRef(v_ref_5530_, v_ref_5542_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5552_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5550_);
    crate::leanh::lean_inc(v_currMacroScope_5548_);
    crate::leanh::lean_inc(v_quotContext_5547_);
    crate::leanh::lean_inc(v_maxHeartbeats_5546_);
    crate::leanh::lean_inc(v_initHeartbeats_5545_);
    crate::leanh::lean_inc(v_openDecls_5544_);
    crate::leanh::lean_inc(v_currNamespace_5543_);
    crate::leanh::lean_inc(v_maxRecDepth_5541_);
    crate::leanh::lean_inc(v_currRecDepth_5540_);
    crate::leanh::lean_inc_ref(v_options_5539_);
    crate::leanh::lean_inc_ref(v_fileMap_5538_);
    crate::leanh::lean_inc_ref(v_fileName_5537_);
    v___x_5554_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5554_, 0, v_fileName_5537_);
    crate::leanh::lean_ctor_set(v___x_5554_, 1, v_fileMap_5538_);
    crate::leanh::lean_ctor_set(v___x_5554_, 2, v_options_5539_);
    crate::leanh::lean_ctor_set(v___x_5554_, 3, v_currRecDepth_5540_);
    crate::leanh::lean_ctor_set(v___x_5554_, 4, v_maxRecDepth_5541_);
    crate::leanh::lean_ctor_set(v___x_5554_, 5, v_ref_5553_);
    crate::leanh::lean_ctor_set(v___x_5554_, 6, v_currNamespace_5543_);
    crate::leanh::lean_ctor_set(v___x_5554_, 7, v_openDecls_5544_);
    crate::leanh::lean_ctor_set(v___x_5554_, 8, v_initHeartbeats_5545_);
    crate::leanh::lean_ctor_set(v___x_5554_, 9, v_maxHeartbeats_5546_);
    crate::leanh::lean_ctor_set(v___x_5554_, 10, v_quotContext_5547_);
    crate::leanh::lean_ctor_set(v___x_5554_, 11, v_currMacroScope_5548_);
    crate::leanh::lean_ctor_set(v___x_5554_, 12, v_cancelTk_x3f_5550_);
    crate::leanh::lean_ctor_set(v___x_5554_, 13, v_inheritedTraceOptions_5552_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5554_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5549_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5554_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5551_,
    );
    v___x_5555_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
        v_msg_5531_,
        v___y_5532_,
        v___y_5533_,
        v___x_5554_,
        v___y_5535_,
    );
    crate::leanh::lean_dec_ref_known(v___x_5554_, 14);
    return v___x_5555_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg___boxed(
    mut v_ref_5556_: *mut crate::leanh::LeanObject,
    mut v_msg_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5563_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_5556_, v_msg_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_);
    crate::leanh::lean_dec(v___y_5561_);
    crate::leanh::lean_dec_ref(v___y_5560_);
    crate::leanh::lean_dec(v___y_5559_);
    crate::leanh::lean_dec_ref(v___y_5558_);
    crate::leanh::lean_dec(v_ref_5556_);
    return v_res_5563_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(
    mut v_ref_5564_: *mut crate::leanh::LeanObject,
    mut v_msg_5565_: *mut crate::leanh::LeanObject,
    mut v_declHint_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5572_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16(v_msg_5565_, v_declHint_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
    v_a_5573_ = crate::leanh::lean_ctor_get(v___x_5572_, 0);
    crate::leanh::lean_inc(v_a_5573_);
    crate::leanh::lean_dec_ref(v___x_5572_);
    v___x_5574_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_5564_, v_a_5573_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
    return v___x_5574_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg___boxed(
    mut v_ref_5575_: *mut crate::leanh::LeanObject,
    mut v_msg_5576_: *mut crate::leanh::LeanObject,
    mut v_declHint_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_5575_, v_msg_5576_, v_declHint_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
    crate::leanh::lean_dec(v___y_5581_);
    crate::leanh::lean_dec_ref(v___y_5580_);
    crate::leanh::lean_dec(v___y_5579_);
    crate::leanh::lean_dec_ref(v___y_5578_);
    crate::leanh::lean_dec(v_ref_5575_);
    return v_res_5583_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5585_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__0;
    v___x_5586_ = l_Lean_stringToMessageData(v___x_5585_);
    return v___x_5586_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__2;
    v___x_5589_ = l_Lean_stringToMessageData(v___x_5588_);
    return v___x_5589_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(
    mut v_ref_5590_: *mut crate::leanh::LeanObject,
    mut v_constName_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__1);
    v___x_5598_ = 0;
    crate::leanh::lean_inc(v_constName_5591_);
    v___x_5599_ = l_Lean_MessageData_ofConstName(v_constName_5591_, v___x_5598_);
    v___x_5600_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5600_, 0, v___x_5597_);
    crate::leanh::lean_ctor_set(v___x_5600_, 1, v___x_5599_);
    v___x_5601_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___closed__3);
    v___x_5602_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5602_, 0, v___x_5600_);
    crate::leanh::lean_ctor_set(v___x_5602_, 1, v___x_5601_);
    v___x_5603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_5590_, v___x_5602_, v_constName_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    return v___x_5603_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg___boxed(
    mut v_ref_5604_: *mut crate::leanh::LeanObject,
    mut v_constName_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5611_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_5604_, v_constName_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
    crate::leanh::lean_dec(v___y_5609_);
    crate::leanh::lean_dec_ref(v___y_5608_);
    crate::leanh::lean_dec(v___y_5607_);
    crate::leanh::lean_dec_ref(v___y_5606_);
    crate::leanh::lean_dec(v_ref_5604_);
    return v_res_5611_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(
    mut v_constName_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5618_ = crate::leanh::lean_ctor_get(v___y_5615_, 5);
    v___x_5619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_5618_, v_constName_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
    return v___x_5619_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_constName_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5626_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
    crate::leanh::lean_dec(v___y_5624_);
    crate::leanh::lean_dec_ref(v___y_5623_);
    crate::leanh::lean_dec(v___y_5622_);
    crate::leanh::lean_dec_ref(v___y_5621_);
    return v_res_5626_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(
    mut v_constName_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5641_: u8 = 0;
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5633_ = lean_st_ref_get(v___y_5631_);
                v_env_5634_ = crate::leanh::lean_ctor_get(v___x_5633_, 0);
                crate::leanh::lean_inc_ref(v_env_5634_);
                crate::leanh::lean_dec(v___x_5633_);
                v___x_5635_ = 0;
                crate::leanh::lean_inc(v_constName_5627_);
                v___x_5636_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_5634_,
                    v_constName_5627_,
                    v___x_5635_,
                );
                if crate::leanh::lean_obj_tag(v___x_5636_) == 0 {
                    v___x_5637_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
                    return v___x_5637_;
                } else {
                    crate::leanh::lean_dec(v_constName_5627_);
                    v_val_5638_ = crate::leanh::lean_ctor_get(v___x_5636_, 0);
                    v_isSharedCheck_5645_ = (!crate::leanh::lean_is_exclusive(v___x_5636_)) as u8;
                    if v_isSharedCheck_5645_ == 0 {
                        v___x_5640_ = v___x_5636_;
                        v_isShared_5641_ = v_isSharedCheck_5645_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5638_);
                        crate::leanh::lean_dec(v___x_5636_);
                        v___x_5640_ = crate::leanh::lean_box(0);
                        v_isShared_5641_ = v_isSharedCheck_5645_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5641_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5640_, 0);
                    v___x_5643_ = v___x_5640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_val_5638_);
                    v___x_5643_ = v_reuseFailAlloc_5644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1___boxed(
    mut v_constName_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5652_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_);
    crate::leanh::lean_dec(v___y_5650_);
    crate::leanh::lean_dec_ref(v___y_5649_);
    crate::leanh::lean_dec(v___y_5648_);
    crate::leanh::lean_dec_ref(v___y_5647_);
    return v_res_5652_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(
    mut v_constName_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v_levelParams_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut v_a_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_5653_);
                v___x_5659_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(v_constName_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
                if crate::leanh::lean_obj_tag(v___x_5659_) == 0 {
                    v_a_5660_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                    v_isSharedCheck_5671_ = (!crate::leanh::lean_is_exclusive(v___x_5659_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5662_ = v___x_5659_;
                        v_isShared_5663_ = v_isSharedCheck_5671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5660_);
                        crate::leanh::lean_dec(v___x_5659_);
                        v___x_5662_ = crate::leanh::lean_box(0);
                        v_isShared_5663_ = v_isSharedCheck_5671_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_5653_);
                    v_a_5672_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                    v_isSharedCheck_5679_ = (!crate::leanh::lean_is_exclusive(v___x_5659_)) as u8;
                    if v_isSharedCheck_5679_ == 0 {
                        v___x_5674_ = v___x_5659_;
                        v_isShared_5675_ = v_isSharedCheck_5679_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5672_);
                        crate::leanh::lean_dec(v___x_5659_);
                        v___x_5674_ = crate::leanh::lean_box(0);
                        v_isShared_5675_ = v_isSharedCheck_5679_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_5664_ = crate::leanh::lean_ctor_get(v_a_5660_, 1);
                crate::leanh::lean_inc(v_levelParams_5664_);
                crate::leanh::lean_dec(v_a_5660_);
                v___x_5665_ = crate::leanh::lean_box(0);
                v___x_5666_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(v_levelParams_5664_, v___x_5665_);
                v___x_5667_ = l_Lean_mkConst(v_constName_5653_, v___x_5666_);
                if v_isShared_5663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5662_, 0, v___x_5667_);
                    v___x_5669_ = v___x_5662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
                    v___x_5669_ = v_reuseFailAlloc_5670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5669_;
            }
            3 => {
                if v_isShared_5675_ == 0 {
                    v___x_5677_ = v___x_5674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
                    v___x_5677_ = v_reuseFailAlloc_5678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1___boxed(
    mut v_constName_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5686_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(
        v_constName_5680_,
        v___y_5681_,
        v___y_5682_,
        v___y_5683_,
        v___y_5684_,
    );
    crate::leanh::lean_dec(v___y_5684_);
    crate::leanh::lean_dec_ref(v___y_5683_);
    crate::leanh::lean_dec(v___y_5682_);
    crate::leanh::lean_dec_ref(v___y_5681_);
    return v_res_5686_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0() -> u64 {
    let mut v___x_5687_: u8 = 0;
    let mut v___x_5688_: u64 = 0;
    v___x_5687_ = 2;
    v___x_5688_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_5687_);
    return v___x_5688_;
}
pub unsafe fn _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5690_ = l_Lean_Meta_mkSimpCongrTheorem___closed__1;
    v___x_5691_ = l_Lean_stringToMessageData(v___x_5690_);
    return v___x_5691_;
}
pub unsafe fn l_Lean_Meta_mkSimpCongrTheorem(
    mut v_declName_5692_: *mut crate::leanh::LeanObject,
    mut v_prio_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5700_: u8 = 0;
    let mut v_ctxApprox_5701_: u8 = 0;
    let mut v_quasiPatternApprox_5702_: u8 = 0;
    let mut v_constApprox_5703_: u8 = 0;
    let mut v_isDefEqStuckEx_5704_: u8 = 0;
    let mut v_unificationHints_5705_: u8 = 0;
    let mut v_proofIrrelevance_5706_: u8 = 0;
    let mut v_assignSyntheticOpaque_5707_: u8 = 0;
    let mut v_offsetCnstrs_5708_: u8 = 0;
    let mut v_etaStruct_5709_: u8 = 0;
    let mut v_univApprox_5710_: u8 = 0;
    let mut v_iota_5711_: u8 = 0;
    let mut v_beta_5712_: u8 = 0;
    let mut v_proj_5713_: u8 = 0;
    let mut v_zeta_5714_: u8 = 0;
    let mut v_zetaDelta_5715_: u8 = 0;
    let mut v_zetaUnused_5716_: u8 = 0;
    let mut v_zetaHave_5717_: u8 = 0;
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v_trackZetaDelta_5721_: u8 = 0;
    let mut v_zetaDeltaSet_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5728_: u8 = 0;
    let mut v_inTypeClassResolution_5729_: u8 = 0;
    let mut v_cacheInferType_5730_: u8 = 0;
    let mut v___x_5731_: u8 = 0;
    let mut v_config_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: u64 = 0;
    let mut v___x_5735_: u64 = 0;
    let mut v___x_5736_: u64 = 0;
    let mut v___x_5737_: u64 = 0;
    let mut v___x_5738_: u64 = 0;
    let mut v_key_5739_: u64 = 0;
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: u8 = 0;
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v_fst_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: u8 = 0;
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5784_: u8 = 0;
    let mut v_a_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5788_: u8 = 0;
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut v_a_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5796_: u8 = 0;
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5800_: u8 = 0;
    let mut v_a_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_reuseFailAlloc_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5699_ = l_Lean_Meta_Context_config(v_a_5694_);
                v_foApprox_5700_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 0 as u32);
                v_ctxApprox_5701_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 1 as u32);
                v_quasiPatternApprox_5702_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_5699_, 2 as u32);
                v_constApprox_5703_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 3 as u32);
                v_isDefEqStuckEx_5704_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 4 as u32);
                v_unificationHints_5705_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 5 as u32);
                v_proofIrrelevance_5706_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 6 as u32);
                v_assignSyntheticOpaque_5707_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_5699_, 7 as u32);
                v_offsetCnstrs_5708_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 8 as u32);
                v_etaStruct_5709_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 10 as u32);
                v_univApprox_5710_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 11 as u32);
                v_iota_5711_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 12 as u32);
                v_beta_5712_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 13 as u32);
                v_proj_5713_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 14 as u32);
                v_zeta_5714_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 15 as u32);
                v_zetaDelta_5715_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 16 as u32);
                v_zetaUnused_5716_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 17 as u32);
                v_zetaHave_5717_ = crate::leanh::lean_ctor_get_uint8(v___x_5699_, 18 as u32);
                v_isSharedCheck_5810_ = (!crate::leanh::lean_is_exclusive(v___x_5699_)) as u8;
                if v_isSharedCheck_5810_ == 0 {
                    v___x_5719_ = v___x_5699_;
                    v_isShared_5720_ = v_isSharedCheck_5810_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5699_);
                    v___x_5719_ = crate::leanh::lean_box(0);
                    v_isShared_5720_ = v_isSharedCheck_5810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_5721_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5722_ = crate::leanh::lean_ctor_get(v_a_5694_, 1);
                v_lctx_5723_ = crate::leanh::lean_ctor_get(v_a_5694_, 2);
                v_localInstances_5724_ = crate::leanh::lean_ctor_get(v_a_5694_, 3);
                v_defEqCtx_x3f_5725_ = crate::leanh::lean_ctor_get(v_a_5694_, 4);
                v_synthPendingDepth_5726_ = crate::leanh::lean_ctor_get(v_a_5694_, 5);
                v_canUnfold_x3f_5727_ = crate::leanh::lean_ctor_get(v_a_5694_, 6);
                v_univApprox_5728_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5729_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5730_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5731_ = 2;
                if v_isShared_5720_ == 0 {
                    v_config_5733_ = v___x_5719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5809_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        0 as u32,
                        v_foApprox_5700_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        1 as u32,
                        v_ctxApprox_5701_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        2 as u32,
                        v_quasiPatternApprox_5702_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        3 as u32,
                        v_constApprox_5703_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        4 as u32,
                        v_isDefEqStuckEx_5704_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        5 as u32,
                        v_unificationHints_5705_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        6 as u32,
                        v_proofIrrelevance_5706_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        7 as u32,
                        v_assignSyntheticOpaque_5707_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        8 as u32,
                        v_offsetCnstrs_5708_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        10 as u32,
                        v_etaStruct_5709_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        11 as u32,
                        v_univApprox_5710_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        12 as u32,
                        v_iota_5711_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        13 as u32,
                        v_beta_5712_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        14 as u32,
                        v_proj_5713_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        15 as u32,
                        v_zeta_5714_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        16 as u32,
                        v_zetaDelta_5715_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        17 as u32,
                        v_zetaUnused_5716_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5809_,
                        18 as u32,
                        v_zetaHave_5717_,
                    );
                    v_config_5733_ = v_reuseFailAlloc_5809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_5733_, 9 as u32, v___x_5731_);
                v___x_5734_ = l_Lean_Meta_Context_configKey(v_a_5694_);
                v___x_5735_ = 3u64;
                v___x_5736_ = lean_uint64_shift_right(v___x_5734_, v___x_5735_);
                v___x_5737_ = lean_uint64_shift_left(v___x_5736_, v___x_5735_);
                v___x_5738_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpCongrTheorem___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpCongrTheorem___closed__0_once),
                    _init_l_Lean_Meta_mkSimpCongrTheorem___closed__0,
                );
                v_key_5739_ = lean_uint64_lor(v___x_5737_, v___x_5738_);
                v___x_5740_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_5740_, 0, v_config_5733_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5740_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_5739_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_5727_);
                crate::leanh::lean_inc(v_synthPendingDepth_5726_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_5725_);
                crate::leanh::lean_inc_ref(v_localInstances_5724_);
                crate::leanh::lean_inc_ref(v_lctx_5723_);
                crate::leanh::lean_inc(v_zetaDeltaSet_5722_);
                v___x_5741_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5741_, 0, v___x_5740_);
                crate::leanh::lean_ctor_set(v___x_5741_, 1, v_zetaDeltaSet_5722_);
                crate::leanh::lean_ctor_set(v___x_5741_, 2, v_lctx_5723_);
                crate::leanh::lean_ctor_set(v___x_5741_, 3, v_localInstances_5724_);
                crate::leanh::lean_ctor_set(v___x_5741_, 4, v_defEqCtx_x3f_5725_);
                crate::leanh::lean_ctor_set(v___x_5741_, 5, v_synthPendingDepth_5726_);
                crate::leanh::lean_ctor_set(v___x_5741_, 6, v_canUnfold_x3f_5727_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5721_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5728_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5729_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5730_,
                );
                crate::leanh::lean_inc(v_declName_5692_);
                v___x_5742_ =
                    l_Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1(
                        v_declName_5692_,
                        v___x_5741_,
                        v_a_5695_,
                        v_a_5696_,
                        v_a_5697_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5742_) == 0 {
                    v_a_5743_ = crate::leanh::lean_ctor_get(v___x_5742_, 0);
                    crate::leanh::lean_inc(v_a_5743_);
                    crate::leanh::lean_dec_ref_known(v___x_5742_, 1);
                    crate::leanh::lean_inc(v_a_5697_);
                    crate::leanh::lean_inc_ref(v_a_5696_);
                    crate::leanh::lean_inc(v_a_5695_);
                    crate::leanh::lean_inc_ref(v___x_5741_);
                    v___x_5744_ =
                        lean_infer_type(v_a_5743_, v___x_5741_, v_a_5695_, v_a_5696_, v_a_5697_);
                    if crate::leanh::lean_obj_tag(v___x_5744_) == 0 {
                        v_a_5745_ = crate::leanh::lean_ctor_get(v___x_5744_, 0);
                        crate::leanh::lean_inc(v_a_5745_);
                        crate::leanh::lean_dec_ref_known(v___x_5744_, 1);
                        v___x_5746_ = crate::leanh::lean_box(0);
                        v___x_5747_ = 0;
                        v___x_5748_ = l_Lean_Meta_forallMetaTelescopeReducing(
                            v_a_5745_,
                            v___x_5746_,
                            v___x_5747_,
                            v___x_5741_,
                            v_a_5695_,
                            v_a_5696_,
                            v_a_5697_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5748_) == 0 {
                            v_a_5749_ = crate::leanh::lean_ctor_get(v___x_5748_, 0);
                            crate::leanh::lean_inc(v_a_5749_);
                            crate::leanh::lean_dec_ref_known(v___x_5748_, 1);
                            v_snd_5750_ = crate::leanh::lean_ctor_get(v_a_5749_, 1);
                            crate::leanh::lean_inc(v_snd_5750_);
                            v_fst_5751_ = crate::leanh::lean_ctor_get(v_a_5749_, 0);
                            crate::leanh::lean_inc(v_fst_5751_);
                            crate::leanh::lean_dec(v_a_5749_);
                            v_fst_5752_ = crate::leanh::lean_ctor_get(v_snd_5750_, 0);
                            v_snd_5753_ = crate::leanh::lean_ctor_get(v_snd_5750_, 1);
                            v_isSharedCheck_5784_ =
                                (!crate::leanh::lean_is_exclusive(v_snd_5750_)) as u8;
                            if v_isSharedCheck_5784_ == 0 {
                                v___x_5755_ = v_snd_5750_;
                                v_isShared_5756_ = v_isSharedCheck_5784_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5753_);
                                crate::leanh::lean_inc(v_fst_5752_);
                                crate::leanh::lean_dec(v_snd_5750_);
                                v___x_5755_ = crate::leanh::lean_box(0);
                                v_isShared_5756_ = v_isSharedCheck_5784_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_5741_, 7);
                            crate::leanh::lean_dec(v_prio_5693_);
                            crate::leanh::lean_dec(v_declName_5692_);
                            v_a_5785_ = crate::leanh::lean_ctor_get(v___x_5748_, 0);
                            v_isSharedCheck_5792_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5748_)) as u8;
                            if v_isSharedCheck_5792_ == 0 {
                                v___x_5787_ = v___x_5748_;
                                v_isShared_5788_ = v_isSharedCheck_5792_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5785_);
                                crate::leanh::lean_dec(v___x_5748_);
                                v___x_5787_ = crate::leanh::lean_box(0);
                                v_isShared_5788_ = v_isSharedCheck_5792_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_5741_, 7);
                        crate::leanh::lean_dec(v_prio_5693_);
                        crate::leanh::lean_dec(v_declName_5692_);
                        v_a_5793_ = crate::leanh::lean_ctor_get(v___x_5744_, 0);
                        v_isSharedCheck_5800_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5744_)) as u8;
                        if v_isSharedCheck_5800_ == 0 {
                            v___x_5795_ = v___x_5744_;
                            v_isShared_5796_ = v_isSharedCheck_5800_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5793_);
                            crate::leanh::lean_dec(v___x_5744_);
                            v___x_5795_ = crate::leanh::lean_box(0);
                            v_isShared_5796_ = v_isSharedCheck_5800_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5741_, 7);
                    crate::leanh::lean_dec(v_prio_5693_);
                    crate::leanh::lean_dec(v_declName_5692_);
                    v_a_5801_ = crate::leanh::lean_ctor_get(v___x_5742_, 0);
                    v_isSharedCheck_5808_ = (!crate::leanh::lean_is_exclusive(v___x_5742_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5803_ = v___x_5742_;
                        v_isShared_5804_ = v_isSharedCheck_5808_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5801_);
                        crate::leanh::lean_dec(v___x_5742_);
                        v___x_5803_ = crate::leanh::lean_box(0);
                        v_isShared_5804_ = v_isSharedCheck_5808_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__8;
                v___x_5767_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5768_ = l_Lean_Expr_isAppOfArity(v_snd_5753_, v___x_5766_, v___x_5767_);
                if v___x_5768_ == 0 {
                    v___x_5769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__10;
                    v___x_5770_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_5771_ = l_Lean_Expr_isAppOfArity(v_snd_5753_, v___x_5769_, v___x_5770_);
                    if v___x_5771_ == 0 {
                        crate::leanh::lean_dec(v_fst_5752_);
                        crate::leanh::lean_dec(v_fst_5751_);
                        crate::leanh::lean_dec(v_prio_5693_);
                        crate::leanh::lean_dec(v_declName_5692_);
                        v___x_5772_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSimpCongrTheorem___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkSimpCongrTheorem___closed__2_once
                            ),
                            _init_l_Lean_Meta_mkSimpCongrTheorem___closed__2,
                        );
                        v___x_5773_ = l_Lean_indentExpr(v_snd_5753_);
                        if v_isShared_5756_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5755_, 7);
                            crate::leanh::lean_ctor_set(v___x_5755_, 1, v___x_5773_);
                            crate::leanh::lean_ctor_set(v___x_5755_, 0, v___x_5772_);
                            v___x_5775_ = v___x_5755_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_5777_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5772_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 1, v___x_5773_);
                            v___x_5775_ = v_reuseFailAlloc_5777_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5755_);
                        v___x_5778_ = l_Lean_Expr_appFn_x21(v_snd_5753_);
                        v___x_5779_ = l_Lean_Expr_appArg_x21(v___x_5778_);
                        crate::leanh::lean_dec_ref(v___x_5778_);
                        v___x_5780_ = l_Lean_Expr_appArg_x21(v_snd_5753_);
                        v_fst_5758_ = v___x_5779_;
                        v_snd_5759_ = v___x_5780_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5755_);
                    v___x_5781_ = l_Lean_Expr_appFn_x21(v_snd_5753_);
                    v___x_5782_ = l_Lean_Expr_appArg_x21(v___x_5781_);
                    crate::leanh::lean_dec_ref(v___x_5781_);
                    v___x_5783_ = l_Lean_Expr_appArg_x21(v_snd_5753_);
                    v_fst_5758_ = v___x_5782_;
                    v_snd_5759_ = v___x_5783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_dummy_5760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__7___lam__0___closed__0);
                v_nargs_5761_ = l_Lean_Expr_getAppNumArgs(v_fst_5758_);
                crate::leanh::lean_inc(v_nargs_5761_);
                v___x_5762_ = lean_mk_array(v_nargs_5761_, v_dummy_5760_);
                v___x_5763_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5764_ = lean_nat_sub(v_nargs_5761_, v___x_5763_);
                crate::leanh::lean_dec(v_nargs_5761_);
                v___x_5765_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkSimpCongrTheorem_spec__9(
                    v_fst_5752_,
                    v_fst_5751_,
                    v_declName_5692_,
                    v_prio_5693_,
                    v_snd_5753_,
                    v_snd_5759_,
                    v_fst_5758_,
                    v___x_5762_,
                    v___x_5764_,
                    v___x_5741_,
                    v_a_5695_,
                    v_a_5696_,
                    v_a_5697_,
                );
                crate::leanh::lean_dec_ref_known(v___x_5741_, 7);
                crate::leanh::lean_dec(v___x_5764_);
                crate::leanh::lean_dec(v_fst_5751_);
                return v___x_5765_;
            }
            5 => {
                v___x_5776_ =
                    l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
                        v___x_5775_,
                        v___x_5741_,
                        v_a_5695_,
                        v_a_5696_,
                        v_a_5697_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_5741_, 7);
                return v___x_5776_;
            }
            6 => {
                if v_isShared_5788_ == 0 {
                    v___x_5790_ = v___x_5787_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_a_5785_);
                    v___x_5790_ = v_reuseFailAlloc_5791_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5790_;
            }
            8 => {
                if v_isShared_5796_ == 0 {
                    v___x_5798_ = v___x_5795_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5793_);
                    v___x_5798_ = v_reuseFailAlloc_5799_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5798_;
            }
            10 => {
                if v_isShared_5804_ == 0 {
                    v___x_5806_ = v___x_5803_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_a_5801_);
                    v___x_5806_ = v_reuseFailAlloc_5807_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSimpCongrTheorem___boxed(
    mut v_declName_5811_: *mut crate::leanh::LeanObject,
    mut v_prio_5812_: *mut crate::leanh::LeanObject,
    mut v_a_5813_: *mut crate::leanh::LeanObject,
    mut v_a_5814_: *mut crate::leanh::LeanObject,
    mut v_a_5815_: *mut crate::leanh::LeanObject,
    mut v_a_5816_: *mut crate::leanh::LeanObject,
    mut v_a_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5818_ = l_Lean_Meta_mkSimpCongrTheorem(
        v_declName_5811_,
        v_prio_5812_,
        v_a_5813_,
        v_a_5814_,
        v_a_5815_,
        v_a_5816_,
    );
    crate::leanh::lean_dec(v_a_5816_);
    crate::leanh::lean_dec_ref(v_a_5815_);
    crate::leanh::lean_dec(v_a_5814_);
    crate::leanh::lean_dec_ref(v_a_5813_);
    return v_res_5818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(
    mut v_as_5819_: *mut crate::leanh::LeanObject,
    mut v_sz_5820_: usize,
    mut v_i_5821_: usize,
    mut v_b_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___redArg(v_as_5819_, v_sz_5820_, v_i_5821_, v_b_5822_);
    return v___x_5828_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0___boxed(
    mut v_as_5829_: *mut crate::leanh::LeanObject,
    mut v_sz_5830_: *mut crate::leanh::LeanObject,
    mut v_i_5831_: *mut crate::leanh::LeanObject,
    mut v_b_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5838_: usize = 0;
    let mut v_i_boxed_5839_: usize = 0;
    let mut v_res_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5838_ = crate::leanh::lean_unbox_usize(v_sz_5830_);
    crate::leanh::lean_dec(v_sz_5830_);
    v_i_boxed_5839_ = crate::leanh::lean_unbox_usize(v_i_5831_);
    crate::leanh::lean_dec(v_i_5831_);
    v_res_5840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSimpCongrTheorem_spec__0(v_as_5829_, v_sz_boxed_5838_, v_i_boxed_5839_, v_b_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
    crate::leanh::lean_dec(v___y_5836_);
    crate::leanh::lean_dec_ref(v___y_5835_);
    crate::leanh::lean_dec(v___y_5834_);
    crate::leanh::lean_dec_ref(v___y_5833_);
    crate::leanh::lean_dec_ref(v_as_5829_);
    return v_res_5840_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(
    mut v_00_u03b1_5841_: *mut crate::leanh::LeanObject,
    mut v_msg_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5848_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___redArg(
        v_msg_5842_,
        v___y_5843_,
        v___y_5844_,
        v___y_5845_,
        v___y_5846_,
    );
    return v___x_5848_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3___boxed(
    mut v_00_u03b1_5849_: *mut crate::leanh::LeanObject,
    mut v_msg_5850_: *mut crate::leanh::LeanObject,
    mut v___y_5851_: *mut crate::leanh::LeanObject,
    mut v___y_5852_: *mut crate::leanh::LeanObject,
    mut v___y_5853_: *mut crate::leanh::LeanObject,
    mut v___y_5854_: *mut crate::leanh::LeanObject,
    mut v___y_5855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Lean_throwError___at___00Lean_Meta_mkSimpCongrTheorem_spec__3(
        v_00_u03b1_5849_,
        v_msg_5850_,
        v___y_5851_,
        v___y_5852_,
        v___y_5853_,
        v___y_5854_,
    );
    crate::leanh::lean_dec(v___y_5854_);
    crate::leanh::lean_dec_ref(v___y_5853_);
    crate::leanh::lean_dec(v___y_5852_);
    crate::leanh::lean_dec_ref(v___y_5851_);
    return v_res_5856_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(
    mut v_00_u03b1_5857_: *mut crate::leanh::LeanObject,
    mut v_constName_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___redArg(v_constName_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
    return v___x_5864_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b1_5865_: *mut crate::leanh::LeanObject,
    mut v_constName_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5872_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3(v_00_u03b1_5865_, v_constName_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
    crate::leanh::lean_dec(v___y_5870_);
    crate::leanh::lean_dec_ref(v___y_5869_);
    crate::leanh::lean_dec(v___y_5868_);
    crate::leanh::lean_dec_ref(v___y_5867_);
    return v_res_5872_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(
    mut v_00_u03b1_5873_: *mut crate::leanh::LeanObject,
    mut v_ref_5874_: *mut crate::leanh::LeanObject,
    mut v_constName_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
    mut v___y_5877_: *mut crate::leanh::LeanObject,
    mut v___y_5878_: *mut crate::leanh::LeanObject,
    mut v___y_5879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5881_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___redArg(v_ref_5874_, v_constName_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12___boxed(
    mut v_00_u03b1_5882_: *mut crate::leanh::LeanObject,
    mut v_ref_5883_: *mut crate::leanh::LeanObject,
    mut v_constName_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5890_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12(v_00_u03b1_5882_, v_ref_5883_, v_constName_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
    crate::leanh::lean_dec(v___y_5888_);
    crate::leanh::lean_dec_ref(v___y_5887_);
    crate::leanh::lean_dec(v___y_5886_);
    crate::leanh::lean_dec_ref(v___y_5885_);
    crate::leanh::lean_dec(v_ref_5883_);
    return v_res_5890_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(
    mut v_00_u03b1_5891_: *mut crate::leanh::LeanObject,
    mut v_ref_5892_: *mut crate::leanh::LeanObject,
    mut v_msg_5893_: *mut crate::leanh::LeanObject,
    mut v_declHint_5894_: *mut crate::leanh::LeanObject,
    mut v___y_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5900_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___redArg(v_ref_5892_, v_msg_5893_, v_declHint_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
    return v___x_5900_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15___boxed(
    mut v_00_u03b1_5901_: *mut crate::leanh::LeanObject,
    mut v_ref_5902_: *mut crate::leanh::LeanObject,
    mut v_msg_5903_: *mut crate::leanh::LeanObject,
    mut v_declHint_5904_: *mut crate::leanh::LeanObject,
    mut v___y_5905_: *mut crate::leanh::LeanObject,
    mut v___y_5906_: *mut crate::leanh::LeanObject,
    mut v___y_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5910_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15(v_00_u03b1_5901_, v_ref_5902_, v_msg_5903_, v_declHint_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
    crate::leanh::lean_dec(v___y_5908_);
    crate::leanh::lean_dec_ref(v___y_5907_);
    crate::leanh::lean_dec(v___y_5906_);
    crate::leanh::lean_dec_ref(v___y_5905_);
    crate::leanh::lean_dec(v_ref_5902_);
    return v_res_5910_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(
    mut v_msg_5911_: *mut crate::leanh::LeanObject,
    mut v_declHint_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5918_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg(v_msg_5911_, v_declHint_5912_, v___y_5916_);
    return v___x_5918_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___boxed(
    mut v_msg_5919_: *mut crate::leanh::LeanObject,
    mut v_declHint_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5926_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17(v_msg_5919_, v_declHint_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
    crate::leanh::lean_dec(v___y_5924_);
    crate::leanh::lean_dec_ref(v___y_5923_);
    crate::leanh::lean_dec(v___y_5922_);
    crate::leanh::lean_dec_ref(v___y_5921_);
    return v_res_5926_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(
    mut v_00_u03b1_5927_: *mut crate::leanh::LeanObject,
    mut v_ref_5928_: *mut crate::leanh::LeanObject,
    mut v_msg_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
    mut v___y_5931_: *mut crate::leanh::LeanObject,
    mut v___y_5932_: *mut crate::leanh::LeanObject,
    mut v___y_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5935_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___redArg(v_ref_5928_, v_msg_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_);
    return v___x_5935_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17___boxed(
    mut v_00_u03b1_5936_: *mut crate::leanh::LeanObject,
    mut v_ref_5937_: *mut crate::leanh::LeanObject,
    mut v_msg_5938_: *mut crate::leanh::LeanObject,
    mut v___y_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__17(v_00_u03b1_5936_, v_ref_5937_, v_msg_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
    crate::leanh::lean_dec(v___y_5942_);
    crate::leanh::lean_dec_ref(v___y_5941_);
    crate::leanh::lean_dec(v___y_5940_);
    crate::leanh::lean_dec_ref(v___y_5939_);
    crate::leanh::lean_dec(v_ref_5937_);
    return v_res_5944_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5945_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5945_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5946_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__0);
    v___x_5947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5947_, 0, v___x_5946_);
    return v___x_5947_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5948_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
    v___x_5949_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5948_);
    crate::leanh::lean_ctor_set(v___x_5949_, 1, v___x_5948_);
    return v___x_5949_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5950_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__1);
    v___x_5951_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5951_, 0, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 1, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 2, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 3, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 4, v___x_5950_);
    crate::leanh::lean_ctor_set(v___x_5951_, 5, v___x_5950_);
    return v___x_5951_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(
    mut v_ext_5952_: *mut crate::leanh::LeanObject,
    mut v_b_5953_: *mut crate::leanh::LeanObject,
    mut v_kind_5954_: u8,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5992_: u8 = 0;
    let mut v_unused_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5995_: u8 = 0;
    let mut v_unused_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_5959_ = crate::leanh::lean_ctor_get(v___y_5956_, 6);
                v___x_5960_ = lean_st_ref_take(v___y_5957_);
                v_env_5961_ = crate::leanh::lean_ctor_get(v___x_5960_, 0);
                v_nextMacroScope_5962_ = crate::leanh::lean_ctor_get(v___x_5960_, 1);
                v_ngen_5963_ = crate::leanh::lean_ctor_get(v___x_5960_, 2);
                v_auxDeclNGen_5964_ = crate::leanh::lean_ctor_get(v___x_5960_, 3);
                v_traceState_5965_ = crate::leanh::lean_ctor_get(v___x_5960_, 4);
                v_messages_5966_ = crate::leanh::lean_ctor_get(v___x_5960_, 6);
                v_infoState_5967_ = crate::leanh::lean_ctor_get(v___x_5960_, 7);
                v_snapshotTasks_5968_ = crate::leanh::lean_ctor_get(v___x_5960_, 8);
                v_isSharedCheck_5995_ = (!crate::leanh::lean_is_exclusive(v___x_5960_)) as u8;
                if v_isSharedCheck_5995_ == 0 {
                    v_unused_5996_ = crate::leanh::lean_ctor_get(v___x_5960_, 5);
                    crate::leanh::lean_dec(v_unused_5996_);
                    v___x_5970_ = v___x_5960_;
                    v_isShared_5971_ = v_isSharedCheck_5995_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5968_);
                    crate::leanh::lean_inc(v_infoState_5967_);
                    crate::leanh::lean_inc(v_messages_5966_);
                    crate::leanh::lean_inc(v_traceState_5965_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5964_);
                    crate::leanh::lean_inc(v_ngen_5963_);
                    crate::leanh::lean_inc(v_nextMacroScope_5962_);
                    crate::leanh::lean_inc(v_env_5961_);
                    crate::leanh::lean_dec(v___x_5960_);
                    v___x_5970_ = crate::leanh::lean_box(0);
                    v_isShared_5971_ = v_isSharedCheck_5995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_currNamespace_5959_);
                v___x_5972_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_5961_,
                    v_ext_5952_,
                    v_b_5953_,
                    v_kind_5954_,
                    v_currNamespace_5959_,
                );
                v___x_5973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__2);
                if v_isShared_5971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5970_, 5, v___x_5973_);
                    crate::leanh::lean_ctor_set(v___x_5970_, 0, v___x_5972_);
                    v___x_5975_ = v___x_5970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5994_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 0, v___x_5972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 1, v_nextMacroScope_5962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 2, v_ngen_5963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 3, v_auxDeclNGen_5964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 4, v_traceState_5965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 5, v___x_5973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 6, v_messages_5966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 7, v_infoState_5967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 8, v_snapshotTasks_5968_);
                    v___x_5975_ = v_reuseFailAlloc_5994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5976_ = lean_st_ref_set(v___y_5957_, v___x_5975_);
                v___x_5977_ = lean_st_ref_take(v___y_5955_);
                v_mctx_5978_ = crate::leanh::lean_ctor_get(v___x_5977_, 0);
                v_zetaDeltaFVarIds_5979_ = crate::leanh::lean_ctor_get(v___x_5977_, 2);
                v_postponed_5980_ = crate::leanh::lean_ctor_get(v___x_5977_, 3);
                v_diag_5981_ = crate::leanh::lean_ctor_get(v___x_5977_, 4);
                v_isSharedCheck_5992_ = (!crate::leanh::lean_is_exclusive(v___x_5977_)) as u8;
                if v_isSharedCheck_5992_ == 0 {
                    v_unused_5993_ = crate::leanh::lean_ctor_get(v___x_5977_, 1);
                    crate::leanh::lean_dec(v_unused_5993_);
                    v___x_5983_ = v___x_5977_;
                    v_isShared_5984_ = v_isSharedCheck_5992_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5981_);
                    crate::leanh::lean_inc(v_postponed_5980_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5979_);
                    crate::leanh::lean_inc(v_mctx_5978_);
                    crate::leanh::lean_dec(v___x_5977_);
                    v___x_5983_ = crate::leanh::lean_box(0);
                    v_isShared_5984_ = v_isSharedCheck_5992_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___closed__3);
                if v_isShared_5984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5983_, 1, v___x_5985_);
                    v___x_5987_ = v___x_5983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5991_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_mctx_5978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 1, v___x_5985_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5991_,
                        2,
                        v_zetaDeltaFVarIds_5979_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 3, v_postponed_5980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 4, v_diag_5981_);
                    v___x_5987_ = v_reuseFailAlloc_5991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5988_ = lean_st_ref_set(v___y_5955_, v___x_5987_);
                v___x_5989_ = crate::leanh::lean_box(0);
                v___x_5990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5990_, 0, v___x_5989_);
                return v___x_5990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg___boxed(
    mut v_ext_5997_: *mut crate::leanh::LeanObject,
    mut v_b_5998_: *mut crate::leanh::LeanObject,
    mut v_kind_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6004_: u8 = 0;
    let mut v_res_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6004_ = (crate::leanh::lean_unbox(v_kind_5999_) as u8);
    v_res_6005_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(
            v_ext_5997_,
            v_b_5998_,
            v_kind_boxed_6004_,
            v___y_6000_,
            v___y_6001_,
            v___y_6002_,
        );
    crate::leanh::lean_dec(v___y_6002_);
    crate::leanh::lean_dec_ref(v___y_6001_);
    crate::leanh::lean_dec(v___y_6000_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(
    mut v_00_u03b1_6006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6007_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6008_: *mut crate::leanh::LeanObject,
    mut v_ext_6009_: *mut crate::leanh::LeanObject,
    mut v_b_6010_: *mut crate::leanh::LeanObject,
    mut v_kind_6011_: u8,
    mut v___y_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
    mut v___y_6015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6017_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(
            v_ext_6009_,
            v_b_6010_,
            v_kind_6011_,
            v___y_6013_,
            v___y_6014_,
            v___y_6015_,
        );
    return v___x_6017_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___boxed(
    mut v_00_u03b1_6018_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6019_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6020_: *mut crate::leanh::LeanObject,
    mut v_ext_6021_: *mut crate::leanh::LeanObject,
    mut v_b_6022_: *mut crate::leanh::LeanObject,
    mut v_kind_6023_: *mut crate::leanh::LeanObject,
    mut v___y_6024_: *mut crate::leanh::LeanObject,
    mut v___y_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
    mut v___y_6028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6029_: u8 = 0;
    let mut v_res_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6029_ = (crate::leanh::lean_unbox(v_kind_6023_) as u8);
    v_res_6030_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0(
        v_00_u03b1_6018_,
        v_00_u03b2_6019_,
        v_00_u03c3_6020_,
        v_ext_6021_,
        v_b_6022_,
        v_kind_boxed_6029_,
        v___y_6024_,
        v___y_6025_,
        v___y_6026_,
        v___y_6027_,
    );
    crate::leanh::lean_dec(v___y_6027_);
    crate::leanh::lean_dec_ref(v___y_6026_);
    crate::leanh::lean_dec(v___y_6025_);
    crate::leanh::lean_dec_ref(v___y_6024_);
    return v_res_6030_;
}
pub unsafe fn l_Lean_Meta_addSimpCongrTheorem(
    mut v_declName_6031_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6032_: u8,
    mut v_prio_6033_: *mut crate::leanh::LeanObject,
    mut v_a_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
    mut v_a_6037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6046_: u8 = 0;
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6039_ = l_Lean_Meta_mkSimpCongrTheorem(
                    v_declName_6031_,
                    v_prio_6033_,
                    v_a_6034_,
                    v_a_6035_,
                    v_a_6036_,
                    v_a_6037_,
                );
                if crate::leanh::lean_obj_tag(v___x_6039_) == 0 {
                    v_a_6040_ = crate::leanh::lean_ctor_get(v___x_6039_, 0);
                    crate::leanh::lean_inc(v_a_6040_);
                    crate::leanh::lean_dec_ref_known(v___x_6039_, 1);
                    v___x_6041_ = l_Lean_Meta_congrExtension;
                    v___x_6042_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addSimpCongrTheorem_spec__0___redArg(v___x_6041_, v_a_6040_, v_attrKind_6032_, v_a_6035_, v_a_6036_, v_a_6037_);
                    return v___x_6042_;
                } else {
                    v_a_6043_ = crate::leanh::lean_ctor_get(v___x_6039_, 0);
                    v_isSharedCheck_6050_ = (!crate::leanh::lean_is_exclusive(v___x_6039_)) as u8;
                    if v_isSharedCheck_6050_ == 0 {
                        v___x_6045_ = v___x_6039_;
                        v_isShared_6046_ = v_isSharedCheck_6050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6043_);
                        crate::leanh::lean_dec(v___x_6039_);
                        v___x_6045_ = crate::leanh::lean_box(0);
                        v_isShared_6046_ = v_isSharedCheck_6050_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6046_ == 0 {
                    v___x_6048_ = v___x_6045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_a_6043_);
                    v___x_6048_ = v_reuseFailAlloc_6049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addSimpCongrTheorem___boxed(
    mut v_declName_6051_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6052_: *mut crate::leanh::LeanObject,
    mut v_prio_6053_: *mut crate::leanh::LeanObject,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_6059_: u8 = 0;
    let mut v_res_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6059_ = (crate::leanh::lean_unbox(v_attrKind_6052_) as u8);
    v_res_6060_ = l_Lean_Meta_addSimpCongrTheorem(
        v_declName_6051_,
        v_attrKind_boxed_6059_,
        v_prio_6053_,
        v_a_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
    );
    crate::leanh::lean_dec(v_a_6057_);
    crate::leanh::lean_dec_ref(v_a_6056_);
    crate::leanh::lean_dec(v_a_6055_);
    crate::leanh::lean_dec_ref(v_a_6054_);
    return v_res_6060_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: u64 = 0;
    v___x_6067_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6067_);
    return v___x_6068_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6069_: u64 = 0;
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6069_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6070_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6071_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_6071_, 0, v___x_6070_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_6071_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_6069_,
    );
    return v___x_6071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6072_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6072_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6073_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6074_, 0, v___x_6073_);
    return v___x_6074_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6076_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6076_, 0, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 1, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 2, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 3, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 4, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 5, v___x_6075_);
    return v___x_6076_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6078_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6078_, 0, v___x_6077_);
    crate::leanh::lean_ctor_set(v___x_6078_, 1, v___x_6077_);
    crate::leanh::lean_ctor_set(v___x_6078_, 2, v___x_6077_);
    crate::leanh::lean_ctor_set(v___x_6078_, 3, v___x_6077_);
    crate::leanh::lean_ctor_set(v___x_6078_, 4, v___x_6077_);
    return v___x_6078_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(
    mut v___x_6079_: *mut crate::leanh::LeanObject,
    mut v___x_6080_: *mut crate::leanh::LeanObject,
    mut v_declName_6081_: *mut crate::leanh::LeanObject,
    mut v_stx_6082_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6083_: u8,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: u8 = 0;
    let mut v___x_6092_: u8 = 0;
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: usize = 0;
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6087_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6088_ = l_Lean_Syntax_getArg(v_stx_6082_, v___x_6087_);
                v___x_6089_ = l_Lean_getAttrParamOptPrio(v___x_6088_, v___y_6084_, v___y_6085_);
                if crate::leanh::lean_obj_tag(v___x_6089_) == 0 {
                    v_a_6090_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                    crate::leanh::lean_inc(v_a_6090_);
                    crate::leanh::lean_dec_ref_known(v___x_6089_, 1);
                    v___x_6091_ = 0;
                    v___x_6092_ = 1;
                    v___x_6093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
                    v___x_6094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
                    v___x_6095_ = crate::leanh::lean_unsigned_to_nat(32);
                    v___x_6096_ = lean_mk_empty_array_with_capacity(v___x_6095_);
                    v___x_6097_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__3);
                    v___x_6098_ = 5usize;
                    crate::leanh::lean_inc_n(v___x_6079_, 6);
                    v___x_6099_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v___x_6099_, 0, v___x_6097_);
                    crate::leanh::lean_ctor_set(v___x_6099_, 1, v___x_6096_);
                    crate::leanh::lean_ctor_set(v___x_6099_, 2, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6099_, 3, v___x_6079_);
                    crate::leanh::lean_ctor_set_usize(v___x_6099_, 4, v___x_6098_);
                    v___x_6100_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc_ref(v___x_6099_);
                    v___x_6101_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6101_, 0, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6101_, 1, v___x_6099_);
                    crate::leanh::lean_ctor_set(v___x_6101_, 2, v___x_6100_);
                    v___x_6102_ = lean_mk_empty_array_with_capacity(v___x_6079_);
                    v___x_6103_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_6080_);
                    v___x_6104_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v___x_6104_, 0, v___x_6093_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 1, v___x_6080_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 2, v___x_6101_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 3, v___x_6102_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 4, v___x_6103_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 5, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6104_, 6, v___x_6103_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6104_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v___x_6091_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6104_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v___x_6091_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6104_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v___x_6091_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6104_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v___x_6092_,
                    );
                    v___x_6105_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6105_, 0, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 1, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 2, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 3, v___x_6079_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 4, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 5, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 6, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 7, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 8, v___x_6094_);
                    crate::leanh::lean_ctor_set(v___x_6105_, 9, v___x_6094_);
                    v___x_6106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
                    v___x_6107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
                    v___x_6108_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6108_, 0, v___x_6105_);
                    crate::leanh::lean_ctor_set(v___x_6108_, 1, v___x_6106_);
                    crate::leanh::lean_ctor_set(v___x_6108_, 2, v___x_6080_);
                    crate::leanh::lean_ctor_set(v___x_6108_, 3, v___x_6099_);
                    crate::leanh::lean_ctor_set(v___x_6108_, 4, v___x_6107_);
                    v___x_6109_ = lean_st_mk_ref(v___x_6108_);
                    v___x_6110_ = l_Lean_Meta_addSimpCongrTheorem(
                        v_declName_6081_,
                        v_attrKind_6083_,
                        v_a_6090_,
                        v___x_6104_,
                        v___x_6109_,
                        v___y_6084_,
                        v___y_6085_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_6104_, 7);
                    if crate::leanh::lean_obj_tag(v___x_6110_) == 0 {
                        v_isSharedCheck_6119_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6110_)) as u8;
                        if v_isSharedCheck_6119_ == 0 {
                            v_unused_6120_ = crate::leanh::lean_ctor_get(v___x_6110_, 0);
                            crate::leanh::lean_dec(v_unused_6120_);
                            v___x_6112_ = v___x_6110_;
                            v_isShared_6113_ = v_isSharedCheck_6119_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6110_);
                            v___x_6112_ = crate::leanh::lean_box(0);
                            v_isShared_6113_ = v_isSharedCheck_6119_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6109_);
                        return v___x_6110_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_6081_);
                    crate::leanh::lean_dec(v___x_6080_);
                    crate::leanh::lean_dec(v___x_6079_);
                    v_a_6121_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                    v_isSharedCheck_6128_ = (!crate::leanh::lean_is_exclusive(v___x_6089_)) as u8;
                    if v_isSharedCheck_6128_ == 0 {
                        v___x_6123_ = v___x_6089_;
                        v_isShared_6124_ = v_isSharedCheck_6128_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6121_);
                        crate::leanh::lean_dec(v___x_6089_);
                        v___x_6123_ = crate::leanh::lean_box(0);
                        v_isShared_6124_ = v_isSharedCheck_6128_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6114_ = lean_st_ref_get(v___x_6109_);
                crate::leanh::lean_dec(v___x_6109_);
                crate::leanh::lean_dec(v___x_6114_);
                v___x_6115_ = crate::leanh::lean_box(0);
                if v_isShared_6113_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6112_, 0, v___x_6115_);
                    v___x_6117_ = v___x_6112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 0, v___x_6115_);
                    v___x_6117_ = v_reuseFailAlloc_6118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6117_;
            }
            3 => {
                if v_isShared_6124_ == 0 {
                    v___x_6126_ = v___x_6123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
                    v___x_6126_ = v_reuseFailAlloc_6127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(
    mut v___x_6129_: *mut crate::leanh::LeanObject,
    mut v___x_6130_: *mut crate::leanh::LeanObject,
    mut v_declName_6131_: *mut crate::leanh::LeanObject,
    mut v_stx_6132_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_6137_: u8 = 0;
    let mut v_res_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6137_ = (crate::leanh::lean_unbox(v_attrKind_6133_) as u8);
    v_res_6138_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_6129_, v___x_6130_, v_declName_6131_, v_stx_6132_, v_attrKind_boxed_6137_, v___y_6134_, v___y_6135_);
    crate::leanh::lean_dec(v___y_6135_);
    crate::leanh::lean_dec_ref(v___y_6134_);
    crate::leanh::lean_dec(v_stx_6132_);
    return v_res_6138_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
    mut v___y_6141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6143_ = lean_st_ref_get(v___y_6141_);
    v_env_6144_ = crate::leanh::lean_ctor_get(v___x_6143_, 0);
    crate::leanh::lean_inc_ref(v_env_6144_);
    crate::leanh::lean_dec(v___x_6143_);
    v_options_6145_ = crate::leanh::lean_ctor_get(v___y_6140_, 2);
    v___x_6146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__2);
    v___x_6147_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6148_ = lean_mk_empty_array_with_capacity(v___x_6147_);
    crate::leanh::lean_dec_ref(v___x_6148_);
    v___x_6149_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1_spec__3_spec__12_spec__15_spec__16_spec__17___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_6145_);
    v___x_6150_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6150_, 0, v_env_6144_);
    crate::leanh::lean_ctor_set(v___x_6150_, 1, v___x_6146_);
    crate::leanh::lean_ctor_set(v___x_6150_, 2, v___x_6149_);
    crate::leanh::lean_ctor_set(v___x_6150_, 3, v_options_6145_);
    v___x_6151_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6151_, 0, v___x_6150_);
    crate::leanh::lean_ctor_set(v___x_6151_, 1, v_msgData_6139_);
    v___x_6152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6152_, 0, v___x_6151_);
    return v___x_6152_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_6153_: *mut crate::leanh::LeanObject,
    mut v___y_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
    mut v___y_6156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msgData_6153_, v___y_6154_, v___y_6155_);
    crate::leanh::lean_dec(v___y_6155_);
    crate::leanh::lean_dec_ref(v___y_6154_);
    return v_res_6157_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6167_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6162_ = crate::leanh::lean_ctor_get(v___y_6159_, 5);
                v___x_6163_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0_spec__0(v_msg_6158_, v___y_6159_, v___y_6160_);
                v_a_6164_ = crate::leanh::lean_ctor_get(v___x_6163_, 0);
                v_isSharedCheck_6172_ = (!crate::leanh::lean_is_exclusive(v___x_6163_)) as u8;
                if v_isSharedCheck_6172_ == 0 {
                    v___x_6166_ = v___x_6163_;
                    v_isShared_6167_ = v_isSharedCheck_6172_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6164_);
                    crate::leanh::lean_dec(v___x_6163_);
                    v___x_6166_ = crate::leanh::lean_box(0);
                    v_isShared_6167_ = v_isSharedCheck_6172_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_6162_);
                v___x_6168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6168_, 0, v_ref_6162_);
                crate::leanh::lean_ctor_set(v___x_6168_, 1, v_a_6164_);
                if v_isShared_6167_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6166_, 1);
                    crate::leanh::lean_ctor_set(v___x_6166_, 0, v___x_6168_);
                    v___x_6170_ = v___x_6166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6168_);
                    v___x_6170_ = v_reuseFailAlloc_6171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6177_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_6173_, v___y_6174_, v___y_6175_);
    crate::leanh::lean_dec(v___y_6175_);
    crate::leanh::lean_dec_ref(v___y_6174_);
    return v_res_6177_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6180_ = l_Lean_stringToMessageData(v___x_6179_);
    return v___x_6180_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6182_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6183_ = l_Lean_stringToMessageData(v___x_6182_);
    return v___x_6183_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(
    mut v___x_6184_: *mut crate::leanh::LeanObject,
    mut v_decl_6185_: *mut crate::leanh::LeanObject,
    mut v___y_6186_: *mut crate::leanh::LeanObject,
    mut v___y_6187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6190_ = l_Lean_MessageData_ofName(v___x_6184_);
    v___x_6191_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6191_, 0, v___x_6189_);
    crate::leanh::lean_ctor_set(v___x_6191_, 1, v___x_6190_);
    v___x_6192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6193_, 0, v___x_6191_);
    crate::leanh::lean_ctor_set(v___x_6193_, 1, v___x_6192_);
    v___x_6194_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v___x_6193_, v___y_6186_, v___y_6187_);
    return v___x_6194_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(
    mut v___x_6195_: *mut crate::leanh::LeanObject,
    mut v_decl_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6200_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_(v___x_6195_, v_decl_6196_, v___y_6197_, v___y_6198_);
    crate::leanh::lean_dec(v___y_6198_);
    crate::leanh::lean_dec_ref(v___y_6197_);
    crate::leanh::lean_dec(v_decl_6196_);
    return v_res_6200_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = crate::leanh::lean_unsigned_to_nat(3428004144);
    v___x_6259_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6260_ = l_Lean_Name_num___override(v___x_6259_, v___x_6258_);
    return v___x_6260_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6262_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6264_ = l_Lean_Name_str___override(v___x_6263_, v___x_6262_);
    return v___x_6264_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6266_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6267_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6268_ = l_Lean_Name_str___override(v___x_6267_, v___x_6266_);
    return v___x_6268_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6269_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6271_ = l_Lean_Name_num___override(v___x_6270_, v___x_6269_);
    return v___x_6271_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6278_: u8 = 0;
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6278_ = 0;
    v___x_6279_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6280_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6282_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6282_, 0, v___x_6281_);
    crate::leanh::lean_ctor_set(v___x_6282_, 1, v___x_6280_);
    crate::leanh::lean_ctor_set(v___x_6282_, 2, v___x_6279_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6282_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6278_,
    );
    return v___x_6282_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6283_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___f_6284_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6285_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__33_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6286_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6286_, 0, v___x_6285_);
    crate::leanh::lean_ctor_set(v___x_6286_, 1, v___f_6284_);
    crate::leanh::lean_ctor_set(v___x_6286_, 2, v___f_6283_);
    return v___x_6286_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__34_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6289_ = l_Lean_registerBuiltinAttribute(v___x_6288_);
    return v___x_6289_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(
    mut v_a_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6291_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
    return v_res_6291_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_6292_: *mut crate::leanh::LeanObject,
    mut v_msg_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6297_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___redArg(v_msg_6293_, v___y_6294_, v___y_6295_);
    return v___x_6297_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_6298_: *mut crate::leanh::LeanObject,
    mut v_msg_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6303_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__spec__0(v_00_u03b1_6298_, v_msg_6299_, v___y_6300_, v___y_6301_);
    crate::leanh::lean_dec(v___y_6301_);
    crate::leanh::lean_dec_ref(v___y_6300_);
    return v_res_6303_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_);
    v___x_6307_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_;
    v___x_6308_ = l_Lean_addBuiltinDocString(v___x_6306_, v___x_6307_);
    return v___x_6308_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2____boxed(
    mut v_a_6309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6310_ = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
    return v_res_6310_;
}
pub unsafe fn l_Lean_Meta_getSimpCongrTheorems___redArg(
    mut v_a_6311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6313_ = lean_st_ref_get(v_a_6311_);
    v_env_6314_ = crate::leanh::lean_ctor_get(v___x_6313_, 0);
    crate::leanh::lean_inc_ref(v_env_6314_);
    crate::leanh::lean_dec(v___x_6313_);
    v___x_6315_ = l_Lean_Meta_congrExtension;
    v_ext_6316_ = crate::leanh::lean_ctor_get(v___x_6315_, 1);
    v_toEnvExtension_6317_ = crate::leanh::lean_ctor_get(v_ext_6316_, 0);
    v_asyncMode_6318_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6317_, 2);
    v___x_6319_ = l_Lean_Meta_instInhabitedSimpCongrTheorems_default;
    v___x_6320_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_6319_,
        v___x_6315_,
        v_env_6314_,
        v_asyncMode_6318_,
    );
    v___x_6321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6321_, 0, v___x_6320_);
    return v___x_6321_;
}
pub unsafe fn l_Lean_Meta_getSimpCongrTheorems___redArg___boxed(
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v_a_6323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6324_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_6322_);
    crate::leanh::lean_dec(v_a_6322_);
    return v_res_6324_;
}
pub unsafe fn l_Lean_Meta_getSimpCongrTheorems(
    mut v_a_6325_: *mut crate::leanh::LeanObject,
    mut v_a_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_6326_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_Meta_getSimpCongrTheorems___boxed(
    mut v_a_6329_: *mut crate::leanh::LeanObject,
    mut v_a_6330_: *mut crate::leanh::LeanObject,
    mut v_a_6331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6332_ = l_Lean_Meta_getSimpCongrTheorems(v_a_6329_, v_a_6330_);
    crate::leanh::lean_dec(v_a_6330_);
    crate::leanh::lean_dec_ref(v_a_6329_);
    return v_res_6332_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedSimpCongrTheorems_default =
        _init_l_Lean_Meta_instInhabitedSimpCongrTheorems_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorems_default);
    l_Lean_Meta_instInhabitedSimpCongrTheorems = _init_l_Lean_Meta_instInhabitedSimpCongrTheorems();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedSimpCongrTheorems);
    res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3898756595____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_congrExtension = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_congrExtension);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_Simp_SimpCongrTheorems_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_Simp_SimpCongrTheorems_3428004144____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin);
}

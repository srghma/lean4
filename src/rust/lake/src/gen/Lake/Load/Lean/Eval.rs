// Lean compiler output
// Module: Lake.Load.Lean.Eval
// Imports: Lake.Config.Workspace Lake.Config.LakefileConfig Lean.DocString Lake.DSL.AttributesCore
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_string_append,
    lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lake::Config::ConfigDecl::l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
use crate::r#gen::Lake::Config::Dependency::l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
use crate::r#gen::Lake::Config::FacetConfig::{
    l_Lake_instTypeNameLibraryFacetDecl_unsafe__1, l_Lake_instTypeNameModuleFacetDecl_unsafe__1,
    l_Lake_instTypeNamePackageFacetDecl_unsafe__1,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_LeanExe_keyword;
use crate::r#gen::Lake::Config::LakefileConfig::{
    initialize_Lake_Config_LakefileConfig, runtime_initialize_Lake_Config_LakefileConfig,
};
use crate::r#gen::Lake::Config::Package::l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
use crate::r#gen::Lake::Config::PackageConfig::l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
use crate::r#gen::Lake::Config::Script::l_Lake_instTypeNameScriptFn_unsafe__1;
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::DSL::AttributesCore::{
    initialize_Lake_DSL_AttributesCore, l_Lake_defaultScriptAttr, l_Lake_defaultTargetAttr,
    l_Lake_libraryFacetAttr, l_Lake_lintDriverAttr, l_Lake_moduleFacetAttr, l_Lake_packageAttr,
    l_Lake_packageDepAttr, l_Lake_packageFacetAttr, l_Lake_postUpdateAttr, l_Lake_scriptAttr,
    l_Lake_targetAttr, l_Lake_testDriverAttr, runtime_initialize_Lake_DSL_AttributesCore,
};
use crate::r#gen::Lake::Util::OrderedTagAttribute::l_Lake_OrderedTagAttribute_getAllEntries;
use crate::r#gen::Lake::Util::RBArray::{
    l_Lake_RBArray_insert___redArg, l_Lake_RBArray_mkEmpty___redArg,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DocString::{
    initialize_Lean_DocString, l_Lean_findDocString_x3f, runtime_initialize_Lean_DocString,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConst___redArg, l_Lean_Environment_find_x3f,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116, 32, 39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [39, 44, 32, 96, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 102, 105, 108, 101, 32,
        105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 97, 32, 96, 112, 97, 99, 107, 97, 103,
        101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value:
    crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 102, 105, 108, 101, 32,
        104, 97, 115, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 96, 112, 97, 99, 107, 97,
        103, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value:
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
    m_data: [47, 0],
};
static mut l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [112, 111, 115, 116, 45, 117, 112, 100, 97, 116, 101, 32, 104, 111, 111, 107, 32, 119, 97, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 44, 32, 98, 117, 116, 32, 119, 97, 115, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 105, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 32, 119, 97, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 44, 32, 98, 117, 116, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 117, 110, 100, 101, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [58, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 32, 104, 97, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 114, 111, 111, 116, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [39, 32, 97, 115, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 115, 99, 114, 105, 112, 116, 32, 111, 114, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 116, 101, 115, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 108, 105, 110, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 115, 99, 114, 105, 112, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [58, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 32, 119, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 100, 101, 102, 105, 110, 101, 100, 32, 97, 115, 32, 97, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 44, 32, 98, 117, 116, 32, 116, 104, 101, 110, 32, 114, 101, 100, 101, 102, 105, 110, 101, 100, 32, 97, 115, 32, 97, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_LakefileConfig_loadFromEnv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__1_value: crate::leanh::LeanStringObject<52> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            58, 32, 99, 97, 110, 110, 111, 116, 32, 98, 111, 116, 104, 32, 115, 101, 116, 32, 108,
            105, 110, 116, 68, 114, 105, 118, 101, 114, 32, 97, 110, 100, 32, 117, 115, 101, 32,
            64, 91, 108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__2_value: crate::leanh::LeanStringObject<61> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 61,
        m_capacity: 61,
        m_length: 60,
        m_data: [
            58, 32, 111, 110, 108, 121, 32, 111, 110, 101, 32, 115, 99, 114, 105, 112, 116, 32,
            111, 114, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 99, 97, 110, 32, 98,
            101, 32, 116, 97, 103, 103, 101, 100, 32, 64, 91, 108, 105, 110, 116, 95, 100, 114,
            105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__3_value: crate::leanh::LeanStringObject<52> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            58, 32, 99, 97, 110, 110, 111, 116, 32, 98, 111, 116, 104, 32, 115, 101, 116, 32, 116,
            101, 115, 116, 68, 114, 105, 118, 101, 114, 32, 97, 110, 100, 32, 117, 115, 101, 32,
            64, 91, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__4_value: crate::leanh::LeanStringObject<71> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 71,
        m_capacity: 71,
        m_length: 70,
        m_data: [
            58, 32, 111, 110, 108, 121, 32, 111, 110, 101, 32, 115, 99, 114, 105, 112, 116, 44, 32,
            101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 44, 32, 111, 114, 32, 108, 105, 98, 114,
            97, 114, 121, 32, 99, 97, 110, 32, 98, 101, 32, 116, 97, 103, 103, 101, 100, 32, 64,
            91, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(
    mut v_inst_1780_: *mut crate::leanh::LeanObject,
    mut v_const_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0;
    v___x_1783_ = 1;
    v___x_1784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_const_1781_,
        v___x_1783_,
    );
    v___x_1785_ = lean_string_append(v___x_1782_, v___x_1784_);
    crate::leanh::lean_dec_ref(v___x_1784_);
    v___x_1786_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1;
    v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
    v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_inst_1780_,
        v___x_1783_,
    );
    v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
    crate::leanh::lean_dec_ref(v___x_1788_);
    v___x_1790_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2;
    v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
    v___x_1792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1791_);
    return v___x_1792_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType(
    mut v_00_u03b1_1793_: *mut crate::leanh::LeanObject,
    mut v_inst_1794_: *mut crate::leanh::LeanObject,
    mut v_const_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ =
        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(
            v_inst_1794_,
            v_const_1795_,
        );
    return v___x_1796_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
    mut v_env_1799_: *mut crate::leanh::LeanObject,
    mut v_opts_1800_: *mut crate::leanh::LeanObject,
    mut v_inst_1801_: *mut crate::leanh::LeanObject,
    mut v_const_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = 0;
    crate::leanh::lean_inc(v_const_1802_);
    crate::leanh::lean_inc_ref(v_env_1799_);
    v___x_1804_ = l_Lean_Environment_find_x3f(v_env_1799_, v_const_1802_, v___x_1803_);
    if crate::leanh::lean_obj_tag(v___x_1804_) == 0 {
        let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: u8 = 0;
        let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_1801_);
        crate::leanh::lean_dec_ref(v_env_1799_);
        v___x_1805_ =
            l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0;
        v___x_1806_ = 1;
        v___x_1807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_const_1802_,
            v___x_1806_,
        );
        v___x_1808_ = lean_string_append(v___x_1805_, v___x_1807_);
        crate::leanh::lean_dec_ref(v___x_1807_);
        v___x_1809_ =
            l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
        v___x_1810_ = lean_string_append(v___x_1808_, v___x_1809_);
        v___x_1811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
        return v___x_1811_;
    } else {
        let mut v_val_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1812_ = crate::leanh::lean_ctor_get(v___x_1804_, 0);
        crate::leanh::lean_inc(v_val_1812_);
        crate::leanh::lean_dec_ref_known(v___x_1804_, 1);
        v___x_1813_ = l_Lean_ConstantInfo_type(v_val_1812_);
        crate::leanh::lean_dec(v_val_1812_);
        if crate::leanh::lean_obj_tag(v___x_1813_) == 4 {
            let mut v_declName_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1815_: u8 = 0;
            v_declName_1814_ = crate::leanh::lean_ctor_get(v___x_1813_, 0);
            crate::leanh::lean_inc(v_declName_1814_);
            crate::leanh::lean_dec_ref_known(v___x_1813_, 2);
            v___x_1815_ = lean_name_eq(v_declName_1814_, v_inst_1801_);
            crate::leanh::lean_dec(v_declName_1814_);
            if v___x_1815_ == 0 {
                let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_env_1799_);
                v___x_1816_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_1801_, v_const_1802_);
                return v___x_1816_;
            } else {
                let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_inst_1801_);
                v___x_1817_ = l_Lean_Environment_evalConst___redArg(
                    v_env_1799_,
                    v_opts_1800_,
                    v_const_1802_,
                    v___x_1815_,
                );
                crate::leanh::lean_dec(v_const_1802_);
                crate::leanh::lean_dec_ref(v_env_1799_);
                return v___x_1817_;
            }
        } else {
            let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_1813_);
            crate::leanh::lean_dec_ref(v_env_1799_);
            v___x_1818_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_1801_, v_const_1802_);
            return v___x_1818_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___boxed(
    mut v_env_1819_: *mut crate::leanh::LeanObject,
    mut v_opts_1820_: *mut crate::leanh::LeanObject,
    mut v_inst_1821_: *mut crate::leanh::LeanObject,
    mut v_const_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_1819_,
        v_opts_1820_,
        v_inst_1821_,
        v_const_1822_,
    );
    crate::leanh::lean_dec_ref(v_opts_1820_);
    return v_res_1823_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(
    mut v_env_1824_: *mut crate::leanh::LeanObject,
    mut v_opts_1825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1826_: *mut crate::leanh::LeanObject,
    mut v_inst_1827_: *mut crate::leanh::LeanObject,
    mut v_const_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_1824_,
        v_opts_1825_,
        v_inst_1827_,
        v_const_1828_,
    );
    return v___x_1829_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___boxed(
    mut v_env_1830_: *mut crate::leanh::LeanObject,
    mut v_opts_1831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1832_: *mut crate::leanh::LeanObject,
    mut v_inst_1833_: *mut crate::leanh::LeanObject,
    mut v_const_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(
        v_env_1830_,
        v_opts_1831_,
        v_00_u03b1_1832_,
        v_inst_1833_,
        v_const_1834_,
    );
    crate::leanh::lean_dec_ref(v_opts_1831_);
    return v_res_1835_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0(
    mut v_declName_1837_: *mut crate::leanh::LeanObject,
    mut v_map_1838_: *mut crate::leanh::LeanObject,
    mut v_toPure_1839_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
    v___x_1842_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v___x_1841_,
        v_declName_1837_,
        v_____do__lift_1840_,
        v_map_1838_,
    );
    v___x_1843_ =
        crate::leanh::lean_apply_2(v_toPure_1839_, crate::leanh::lean_box(0), v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1(
    mut v_toPure_1844_: *mut crate::leanh::LeanObject,
    mut v_f_1845_: *mut crate::leanh::LeanObject,
    mut v_toBind_1846_: *mut crate::leanh::LeanObject,
    mut v_map_1847_: *mut crate::leanh::LeanObject,
    mut v_declName_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_declName_1848_);
    v___f_1849_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1849_, 0, v_declName_1848_);
    crate::leanh::lean_closure_set(v___f_1849_, 1, v_map_1847_);
    crate::leanh::lean_closure_set(v___f_1849_, 2, v_toPure_1844_);
    v___x_1850_ = crate::leanh::lean_apply_1(v_f_1845_, v_declName_1848_);
    v___x_1851_ = crate::leanh::lean_apply_4(
        v_toBind_1846_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1850_,
        v___f_1849_,
    );
    return v___x_1851_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
    mut v_env_1852_: *mut crate::leanh::LeanObject,
    mut v_attr_1853_: *mut crate::leanh::LeanObject,
    mut v_inst_1854_: *mut crate::leanh::LeanObject,
    mut v_f_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    v_toApplicative_1856_ = crate::leanh::lean_ctor_get(v_inst_1854_, 0);
    v_toBind_1857_ = crate::leanh::lean_ctor_get(v_inst_1854_, 1);
    v_toPure_1858_ = crate::leanh::lean_ctor_get(v_toApplicative_1856_, 1);
    v_entries_1859_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1853_, v_env_1852_);
    v___x_1860_ = crate::leanh::lean_box(1);
    v___x_1861_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1862_ = lean_array_get_size(v_entries_1859_);
    v___x_1863_ = lean_nat_dec_lt(v___x_1861_, v___x_1862_);
    if v___x_1863_ == 0 {
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_1858_);
        crate::leanh::lean_dec_ref(v_entries_1859_);
        crate::leanh::lean_dec(v_f_1855_);
        crate::leanh::lean_dec_ref(v_inst_1854_);
        v___x_1864_ =
            crate::leanh::lean_apply_2(v_toPure_1858_, crate::leanh::lean_box(0), v___x_1860_);
        return v___x_1864_;
    } else {
        let mut v___f_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: u8 = 0;
        crate::leanh::lean_inc(v_toBind_1857_);
        crate::leanh::lean_inc(v_toPure_1858_);
        v___f_1865_ = crate::leanh::lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1865_, 0, v_toPure_1858_);
        crate::leanh::lean_closure_set(v___f_1865_, 1, v_f_1855_);
        crate::leanh::lean_closure_set(v___f_1865_, 2, v_toBind_1857_);
        v___x_1866_ = lean_nat_dec_le(v___x_1862_, v___x_1862_);
        if v___x_1866_ == 0 {
            if v___x_1863_ == 0 {
                let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_toPure_1858_);
                crate::leanh::lean_dec_ref(v___f_1865_);
                crate::leanh::lean_dec_ref(v_entries_1859_);
                crate::leanh::lean_dec_ref(v_inst_1854_);
                v___x_1867_ = crate::leanh::lean_apply_2(
                    v_toPure_1858_,
                    crate::leanh::lean_box(0),
                    v___x_1860_,
                );
                return v___x_1867_;
            } else {
                let mut v___x_1868_: usize = 0;
                let mut v___x_1869_: usize = 0;
                let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1868_ = 0usize;
                v___x_1869_ = lean_usize_of_nat(v___x_1862_);
                v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1854_,
                    v___f_1865_,
                    v_entries_1859_,
                    v___x_1868_,
                    v___x_1869_,
                    v___x_1860_,
                );
                return v___x_1870_;
            }
        } else {
            let mut v___x_1871_: usize = 0;
            let mut v___x_1872_: usize = 0;
            let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1871_ = 0usize;
            v___x_1872_ = lean_usize_of_nat(v___x_1862_);
            v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1854_,
                v___f_1865_,
                v_entries_1859_,
                v___x_1871_,
                v___x_1872_,
                v___x_1860_,
            );
            return v___x_1873_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___boxed(
    mut v_env_1874_: *mut crate::leanh::LeanObject,
    mut v_attr_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_f_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
        v_env_1874_,
        v_attr_1875_,
        v_inst_1876_,
        v_f_1877_,
    );
    crate::leanh::lean_dec_ref(v_attr_1875_);
    return v_res_1878_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(
    mut v_m_1879_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1880_: *mut crate::leanh::LeanObject,
    mut v_env_1881_: *mut crate::leanh::LeanObject,
    mut v_attr_1882_: *mut crate::leanh::LeanObject,
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_f_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
        v_env_1881_,
        v_attr_1882_,
        v_inst_1883_,
        v_f_1884_,
    );
    return v___x_1885_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(
    mut v_m_1886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1887_: *mut crate::leanh::LeanObject,
    mut v_env_1888_: *mut crate::leanh::LeanObject,
    mut v_attr_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_f_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(
        v_m_1886_,
        v_00_u03b2_1887_,
        v_env_1888_,
        v_attr_1889_,
        v_inst_1890_,
        v_f_1891_,
    );
    crate::leanh::lean_dec_ref(v_attr_1889_);
    return v_res_1892_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(
    mut v_declName_1893_: *mut crate::leanh::LeanObject,
    mut v_map_1894_: *mut crate::leanh::LeanObject,
    mut v_toPure_1895_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_declName_1893_,
        v_____do__lift_1896_,
        v_map_1894_,
    );
    v___x_1898_ =
        crate::leanh::lean_apply_2(v_toPure_1895_, crate::leanh::lean_box(0), v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(
    mut v_toPure_1899_: *mut crate::leanh::LeanObject,
    mut v_f_1900_: *mut crate::leanh::LeanObject,
    mut v_toBind_1901_: *mut crate::leanh::LeanObject,
    mut v_map_1902_: *mut crate::leanh::LeanObject,
    mut v_declName_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_declName_1903_);
    v___f_1904_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1904_, 0, v_declName_1903_);
    crate::leanh::lean_closure_set(v___f_1904_, 1, v_map_1902_);
    crate::leanh::lean_closure_set(v___f_1904_, 2, v_toPure_1899_);
    v___x_1905_ = crate::leanh::lean_apply_1(v_f_1900_, v_declName_1903_);
    v___x_1906_ = crate::leanh::lean_apply_4(
        v_toBind_1901_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1905_,
        v___f_1904_,
    );
    return v___x_1906_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
    mut v_env_1907_: *mut crate::leanh::LeanObject,
    mut v_attr_1908_: *mut crate::leanh::LeanObject,
    mut v_inst_1909_: *mut crate::leanh::LeanObject,
    mut v_f_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: u8 = 0;
    v_toApplicative_1911_ = crate::leanh::lean_ctor_get(v_inst_1909_, 0);
    v_toBind_1912_ = crate::leanh::lean_ctor_get(v_inst_1909_, 1);
    v_toPure_1913_ = crate::leanh::lean_ctor_get(v_toApplicative_1911_, 1);
    v_entries_1914_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1908_, v_env_1907_);
    v___x_1915_ = crate::leanh::lean_box(1);
    v___x_1916_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1917_ = lean_array_get_size(v_entries_1914_);
    v___x_1918_ = lean_nat_dec_lt(v___x_1916_, v___x_1917_);
    if v___x_1918_ == 0 {
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_1913_);
        crate::leanh::lean_dec_ref(v_entries_1914_);
        crate::leanh::lean_dec(v_f_1910_);
        crate::leanh::lean_dec_ref(v_inst_1909_);
        v___x_1919_ =
            crate::leanh::lean_apply_2(v_toPure_1913_, crate::leanh::lean_box(0), v___x_1915_);
        return v___x_1919_;
    } else {
        let mut v___f_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: u8 = 0;
        crate::leanh::lean_inc(v_toBind_1912_);
        crate::leanh::lean_inc(v_toPure_1913_);
        v___f_1920_ = crate::leanh::lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1920_, 0, v_toPure_1913_);
        crate::leanh::lean_closure_set(v___f_1920_, 1, v_f_1910_);
        crate::leanh::lean_closure_set(v___f_1920_, 2, v_toBind_1912_);
        v___x_1921_ = lean_nat_dec_le(v___x_1917_, v___x_1917_);
        if v___x_1921_ == 0 {
            if v___x_1918_ == 0 {
                let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_toPure_1913_);
                crate::leanh::lean_dec_ref(v___f_1920_);
                crate::leanh::lean_dec_ref(v_entries_1914_);
                crate::leanh::lean_dec_ref(v_inst_1909_);
                v___x_1922_ = crate::leanh::lean_apply_2(
                    v_toPure_1913_,
                    crate::leanh::lean_box(0),
                    v___x_1915_,
                );
                return v___x_1922_;
            } else {
                let mut v___x_1923_: usize = 0;
                let mut v___x_1924_: usize = 0;
                let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1923_ = 0usize;
                v___x_1924_ = lean_usize_of_nat(v___x_1917_);
                v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1909_,
                    v___f_1920_,
                    v_entries_1914_,
                    v___x_1923_,
                    v___x_1924_,
                    v___x_1915_,
                );
                return v___x_1925_;
            }
        } else {
            let mut v___x_1926_: usize = 0;
            let mut v___x_1927_: usize = 0;
            let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1926_ = 0usize;
            v___x_1927_ = lean_usize_of_nat(v___x_1917_);
            v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1909_,
                v___f_1920_,
                v_entries_1914_,
                v___x_1926_,
                v___x_1927_,
                v___x_1915_,
            );
            return v___x_1928_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___boxed(
    mut v_env_1929_: *mut crate::leanh::LeanObject,
    mut v_attr_1930_: *mut crate::leanh::LeanObject,
    mut v_inst_1931_: *mut crate::leanh::LeanObject,
    mut v_f_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
        v_env_1929_,
        v_attr_1930_,
        v_inst_1931_,
        v_f_1932_,
    );
    crate::leanh::lean_dec_ref(v_attr_1930_);
    return v_res_1933_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(
    mut v_m_1934_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1935_: *mut crate::leanh::LeanObject,
    mut v_env_1936_: *mut crate::leanh::LeanObject,
    mut v_attr_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
    mut v_f_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
        v_env_1936_,
        v_attr_1937_,
        v_inst_1938_,
        v_f_1939_,
    );
    return v___x_1940_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(
    mut v_m_1941_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1942_: *mut crate::leanh::LeanObject,
    mut v_env_1943_: *mut crate::leanh::LeanObject,
    mut v_attr_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_f_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(
        v_m_1941_,
        v_00_u03b2_1942_,
        v_env_1943_,
        v_attr_1944_,
        v_inst_1945_,
        v_f_1946_,
    );
    crate::leanh::lean_dec_ref(v_attr_1944_);
    return v_res_1947_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(
    mut v_map_1948_: *mut crate::leanh::LeanObject,
    mut v_declName_1949_: *mut crate::leanh::LeanObject,
    mut v_toPure_1950_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
    v___x_1953_ = l_Lake_RBArray_insert___redArg(
        v___x_1952_,
        v_map_1948_,
        v_declName_1949_,
        v_____do__lift_1951_,
    );
    v___x_1954_ =
        crate::leanh::lean_apply_2(v_toPure_1950_, crate::leanh::lean_box(0), v___x_1953_);
    return v___x_1954_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(
    mut v_toPure_1955_: *mut crate::leanh::LeanObject,
    mut v_f_1956_: *mut crate::leanh::LeanObject,
    mut v_toBind_1957_: *mut crate::leanh::LeanObject,
    mut v_map_1958_: *mut crate::leanh::LeanObject,
    mut v_declName_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_declName_1959_);
    v___f_1960_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1960_, 0, v_map_1958_);
    crate::leanh::lean_closure_set(v___f_1960_, 1, v_declName_1959_);
    crate::leanh::lean_closure_set(v___f_1960_, 2, v_toPure_1955_);
    v___x_1961_ = crate::leanh::lean_apply_1(v_f_1956_, v_declName_1959_);
    v___x_1962_ = crate::leanh::lean_apply_4(
        v_toBind_1957_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1961_,
        v___f_1960_,
    );
    return v___x_1962_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
    mut v_env_1963_: *mut crate::leanh::LeanObject,
    mut v_attr_1964_: *mut crate::leanh::LeanObject,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_f_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    v_toApplicative_1967_ = crate::leanh::lean_ctor_get(v_inst_1965_, 0);
    v_toBind_1968_ = crate::leanh::lean_ctor_get(v_inst_1965_, 1);
    v_toPure_1969_ = crate::leanh::lean_ctor_get(v_toApplicative_1967_, 1);
    v_entries_1970_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1964_, v_env_1963_);
    v___x_1971_ = lean_array_get_size(v_entries_1970_);
    v___x_1972_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1971_);
    v___x_1973_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1974_ = lean_nat_dec_lt(v___x_1973_, v___x_1971_);
    if v___x_1974_ == 0 {
        let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_1969_);
        crate::leanh::lean_dec_ref(v_entries_1970_);
        crate::leanh::lean_dec(v_f_1966_);
        crate::leanh::lean_dec_ref(v_inst_1965_);
        v___x_1975_ =
            crate::leanh::lean_apply_2(v_toPure_1969_, crate::leanh::lean_box(0), v___x_1972_);
        return v___x_1975_;
    } else {
        let mut v___f_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: u8 = 0;
        crate::leanh::lean_inc(v_toBind_1968_);
        crate::leanh::lean_inc(v_toPure_1969_);
        v___f_1976_ = crate::leanh::lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1976_, 0, v_toPure_1969_);
        crate::leanh::lean_closure_set(v___f_1976_, 1, v_f_1966_);
        crate::leanh::lean_closure_set(v___f_1976_, 2, v_toBind_1968_);
        v___x_1977_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
        if v___x_1977_ == 0 {
            if v___x_1974_ == 0 {
                let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_toPure_1969_);
                crate::leanh::lean_dec_ref(v___f_1976_);
                crate::leanh::lean_dec_ref(v_entries_1970_);
                crate::leanh::lean_dec_ref(v_inst_1965_);
                v___x_1978_ = crate::leanh::lean_apply_2(
                    v_toPure_1969_,
                    crate::leanh::lean_box(0),
                    v___x_1972_,
                );
                return v___x_1978_;
            } else {
                let mut v___x_1979_: usize = 0;
                let mut v___x_1980_: usize = 0;
                let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1979_ = 0usize;
                v___x_1980_ = lean_usize_of_nat(v___x_1971_);
                v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1965_,
                    v___f_1976_,
                    v_entries_1970_,
                    v___x_1979_,
                    v___x_1980_,
                    v___x_1972_,
                );
                return v___x_1981_;
            }
        } else {
            let mut v___x_1982_: usize = 0;
            let mut v___x_1983_: usize = 0;
            let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1982_ = 0usize;
            v___x_1983_ = lean_usize_of_nat(v___x_1971_);
            v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1965_,
                v___f_1976_,
                v_entries_1970_,
                v___x_1982_,
                v___x_1983_,
                v___x_1972_,
            );
            return v___x_1984_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___boxed(
    mut v_env_1985_: *mut crate::leanh::LeanObject,
    mut v_attr_1986_: *mut crate::leanh::LeanObject,
    mut v_inst_1987_: *mut crate::leanh::LeanObject,
    mut v_f_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
        v_env_1985_,
        v_attr_1986_,
        v_inst_1987_,
        v_f_1988_,
    );
    crate::leanh::lean_dec_ref(v_attr_1986_);
    return v_res_1989_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(
    mut v_m_1990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1991_: *mut crate::leanh::LeanObject,
    mut v_env_1992_: *mut crate::leanh::LeanObject,
    mut v_attr_1993_: *mut crate::leanh::LeanObject,
    mut v_inst_1994_: *mut crate::leanh::LeanObject,
    mut v_f_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
        v_env_1992_,
        v_attr_1993_,
        v_inst_1994_,
        v_f_1995_,
    );
    return v___x_1996_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(
    mut v_m_1997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1998_: *mut crate::leanh::LeanObject,
    mut v_env_1999_: *mut crate::leanh::LeanObject,
    mut v_attr_2000_: *mut crate::leanh::LeanObject,
    mut v_inst_2001_: *mut crate::leanh::LeanObject,
    mut v_f_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2003_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(
        v_m_1997_,
        v_00_u03b2_1998_,
        v_env_1999_,
        v_attr_2000_,
        v_inst_2001_,
        v_f_2002_,
    );
    crate::leanh::lean_dec_ref(v_attr_2000_);
    return v_res_2003_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(
    mut v_env_2010_: *mut crate::leanh::LeanObject,
    mut v_opts_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lake_packageAttr;
    crate::leanh::lean_inc_ref(v_env_2010_);
    v___x_2013_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_2012_, v_env_2010_);
    v___x_2014_ = lean_array_to_list(v___x_2013_);
    if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
        let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_2010_);
        v___x_2015_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1;
        return v___x_2015_;
    } else {
        let mut v_tail_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2016_ = crate::leanh::lean_ctor_get(v___x_2014_, 1);
        crate::leanh::lean_inc(v_tail_2016_);
        if crate::leanh::lean_obj_tag(v_tail_2016_) == 0 {
            let mut v_head_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_2017_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
            crate::leanh::lean_inc(v_head_2017_);
            crate::leanh::lean_dec_ref_known(v___x_2014_, 2);
            v___x_2018_ =
                l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_;
            v___x_2019_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                v_env_2010_,
                v_opts_2011_,
                v___x_2018_,
                v_head_2017_,
            );
            return v___x_2019_;
        } else {
            let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2014_, 2);
            crate::leanh::lean_dec(v_tail_2016_);
            crate::leanh::lean_dec_ref(v_env_2010_);
            v___x_2020_ =
                l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3;
            return v___x_2020_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(
    mut v_env_2021_: *mut crate::leanh::LeanObject,
    mut v_opts_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2023_ =
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_2021_, v_opts_2022_);
    crate::leanh::lean_dec_ref(v_opts_2022_);
    return v_res_2023_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
    mut v_e_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut v_a_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_2024_) == 0 {
                    v_a_2026_ = crate::leanh::lean_ctor_get(v_e_2024_, 0);
                    v_isSharedCheck_2034_ = (!crate::leanh::lean_is_exclusive(v_e_2024_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2028_ = v_e_2024_;
                        v_isShared_2029_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2026_);
                        crate::leanh::lean_dec(v_e_2024_);
                        v___x_2028_ = crate::leanh::lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2035_ = crate::leanh::lean_ctor_get(v_e_2024_, 0);
                    v_isSharedCheck_2042_ = (!crate::leanh::lean_is_exclusive(v_e_2024_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v___x_2037_ = v_e_2024_;
                        v_isShared_2038_ = v_isSharedCheck_2042_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2035_);
                        crate::leanh::lean_dec(v_e_2024_);
                        v___x_2037_ = crate::leanh::lean_box(0);
                        v_isShared_2038_ = v_isSharedCheck_2042_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2030_ = lean_mk_io_user_error(v_a_2026_);
                if v_isShared_2029_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2028_, 1);
                    crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2030_);
                    v___x_2032_ = v___x_2028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2032_;
            }
            3 => {
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2037_, 0);
                    v___x_2040_ = v___x_2037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
                    v___x_2040_ = v_reuseFailAlloc_2041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(
    mut v_e_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2045_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_2043_);
    return v_res_2045_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(
    mut v_00_u03b1_2046_: *mut crate::leanh::LeanObject,
    mut v_e_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_2047_);
    return v___x_2049_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(
    mut v_00_u03b1_2050_: *mut crate::leanh::LeanObject,
    mut v_e_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(v_00_u03b1_2050_, v_e_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__0(
    mut v_env_2054_: *mut crate::leanh::LeanObject,
    mut v_opts_2055_: *mut crate::leanh::LeanObject,
    mut v___x_2056_: *mut crate::leanh::LeanObject,
    mut v_name_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_2054_,
        v_opts_2055_,
        v___x_2056_,
        v_name_2057_,
    );
    return v___x_2058_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(
    mut v_env_2059_: *mut crate::leanh::LeanObject,
    mut v_opts_2060_: *mut crate::leanh::LeanObject,
    mut v___x_2061_: *mut crate::leanh::LeanObject,
    mut v_name_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lake_LakefileConfig_loadFromEnv___lam__0(
        v_env_2059_,
        v_opts_2060_,
        v___x_2061_,
        v_name_2062_,
    );
    crate::leanh::lean_dec_ref(v_opts_2060_);
    return v_res_2063_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__1(
    mut v___x_2065_: u8,
    mut v_env_2066_: *mut crate::leanh::LeanObject,
    mut v_opts_2067_: *mut crate::leanh::LeanObject,
    mut v___x_2068_: *mut crate::leanh::LeanObject,
    mut v___x_2069_: *mut crate::leanh::LeanObject,
    mut v_scriptName_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_scriptName_2070_, 2);
    v___x_2073_ = l_Lean_Name_toString(v_scriptName_2070_, v___x_2065_);
    crate::leanh::lean_inc_ref(v_env_2066_);
    v___x_2074_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_2066_,
        v_opts_2067_,
        v___x_2068_,
        v_scriptName_2070_,
    );
    v___x_2075_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_2074_);
    if crate::leanh::lean_obj_tag(v___x_2075_) == 0 {
        let mut v_a_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: u8 = 0;
        let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2076_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
        crate::leanh::lean_inc(v_a_2076_);
        crate::leanh::lean_dec_ref_known(v___x_2075_, 1);
        v___x_2077_ = 1;
        v___x_2078_ = l_Lean_findDocString_x3f(v_env_2066_, v_scriptName_2070_, v___x_2077_);
        if crate::leanh::lean_obj_tag(v___x_2078_) == 0 {
            let mut v_a_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2079_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
            crate::leanh::lean_inc(v_a_2079_);
            crate::leanh::lean_dec_ref_known(v___x_2078_, 1);
            v___x_2080_ = l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0;
            v___x_2081_ = lean_string_append(v___x_2069_, v___x_2080_);
            v___x_2082_ = lean_string_append(v___x_2081_, v___x_2073_);
            crate::leanh::lean_dec_ref(v___x_2073_);
            v___x_2083_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2083_, 0, v___x_2082_);
            crate::leanh::lean_ctor_set(v___x_2083_, 1, v_a_2076_);
            crate::leanh::lean_ctor_set(v___x_2083_, 2, v_a_2079_);
            v___x_2084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
            crate::leanh::lean_ctor_set(v___x_2084_, 1, v___y_2071_);
            return v___x_2084_;
        } else {
            let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2087_: u8 = 0;
            let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_2076_);
            crate::leanh::lean_dec_ref(v___x_2073_);
            crate::leanh::lean_dec_ref(v___x_2069_);
            v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
            crate::leanh::lean_inc(v_a_2085_);
            crate::leanh::lean_dec_ref_known(v___x_2078_, 1);
            v___x_2086_ = lean_io_error_to_string(v_a_2085_);
            v___x_2087_ = 3;
            v___x_2088_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2086_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_2088_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_2087_,
            );
            v___x_2089_ = lean_array_get_size(v___y_2071_);
            v___x_2090_ = lean_array_push(v___y_2071_, v___x_2088_);
            v___x_2091_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2091_, 0, v___x_2089_);
            crate::leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
            return v___x_2091_;
        }
    } else {
        let mut v_a_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: u8 = 0;
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2073_);
        crate::leanh::lean_dec(v_scriptName_2070_);
        crate::leanh::lean_dec_ref(v___x_2069_);
        crate::leanh::lean_dec_ref(v_env_2066_);
        v_a_2092_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
        crate::leanh::lean_inc(v_a_2092_);
        crate::leanh::lean_dec_ref_known(v___x_2075_, 1);
        v___x_2093_ = lean_io_error_to_string(v_a_2092_);
        v___x_2094_ = 3;
        v___x_2095_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2093_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_2095_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_2094_,
        );
        v___x_2096_ = lean_array_get_size(v___y_2071_);
        v___x_2097_ = lean_array_push(v___y_2071_, v___x_2095_);
        v___x_2098_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2098_, 0, v___x_2096_);
        crate::leanh::lean_ctor_set(v___x_2098_, 1, v___x_2097_);
        return v___x_2098_;
    }
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(
    mut v___x_2099_: *mut crate::leanh::LeanObject,
    mut v_env_2100_: *mut crate::leanh::LeanObject,
    mut v_opts_2101_: *mut crate::leanh::LeanObject,
    mut v___x_2102_: *mut crate::leanh::LeanObject,
    mut v___x_2103_: *mut crate::leanh::LeanObject,
    mut v_scriptName_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_50967__boxed_2107_: u8 = 0;
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_50967__boxed_2107_ = (crate::leanh::lean_unbox(v___x_2099_) as u8);
    v_res_2108_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(
        v___x_50967__boxed_2107_,
        v_env_2100_,
        v_opts_2101_,
        v___x_2102_,
        v___x_2103_,
        v_scriptName_2104_,
        v___y_2105_,
    );
    crate::leanh::lean_dec_ref(v_opts_2101_);
    return v_res_2108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(
    mut v_env_2111_: *mut crate::leanh::LeanObject,
    mut v_opts_2112_: *mut crate::leanh::LeanObject,
    mut v___x_2113_: *mut crate::leanh::LeanObject,
    mut v_sz_2114_: usize,
    mut v_i_2115_: usize,
    mut v_bs_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: usize = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2123_ = lean_usize_dec_lt(v_i_2115_, v_sz_2114_);
                if v___x_2123_ == 0 {
                    crate::leanh::lean_dec(v___x_2113_);
                    crate::leanh::lean_dec_ref(v_env_2111_);
                    v___x_2124_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2124_, 0, v_bs_2116_);
                    crate::leanh::lean_ctor_set(v___x_2124_, 1, v___y_2117_);
                    return v___x_2124_;
                } else {
                    v___x_2125_ =
                        l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
                    v_v_2126_ = lean_array_uget_borrowed(v_bs_2116_, v_i_2115_);
                    crate::leanh::lean_inc(v_v_2126_);
                    crate::leanh::lean_inc_ref(v_env_2111_);
                    v___x_2127_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2111_,
                            v_opts_2112_,
                            v___x_2125_,
                            v_v_2126_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2127_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_2116_);
                        crate::leanh::lean_dec(v___x_2113_);
                        crate::leanh::lean_dec_ref(v_env_2111_);
                        v_a_2128_ = crate::leanh::lean_ctor_get(v___x_2127_, 0);
                        crate::leanh::lean_inc(v_a_2128_);
                        crate::leanh::lean_dec_ref_known(v___x_2127_, 1);
                        v___x_2129_ = 3;
                        v___x_2130_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2130_, 0, v_a_2128_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2130_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2129_,
                        );
                        v___x_2131_ = lean_array_get_size(v___y_2117_);
                        v___x_2132_ = lean_array_push(v___y_2117_, v___x_2130_);
                        v_a_2120_ = v___x_2131_;
                        v_a_2121_ = v___x_2132_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2133_ = crate::leanh::lean_ctor_get(v___x_2127_, 0);
                        crate::leanh::lean_inc(v_a_2133_);
                        crate::leanh::lean_dec_ref_known(v___x_2127_, 1);
                        v_pkg_2134_ = crate::leanh::lean_ctor_get(v_a_2133_, 0);
                        crate::leanh::lean_inc(v_pkg_2134_);
                        v_fn_2135_ = crate::leanh::lean_ctor_get(v_a_2133_, 1);
                        crate::leanh::lean_inc_ref(v_fn_2135_);
                        crate::leanh::lean_dec(v_a_2133_);
                        v___x_2136_ = lean_name_eq(v_pkg_2134_, v___x_2113_);
                        if v___x_2136_ == 0 {
                            crate::leanh::lean_dec_ref(v_fn_2135_);
                            crate::leanh::lean_dec_ref(v_bs_2116_);
                            crate::leanh::lean_dec_ref(v_env_2111_);
                            v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0;
                            v___x_2138_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_pkg_2134_,
                                    v___x_2123_,
                                );
                            v___x_2139_ = lean_string_append(v___x_2137_, v___x_2138_);
                            crate::leanh::lean_dec_ref(v___x_2138_);
                            v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1;
                            v___x_2141_ = lean_string_append(v___x_2139_, v___x_2140_);
                            v___x_2142_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2113_,
                                    v___x_2123_,
                                );
                            v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
                            crate::leanh::lean_dec_ref(v___x_2142_);
                            v___x_2144_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                            v___x_2145_ = lean_string_append(v___x_2143_, v___x_2144_);
                            v___x_2146_ = 3;
                            v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2147_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_2146_,
                            );
                            v___x_2148_ = lean_array_get_size(v___y_2117_);
                            v___x_2149_ = lean_array_push(v___y_2117_, v___x_2147_);
                            v_a_2120_ = v___x_2148_;
                            v_a_2121_ = v___x_2149_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_pkg_2134_);
                            v___x_2150_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_bs_x27_2151_ = lean_array_uset(v_bs_2116_, v_i_2115_, v___x_2150_);
                            v___x_2152_ = 1usize;
                            v___x_2153_ = lean_usize_add(v_i_2115_, v___x_2152_);
                            v___x_2154_ = lean_array_uset(v_bs_x27_2151_, v_i_2115_, v_fn_2135_);
                            v_i_2115_ = v___x_2153_;
                            v_bs_2116_ = v___x_2154_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2122_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2122_, 0, v_a_2120_);
                crate::leanh::lean_ctor_set(v___x_2122_, 1, v_a_2121_);
                return v___x_2122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(
    mut v_env_2156_: *mut crate::leanh::LeanObject,
    mut v_opts_2157_: *mut crate::leanh::LeanObject,
    mut v___x_2158_: *mut crate::leanh::LeanObject,
    mut v_sz_2159_: *mut crate::leanh::LeanObject,
    mut v_i_2160_: *mut crate::leanh::LeanObject,
    mut v_bs_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2164_: usize = 0;
    let mut v_i_boxed_2165_: usize = 0;
    let mut v_res_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2164_ = crate::leanh::lean_unbox_usize(v_sz_2159_);
    crate::leanh::lean_dec(v_sz_2159_);
    v_i_boxed_2165_ = crate::leanh::lean_unbox_usize(v_i_2160_);
    crate::leanh::lean_dec(v_i_2160_);
    v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_2156_, v_opts_2157_, v___x_2158_, v_sz_boxed_2164_, v_i_boxed_2165_, v_bs_2161_, v___y_2162_);
    crate::leanh::lean_dec_ref(v_opts_2157_);
    return v_res_2166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(
    mut v___x_2170_: *mut crate::leanh::LeanObject,
    mut v_sz_2171_: usize,
    mut v_i_2172_: usize,
    mut v_bs_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2176_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
                if v___x_2176_ == 0 {
                    crate::leanh::lean_dec(v___x_2170_);
                    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2177_, 0, v_bs_2173_);
                    crate::leanh::lean_ctor_set(v___x_2177_, 1, v___y_2174_);
                    return v___x_2177_;
                } else {
                    v_v_2178_ = lean_array_uget(v_bs_2173_, v_i_2172_);
                    v_pkg_2179_ = crate::leanh::lean_ctor_get(v_v_2178_, 0);
                    v_name_2180_ = crate::leanh::lean_ctor_get(v_v_2178_, 1);
                    v___x_2181_ = lean_name_eq(v_pkg_2179_, v___x_2170_);
                    if v___x_2181_ == 0 {
                        crate::leanh::lean_inc(v_name_2180_);
                        crate::leanh::lean_inc(v_pkg_2179_);
                        crate::leanh::lean_dec(v_v_2178_);
                        crate::leanh::lean_dec_ref(v_bs_2173_);
                        v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0;
                        v___x_2183_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_2180_,
                                v___x_2176_,
                            );
                        v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
                        crate::leanh::lean_dec_ref(v___x_2183_);
                        v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1;
                        v___x_2186_ = lean_string_append(v___x_2184_, v___x_2185_);
                        v___x_2187_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_pkg_2179_,
                                v___x_2176_,
                            );
                        v___x_2188_ = lean_string_append(v___x_2186_, v___x_2187_);
                        crate::leanh::lean_dec_ref(v___x_2187_);
                        v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2;
                        v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
                        v___x_2191_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2170_,
                                v___x_2176_,
                            );
                        v___x_2192_ = lean_string_append(v___x_2190_, v___x_2191_);
                        crate::leanh::lean_dec_ref(v___x_2191_);
                        v___x_2193_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                        v___x_2194_ = lean_string_append(v___x_2192_, v___x_2193_);
                        v___x_2195_ = 3;
                        v___x_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2194_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2196_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2195_,
                        );
                        v___x_2197_ = lean_array_get_size(v___y_2174_);
                        v___x_2198_ = lean_array_push(v___y_2174_, v___x_2196_);
                        v___x_2199_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                        crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                        return v___x_2199_;
                    } else {
                        v___x_2200_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2201_ = lean_array_uset(v_bs_2173_, v_i_2172_, v___x_2200_);
                        v___x_2202_ = 1usize;
                        v___x_2203_ = lean_usize_add(v_i_2172_, v___x_2202_);
                        v___x_2204_ = lean_array_uset(v_bs_x27_2201_, v_i_2172_, v_v_2178_);
                        v_i_2172_ = v___x_2203_;
                        v_bs_2173_ = v___x_2204_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___boxed(
    mut v___x_2206_: *mut crate::leanh::LeanObject,
    mut v_sz_2207_: *mut crate::leanh::LeanObject,
    mut v_i_2208_: *mut crate::leanh::LeanObject,
    mut v_bs_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2212_: usize = 0;
    let mut v_i_boxed_2213_: usize = 0;
    let mut v_res_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2212_ = crate::leanh::lean_unbox_usize(v_sz_2207_);
    crate::leanh::lean_dec(v_sz_2207_);
    v_i_boxed_2213_ = crate::leanh::lean_unbox_usize(v_i_2208_);
    crate::leanh::lean_dec(v_i_2208_);
    v_res_2214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v___x_2206_, v_sz_boxed_2212_, v_i_boxed_2213_, v_bs_2209_, v___y_2210_);
    return v_res_2214_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(
    mut v_t_2215_: *mut crate::leanh::LeanObject,
    mut v_k_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2215_) == 0 {
                    v_k_2217_ = crate::leanh::lean_ctor_get(v_t_2215_, 1);
                    v_v_2218_ = crate::leanh::lean_ctor_get(v_t_2215_, 2);
                    v_l_2219_ = crate::leanh::lean_ctor_get(v_t_2215_, 3);
                    v_r_2220_ = crate::leanh::lean_ctor_get(v_t_2215_, 4);
                    v___x_2221_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2216_, v_k_2217_);
                    match v___x_2221_ {
                        0 => {
                            v_t_2215_ = v_l_2219_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2218_);
                            v___x_2223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2223_, 0, v_v_2218_);
                            return v___x_2223_;
                        }
                        _ => {
                            v_t_2215_ = v_r_2220_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2225_ = crate::leanh::lean_box(0);
                    return v___x_2225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(
    mut v_t_2226_: *mut crate::leanh::LeanObject,
    mut v_k_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_2226_, v_k_2227_);
    crate::leanh::lean_dec(v_k_2227_);
    crate::leanh::lean_dec(v_t_2226_);
    return v_res_2228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(
    mut v_a_2231_: *mut crate::leanh::LeanObject,
    mut v___x_2232_: *mut crate::leanh::LeanObject,
    mut v_sz_2233_: usize,
    mut v_i_2234_: usize,
    mut v_bs_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: usize = 0;
    let mut v___x_2248_: usize = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v_unused_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = lean_usize_dec_lt(v_i_2234_, v_sz_2233_);
                if v___x_2238_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2232_);
                    crate::leanh::lean_dec_ref(v_a_2231_);
                    v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2239_, 0, v_bs_2235_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 1, v___y_2236_);
                    return v___x_2239_;
                } else {
                    v_toTreeMap_2240_ = crate::leanh::lean_ctor_get(v_a_2231_, 0);
                    v_v_2241_ = lean_array_uget_borrowed(v_bs_2235_, v_i_2234_);
                    v___x_2242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2240_, v_v_2241_);
                    if crate::leanh::lean_obj_tag(v___x_2242_) == 1 {
                        v_val_2243_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                        crate::leanh::lean_inc(v_val_2243_);
                        crate::leanh::lean_dec_ref_known(v___x_2242_, 1);
                        v_name_2244_ = crate::leanh::lean_ctor_get(v_val_2243_, 1);
                        crate::leanh::lean_inc(v_name_2244_);
                        crate::leanh::lean_dec(v_val_2243_);
                        v___x_2245_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2246_ = lean_array_uset(v_bs_2235_, v_i_2234_, v___x_2245_);
                        v___x_2247_ = 1usize;
                        v___x_2248_ = lean_usize_add(v_i_2234_, v___x_2247_);
                        v___x_2249_ = lean_array_uset(v_bs_x27_2246_, v_i_2234_, v_name_2244_);
                        v_i_2234_ = v___x_2248_;
                        v_bs_2235_ = v___x_2249_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_2241_);
                        crate::leanh::lean_dec(v___x_2242_);
                        crate::leanh::lean_dec_ref(v_bs_2235_);
                        v_isSharedCheck_2267_ = (!crate::leanh::lean_is_exclusive(v_a_2231_)) as u8;
                        if v_isSharedCheck_2267_ == 0 {
                            v_unused_2268_ = crate::leanh::lean_ctor_get(v_a_2231_, 1);
                            crate::leanh::lean_dec(v_unused_2268_);
                            v_unused_2269_ = crate::leanh::lean_ctor_get(v_a_2231_, 0);
                            crate::leanh::lean_dec(v_unused_2269_);
                            v___x_2252_ = v_a_2231_;
                            v_isShared_2253_ = v_isSharedCheck_2267_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2231_);
                            v___x_2252_ = crate::leanh::lean_box(0);
                            v_isShared_2253_ = v_isSharedCheck_2267_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0;
                v___x_2255_ = lean_string_append(v___x_2232_, v___x_2254_);
                v___x_2256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_v_2241_,
                    v___x_2238_,
                );
                v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
                crate::leanh::lean_dec_ref(v___x_2256_);
                v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1;
                v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
                v___x_2260_ = 3;
                v___x_2261_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2259_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2261_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2260_,
                );
                v___x_2262_ = lean_array_get_size(v___y_2236_);
                v___x_2263_ = lean_array_push(v___y_2236_, v___x_2261_);
                if v_isShared_2253_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2252_, 1);
                    crate::leanh::lean_ctor_set(v___x_2252_, 1, v___x_2263_);
                    crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2262_);
                    v___x_2265_ = v___x_2252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2266_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2263_);
                    v___x_2265_ = v_reuseFailAlloc_2266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v___x_2271_: *mut crate::leanh::LeanObject,
    mut v_sz_2272_: *mut crate::leanh::LeanObject,
    mut v_i_2273_: *mut crate::leanh::LeanObject,
    mut v_bs_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2277_: usize = 0;
    let mut v_i_boxed_2278_: usize = 0;
    let mut v_res_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2277_ = crate::leanh::lean_unbox_usize(v_sz_2272_);
    crate::leanh::lean_dec(v_sz_2272_);
    v_i_boxed_2278_ = crate::leanh::lean_unbox_usize(v_i_2273_);
    crate::leanh::lean_dec(v_i_2273_);
    v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_2270_, v___x_2271_, v_sz_boxed_2277_, v_i_boxed_2278_, v_bs_2274_, v___y_2275_);
    return v_res_2279_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(
    mut v_f_2280_: *mut crate::leanh::LeanObject,
    mut v_as_2281_: *mut crate::leanh::LeanObject,
    mut v_i_2282_: usize,
    mut v_stop_2283_: usize,
    mut v_b_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: usize = 0;
    let mut v___x_2300_: usize = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2285_ = lean_usize_dec_eq(v_i_2282_, v_stop_2283_);
                if v___x_2285_ == 0 {
                    v___x_2286_ = lean_array_uget_borrowed(v_as_2281_, v_i_2282_);
                    crate::leanh::lean_inc_ref(v_f_2280_);
                    crate::leanh::lean_inc(v___x_2286_);
                    v___x_2287_ = crate::leanh::lean_apply_1(v_f_2280_, v___x_2286_);
                    if crate::leanh::lean_obj_tag(v___x_2287_) == 0 {
                        crate::leanh::lean_dec_ref(v_b_2284_);
                        crate::leanh::lean_dec_ref(v_f_2280_);
                        v_a_2288_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                        v_isSharedCheck_2295_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2287_)) as u8;
                        if v_isSharedCheck_2295_ == 0 {
                            v___x_2290_ = v___x_2287_;
                            v_isShared_2291_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2288_);
                            crate::leanh::lean_dec(v___x_2287_);
                            v___x_2290_ = crate::leanh::lean_box(0);
                            v_isShared_2291_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2296_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                        crate::leanh::lean_inc(v_a_2296_);
                        crate::leanh::lean_dec_ref_known(v___x_2287_, 1);
                        v___x_2297_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
                        crate::leanh::lean_inc(v___x_2286_);
                        v___x_2298_ = l_Lake_RBArray_insert___redArg(
                            v___x_2297_,
                            v_b_2284_,
                            v___x_2286_,
                            v_a_2296_,
                        );
                        v___x_2299_ = 1usize;
                        v___x_2300_ = lean_usize_add(v_i_2282_, v___x_2299_);
                        v_i_2282_ = v___x_2300_;
                        v_b_2284_ = v___x_2298_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2280_);
                    v___x_2302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2302_, 0, v_b_2284_);
                    return v___x_2302_;
                }
            }
            1 => {
                if v_isShared_2291_ == 0 {
                    v___x_2293_ = v___x_2290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
                    v___x_2293_ = v_reuseFailAlloc_2294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg___boxed(
    mut v_f_2303_: *mut crate::leanh::LeanObject,
    mut v_as_2304_: *mut crate::leanh::LeanObject,
    mut v_i_2305_: *mut crate::leanh::LeanObject,
    mut v_stop_2306_: *mut crate::leanh::LeanObject,
    mut v_b_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2308_: usize = 0;
    let mut v_stop_boxed_2309_: usize = 0;
    let mut v_res_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2308_ = crate::leanh::lean_unbox_usize(v_i_2305_);
    crate::leanh::lean_dec(v_i_2305_);
    v_stop_boxed_2309_ = crate::leanh::lean_unbox_usize(v_stop_2306_);
    crate::leanh::lean_dec(v_stop_2306_);
    v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2303_, v_as_2304_, v_i_boxed_2308_, v_stop_boxed_2309_, v_b_2307_);
    crate::leanh::lean_dec_ref(v_as_2304_);
    return v_res_2310_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(
    mut v_env_2311_: *mut crate::leanh::LeanObject,
    mut v_attr_2312_: *mut crate::leanh::LeanObject,
    mut v_f_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    v_entries_2314_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_2312_, v_env_2311_);
    v___x_2315_ = lean_array_get_size(v_entries_2314_);
    v___x_2316_ = l_Lake_RBArray_mkEmpty___redArg(v___x_2315_);
    v___x_2317_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2318_ = lean_nat_dec_lt(v___x_2317_, v___x_2315_);
    if v___x_2318_ == 0 {
        let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_entries_2314_);
        crate::leanh::lean_dec_ref(v_f_2313_);
        v___x_2319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2319_, 0, v___x_2316_);
        return v___x_2319_;
    } else {
        let mut v___x_2320_: u8 = 0;
        v___x_2320_ = lean_nat_dec_le(v___x_2315_, v___x_2315_);
        if v___x_2320_ == 0 {
            if v___x_2318_ == 0 {
                let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_entries_2314_);
                crate::leanh::lean_dec_ref(v_f_2313_);
                v___x_2321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2321_, 0, v___x_2316_);
                return v___x_2321_;
            } else {
                let mut v___x_2322_: usize = 0;
                let mut v___x_2323_: usize = 0;
                let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2322_ = 0usize;
                v___x_2323_ = lean_usize_of_nat(v___x_2315_);
                v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2313_, v_entries_2314_, v___x_2322_, v___x_2323_, v___x_2316_);
                crate::leanh::lean_dec_ref(v_entries_2314_);
                return v___x_2324_;
            }
        } else {
            let mut v___x_2325_: usize = 0;
            let mut v___x_2326_: usize = 0;
            let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2325_ = 0usize;
            v___x_2326_ = lean_usize_of_nat(v___x_2315_);
            v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2313_, v_entries_2314_, v___x_2325_, v___x_2326_, v___x_2316_);
            crate::leanh::lean_dec_ref(v_entries_2314_);
            return v___x_2327_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(
    mut v_env_2328_: *mut crate::leanh::LeanObject,
    mut v_attr_2329_: *mut crate::leanh::LeanObject,
    mut v_f_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_2328_, v_attr_2329_, v_f_2330_);
    crate::leanh::lean_dec_ref(v_attr_2329_);
    return v_res_2331_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(
    mut v_f_2332_: *mut crate::leanh::LeanObject,
    mut v_as_2333_: *mut crate::leanh::LeanObject,
    mut v_i_2334_: usize,
    mut v_stop_2335_: usize,
    mut v_b_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: usize = 0;
    let mut v___x_2346_: usize = 0;
    let mut v_a_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2339_ = lean_usize_dec_eq(v_i_2334_, v_stop_2335_);
                if v___x_2339_ == 0 {
                    v___x_2340_ = lean_array_uget_borrowed(v_as_2333_, v_i_2334_);
                    crate::leanh::lean_inc_ref(v_f_2332_);
                    crate::leanh::lean_inc(v___x_2340_);
                    v___x_2341_ = crate::leanh::lean_apply_3(
                        v_f_2332_,
                        v___x_2340_,
                        v___y_2337_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2341_) == 0 {
                        v_a_2342_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                        crate::leanh::lean_inc(v_a_2342_);
                        v_a_2343_ = crate::leanh::lean_ctor_get(v___x_2341_, 1);
                        crate::leanh::lean_inc(v_a_2343_);
                        crate::leanh::lean_dec_ref_known(v___x_2341_, 2);
                        crate::leanh::lean_inc(v___x_2340_);
                        v___x_2344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2340_, v_a_2342_, v_b_2336_);
                        v___x_2345_ = 1usize;
                        v___x_2346_ = lean_usize_add(v_i_2334_, v___x_2345_);
                        v_i_2334_ = v___x_2346_;
                        v_b_2336_ = v___x_2344_;
                        v___y_2337_ = v_a_2343_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_2336_);
                        crate::leanh::lean_dec_ref(v_f_2332_);
                        v_a_2348_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                        v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2341_, 1);
                        v_isSharedCheck_2356_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                        if v_isSharedCheck_2356_ == 0 {
                            v___x_2351_ = v___x_2341_;
                            v_isShared_2352_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2349_);
                            crate::leanh::lean_inc(v_a_2348_);
                            crate::leanh::lean_dec(v___x_2341_);
                            v___x_2351_ = crate::leanh::lean_box(0);
                            v_isShared_2352_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2332_);
                    v___x_2357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2357_, 0, v_b_2336_);
                    crate::leanh::lean_ctor_set(v___x_2357_, 1, v___y_2337_);
                    return v___x_2357_;
                }
            }
            1 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2355_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(
    mut v_f_2358_: *mut crate::leanh::LeanObject,
    mut v_as_2359_: *mut crate::leanh::LeanObject,
    mut v_i_2360_: *mut crate::leanh::LeanObject,
    mut v_stop_2361_: *mut crate::leanh::LeanObject,
    mut v_b_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2365_: usize = 0;
    let mut v_stop_boxed_2366_: usize = 0;
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2365_ = crate::leanh::lean_unbox_usize(v_i_2360_);
    crate::leanh::lean_dec(v_i_2360_);
    v_stop_boxed_2366_ = crate::leanh::lean_unbox_usize(v_stop_2361_);
    crate::leanh::lean_dec(v_stop_2361_);
    v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2358_, v_as_2359_, v_i_boxed_2365_, v_stop_boxed_2366_, v_b_2362_, v___y_2363_);
    crate::leanh::lean_dec_ref(v_as_2359_);
    return v_res_2367_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(
    mut v_env_2368_: *mut crate::leanh::LeanObject,
    mut v_attr_2369_: *mut crate::leanh::LeanObject,
    mut v_f_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    v_entries_2373_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_2369_, v_env_2368_);
    v___x_2374_ = crate::leanh::lean_box(1);
    v___x_2375_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2376_ = lean_array_get_size(v_entries_2373_);
    v___x_2377_ = lean_nat_dec_lt(v___x_2375_, v___x_2376_);
    if v___x_2377_ == 0 {
        let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_entries_2373_);
        crate::leanh::lean_dec_ref(v_f_2370_);
        v___x_2378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2378_, 0, v___x_2374_);
        crate::leanh::lean_ctor_set(v___x_2378_, 1, v___y_2371_);
        return v___x_2378_;
    } else {
        let mut v___x_2379_: u8 = 0;
        v___x_2379_ = lean_nat_dec_le(v___x_2376_, v___x_2376_);
        if v___x_2379_ == 0 {
            if v___x_2377_ == 0 {
                let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_entries_2373_);
                crate::leanh::lean_dec_ref(v_f_2370_);
                v___x_2380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2380_, 0, v___x_2374_);
                crate::leanh::lean_ctor_set(v___x_2380_, 1, v___y_2371_);
                return v___x_2380_;
            } else {
                let mut v___x_2381_: usize = 0;
                let mut v___x_2382_: usize = 0;
                let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2381_ = 0usize;
                v___x_2382_ = lean_usize_of_nat(v___x_2376_);
                v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2370_, v_entries_2373_, v___x_2381_, v___x_2382_, v___x_2374_, v___y_2371_);
                crate::leanh::lean_dec_ref(v_entries_2373_);
                return v___x_2383_;
            }
        } else {
            let mut v___x_2384_: usize = 0;
            let mut v___x_2385_: usize = 0;
            let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2384_ = 0usize;
            v___x_2385_ = lean_usize_of_nat(v___x_2376_);
            v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2370_, v_entries_2373_, v___x_2384_, v___x_2385_, v___x_2374_, v___y_2371_);
            crate::leanh::lean_dec_ref(v_entries_2373_);
            return v___x_2386_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(
    mut v_env_2387_: *mut crate::leanh::LeanObject,
    mut v_attr_2388_: *mut crate::leanh::LeanObject,
    mut v_f_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2392_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_2387_, v_attr_2388_, v_f_2389_, v___y_2390_);
    crate::leanh::lean_dec_ref(v_attr_2388_);
    return v_res_2392_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(
    mut v_env_2393_: *mut crate::leanh::LeanObject,
    mut v_opts_2394_: *mut crate::leanh::LeanObject,
    mut v_as_2395_: *mut crate::leanh::LeanObject,
    mut v_sz_2396_: usize,
    mut v_i_2397_: usize,
    mut v_b_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_a_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: usize = 0;
    let mut v___x_2422_: usize = 0;
    let mut v_reuseFailAlloc_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = lean_usize_dec_lt(v_i_2397_, v_sz_2396_);
                if v___x_2399_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_2393_);
                    v___x_2400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2400_, 0, v_b_2398_);
                    return v___x_2400_;
                } else {
                    v___x_2401_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
                    v_a_2402_ = lean_array_uget_borrowed(v_as_2395_, v_i_2397_);
                    crate::leanh::lean_inc(v_a_2402_);
                    crate::leanh::lean_inc_ref(v_env_2393_);
                    v___x_2403_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2393_,
                            v_opts_2394_,
                            v___x_2401_,
                            v_a_2402_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2403_) == 0 {
                        crate::leanh::lean_dec_ref(v_b_2398_);
                        crate::leanh::lean_dec_ref(v_env_2393_);
                        v_a_2404_ = crate::leanh::lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2411_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2406_ = v___x_2403_;
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2404_);
                            crate::leanh::lean_dec(v___x_2403_);
                            v___x_2406_ = crate::leanh::lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2412_ = crate::leanh::lean_ctor_get(v___x_2403_, 0);
                        crate::leanh::lean_inc(v_a_2412_);
                        crate::leanh::lean_dec_ref_known(v___x_2403_, 1);
                        v_name_2413_ = crate::leanh::lean_ctor_get(v_a_2412_, 0);
                        v_config_2414_ = crate::leanh::lean_ctor_get(v_a_2412_, 1);
                        v_isSharedCheck_2425_ = (!crate::leanh::lean_is_exclusive(v_a_2412_)) as u8;
                        if v_isSharedCheck_2425_ == 0 {
                            v___x_2416_ = v_a_2412_;
                            v_isShared_2417_ = v_isSharedCheck_2425_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_config_2414_);
                            crate::leanh::lean_inc(v_name_2413_);
                            crate::leanh::lean_dec(v_a_2412_);
                            v___x_2416_ = crate::leanh::lean_box(0);
                            v_isShared_2417_ = v_isSharedCheck_2425_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2407_ == 0 {
                    v___x_2409_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2409_;
            }
            3 => {
                if v_isShared_2417_ == 0 {
                    v___x_2419_ = v___x_2416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_name_2413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_config_2414_);
                    v___x_2419_ = v_reuseFailAlloc_2424_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2420_ = lean_array_push(v_b_2398_, v___x_2419_);
                v___x_2421_ = 1usize;
                v___x_2422_ = lean_usize_add(v_i_2397_, v___x_2421_);
                v_i_2397_ = v___x_2422_;
                v_b_2398_ = v___x_2420_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12___boxed(
    mut v_env_2426_: *mut crate::leanh::LeanObject,
    mut v_opts_2427_: *mut crate::leanh::LeanObject,
    mut v_as_2428_: *mut crate::leanh::LeanObject,
    mut v_sz_2429_: *mut crate::leanh::LeanObject,
    mut v_i_2430_: *mut crate::leanh::LeanObject,
    mut v_b_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2432_: usize = 0;
    let mut v_i_boxed_2433_: usize = 0;
    let mut v_res_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2432_ = crate::leanh::lean_unbox_usize(v_sz_2429_);
    crate::leanh::lean_dec(v_sz_2429_);
    v_i_boxed_2433_ = crate::leanh::lean_unbox_usize(v_i_2430_);
    crate::leanh::lean_dec(v_i_2430_);
    v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_2426_, v_opts_2427_, v_as_2428_, v_sz_boxed_2432_, v_i_boxed_2433_, v_b_2431_);
    crate::leanh::lean_dec_ref(v_as_2428_);
    crate::leanh::lean_dec_ref(v_opts_2427_);
    return v_res_2434_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(
    mut v___x_2438_: *mut crate::leanh::LeanObject,
    mut v_as_2439_: *mut crate::leanh::LeanObject,
    mut v_i_2440_: usize,
    mut v_stop_2441_: usize,
    mut v_b_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: usize = 0;
    let mut v___x_2449_: usize = 0;
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v_root_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2451_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
                if v___x_2451_ == 0 {
                    v___x_2452_ = lean_array_uget_borrowed(v_as_2439_, v_i_2440_);
                    v_name_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 1);
                    v_kind_2454_ = crate::leanh::lean_ctor_get(v___x_2452_, 2);
                    v_config_2455_ = crate::leanh::lean_ctor_get(v___x_2452_, 3);
                    v___x_2456_ = l_Lake_LeanExe_keyword;
                    v___x_2457_ = lean_name_eq(v_kind_2454_, v___x_2456_);
                    if v___x_2457_ == 0 {
                        v_a_2446_ = v_b_2442_;
                        v_a_2447_ = v___y_2443_;
                        state = 1;
                        continue;
                    } else {
                        v_root_2458_ = crate::leanh::lean_ctor_get(v_config_2455_, 2);
                        v___x_2459_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_2442_, v_root_2458_);
                        if crate::leanh::lean_obj_tag(v___x_2459_) == 1 {
                            crate::leanh::lean_dec(v_b_2442_);
                            v_val_2460_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                            crate::leanh::lean_inc(v_val_2460_);
                            crate::leanh::lean_dec_ref_known(v___x_2459_, 1);
                            v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0;
                            v___x_2462_ = lean_string_append(v___x_2438_, v___x_2461_);
                            crate::leanh::lean_inc(v_name_2453_);
                            v___x_2463_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_name_2453_,
                                    v___x_2457_,
                                );
                            v___x_2464_ = lean_string_append(v___x_2462_, v___x_2463_);
                            crate::leanh::lean_dec_ref(v___x_2463_);
                            v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1;
                            v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
                            crate::leanh::lean_inc(v_root_2458_);
                            v___x_2467_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_root_2458_,
                                    v___x_2457_,
                                );
                            v___x_2468_ = lean_string_append(v___x_2466_, v___x_2467_);
                            crate::leanh::lean_dec_ref(v___x_2467_);
                            v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2;
                            v___x_2470_ = lean_string_append(v___x_2468_, v___x_2469_);
                            v___x_2471_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_val_2460_,
                                    v___x_2457_,
                                );
                            v___x_2472_ = lean_string_append(v___x_2470_, v___x_2471_);
                            crate::leanh::lean_dec_ref(v___x_2471_);
                            v___x_2473_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                            v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
                            v___x_2475_ = 3;
                            v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2474_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2476_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_2475_,
                            );
                            v___x_2477_ = lean_array_get_size(v___y_2443_);
                            v___x_2478_ = lean_array_push(v___y_2443_, v___x_2476_);
                            v___x_2479_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2479_, 0, v___x_2477_);
                            crate::leanh::lean_ctor_set(v___x_2479_, 1, v___x_2478_);
                            return v___x_2479_;
                        } else {
                            crate::leanh::lean_dec(v___x_2459_);
                            crate::leanh::lean_inc(v_name_2453_);
                            crate::leanh::lean_inc(v_root_2458_);
                            v___x_2480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_2458_, v_name_2453_, v_b_2442_);
                            v_a_2446_ = v___x_2480_;
                            v_a_2447_ = v___y_2443_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2438_);
                    v___x_2481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2481_, 0, v_b_2442_);
                    crate::leanh::lean_ctor_set(v___x_2481_, 1, v___y_2443_);
                    return v___x_2481_;
                }
            }
            1 => {
                v___x_2448_ = 1usize;
                v___x_2449_ = lean_usize_add(v_i_2440_, v___x_2448_);
                v_i_2440_ = v___x_2449_;
                v_b_2442_ = v_a_2446_;
                v___y_2443_ = v_a_2447_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(
    mut v___x_2482_: *mut crate::leanh::LeanObject,
    mut v_as_2483_: *mut crate::leanh::LeanObject,
    mut v_i_2484_: *mut crate::leanh::LeanObject,
    mut v_stop_2485_: *mut crate::leanh::LeanObject,
    mut v_b_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2489_: usize = 0;
    let mut v_stop_boxed_2490_: usize = 0;
    let mut v_res_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2489_ = crate::leanh::lean_unbox_usize(v_i_2484_);
    crate::leanh::lean_dec(v_i_2484_);
    v_stop_boxed_2490_ = crate::leanh::lean_unbox_usize(v_stop_2485_);
    crate::leanh::lean_dec(v_stop_2485_);
    v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_2482_, v_as_2483_, v_i_boxed_2489_, v_stop_boxed_2490_, v_b_2486_, v___y_2487_);
    crate::leanh::lean_dec_ref(v_as_2483_);
    return v_res_2491_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v___x_2496_: *mut crate::leanh::LeanObject,
    mut v_sz_2497_: usize,
    mut v_i_2498_: usize,
    mut v_bs_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: usize = 0;
    let mut v___x_2512_: usize = 0;
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_unused_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2502_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
                if v___x_2502_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2496_);
                    crate::leanh::lean_dec_ref(v_a_2494_);
                    v___x_2503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2503_, 0, v_bs_2499_);
                    crate::leanh::lean_ctor_set(v___x_2503_, 1, v___y_2500_);
                    return v___x_2503_;
                } else {
                    v_toTreeMap_2504_ = crate::leanh::lean_ctor_get(v_a_2494_, 0);
                    v_v_2505_ = lean_array_uget(v_bs_2499_, v_i_2498_);
                    v___x_2506_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2507_ = lean_array_uset(v_bs_2499_, v_i_2498_, v___x_2506_);
                    v___x_2515_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2504_, v_v_2505_);
                    if crate::leanh::lean_obj_tag(v___x_2515_) == 1 {
                        crate::leanh::lean_dec(v_v_2505_);
                        v_val_2516_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                        crate::leanh::lean_inc(v_val_2516_);
                        crate::leanh::lean_dec_ref_known(v___x_2515_, 1);
                        v_name_2517_ = crate::leanh::lean_ctor_get(v_val_2516_, 1);
                        crate::leanh::lean_inc(v_name_2517_);
                        crate::leanh::lean_dec(v_val_2516_);
                        v_a_2509_ = v_name_2517_;
                        v_a_2510_ = v___y_2500_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2515_);
                        v___x_2518_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_2505_, v_a_2495_);
                        if v___x_2518_ == 0 {
                            crate::leanh::lean_dec_ref(v_bs_x27_2507_);
                            v_isSharedCheck_2535_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2494_)) as u8;
                            if v_isSharedCheck_2535_ == 0 {
                                v_unused_2536_ = crate::leanh::lean_ctor_get(v_a_2494_, 1);
                                crate::leanh::lean_dec(v_unused_2536_);
                                v_unused_2537_ = crate::leanh::lean_ctor_get(v_a_2494_, 0);
                                crate::leanh::lean_dec(v_unused_2537_);
                                v___x_2520_ = v_a_2494_;
                                v_isShared_2521_ = v_isSharedCheck_2535_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_2494_);
                                v___x_2520_ = crate::leanh::lean_box(0);
                                v_isShared_2521_ = v_isSharedCheck_2535_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2509_ = v_v_2505_;
                            v_a_2510_ = v___y_2500_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2511_ = 1usize;
                v___x_2512_ = lean_usize_add(v_i_2498_, v___x_2511_);
                v___x_2513_ = lean_array_uset(v_bs_x27_2507_, v_i_2498_, v_a_2509_);
                v_i_2498_ = v___x_2512_;
                v_bs_2499_ = v___x_2513_;
                v___y_2500_ = v_a_2510_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0;
                v___x_2523_ = lean_string_append(v___x_2496_, v___x_2522_);
                v___x_2524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_v_2505_,
                    v___x_2502_,
                );
                v___x_2525_ = lean_string_append(v___x_2523_, v___x_2524_);
                crate::leanh::lean_dec_ref(v___x_2524_);
                v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1;
                v___x_2527_ = lean_string_append(v___x_2525_, v___x_2526_);
                v___x_2528_ = 3;
                v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2527_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2529_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2528_,
                );
                v___x_2530_ = lean_array_get_size(v___y_2500_);
                v___x_2531_ = lean_array_push(v___y_2500_, v___x_2529_);
                if v_isShared_2521_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2520_, 1);
                    crate::leanh::lean_ctor_set(v___x_2520_, 1, v___x_2531_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2530_);
                    v___x_2533_ = v___x_2520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2531_);
                    v___x_2533_ = v_reuseFailAlloc_2534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___boxed(
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_a_2539_: *mut crate::leanh::LeanObject,
    mut v___x_2540_: *mut crate::leanh::LeanObject,
    mut v_sz_2541_: *mut crate::leanh::LeanObject,
    mut v_i_2542_: *mut crate::leanh::LeanObject,
    mut v_bs_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2546_: usize = 0;
    let mut v_i_boxed_2547_: usize = 0;
    let mut v_res_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2546_ = crate::leanh::lean_unbox_usize(v_sz_2541_);
    crate::leanh::lean_dec(v_sz_2541_);
    v_i_boxed_2547_ = crate::leanh::lean_unbox_usize(v_i_2542_);
    crate::leanh::lean_dec(v_i_2542_);
    v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_2538_, v_a_2539_, v___x_2540_, v_sz_boxed_2546_, v_i_boxed_2547_, v_bs_2543_, v___y_2544_);
    crate::leanh::lean_dec(v_a_2539_);
    return v_res_2548_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(
    mut v_a_2550_: *mut crate::leanh::LeanObject,
    mut v_a_2551_: *mut crate::leanh::LeanObject,
    mut v___x_2552_: *mut crate::leanh::LeanObject,
    mut v_sz_2553_: usize,
    mut v_i_2554_: usize,
    mut v_bs_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: usize = 0;
    let mut v___x_2568_: usize = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_unused_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2558_ = lean_usize_dec_lt(v_i_2554_, v_sz_2553_);
                if v___x_2558_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2552_);
                    crate::leanh::lean_dec_ref(v_a_2550_);
                    v___x_2559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2559_, 0, v_bs_2555_);
                    crate::leanh::lean_ctor_set(v___x_2559_, 1, v___y_2556_);
                    return v___x_2559_;
                } else {
                    v_toTreeMap_2560_ = crate::leanh::lean_ctor_get(v_a_2550_, 0);
                    v_v_2561_ = lean_array_uget(v_bs_2555_, v_i_2554_);
                    v___x_2562_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2563_ = lean_array_uset(v_bs_2555_, v_i_2554_, v___x_2562_);
                    v___x_2571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2560_, v_v_2561_);
                    if crate::leanh::lean_obj_tag(v___x_2571_) == 1 {
                        crate::leanh::lean_dec(v_v_2561_);
                        v_val_2572_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
                        crate::leanh::lean_inc(v_val_2572_);
                        crate::leanh::lean_dec_ref_known(v___x_2571_, 1);
                        v_name_2573_ = crate::leanh::lean_ctor_get(v_val_2572_, 1);
                        crate::leanh::lean_inc(v_name_2573_);
                        crate::leanh::lean_dec(v_val_2572_);
                        v_a_2565_ = v_name_2573_;
                        v_a_2566_ = v___y_2556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2571_);
                        v___x_2574_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_2561_, v_a_2551_);
                        if v___x_2574_ == 0 {
                            crate::leanh::lean_dec_ref(v_bs_x27_2563_);
                            v_isSharedCheck_2591_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2550_)) as u8;
                            if v_isSharedCheck_2591_ == 0 {
                                v_unused_2592_ = crate::leanh::lean_ctor_get(v_a_2550_, 1);
                                crate::leanh::lean_dec(v_unused_2592_);
                                v_unused_2593_ = crate::leanh::lean_ctor_get(v_a_2550_, 0);
                                crate::leanh::lean_dec(v_unused_2593_);
                                v___x_2576_ = v_a_2550_;
                                v_isShared_2577_ = v_isSharedCheck_2591_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_2550_);
                                v___x_2576_ = crate::leanh::lean_box(0);
                                v_isShared_2577_ = v_isSharedCheck_2591_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2565_ = v_v_2561_;
                            v_a_2566_ = v___y_2556_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2567_ = 1usize;
                v___x_2568_ = lean_usize_add(v_i_2554_, v___x_2567_);
                v___x_2569_ = lean_array_uset(v_bs_x27_2563_, v_i_2554_, v_a_2565_);
                v_i_2554_ = v___x_2568_;
                v_bs_2555_ = v___x_2569_;
                v___y_2556_ = v_a_2566_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0;
                v___x_2579_ = lean_string_append(v___x_2552_, v___x_2578_);
                v___x_2580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_v_2561_,
                    v___x_2558_,
                );
                v___x_2581_ = lean_string_append(v___x_2579_, v___x_2580_);
                crate::leanh::lean_dec_ref(v___x_2580_);
                v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0;
                v___x_2583_ = lean_string_append(v___x_2581_, v___x_2582_);
                v___x_2584_ = 3;
                v___x_2585_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2585_, 0, v___x_2583_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2585_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2584_,
                );
                v___x_2586_ = lean_array_get_size(v___y_2556_);
                v___x_2587_ = lean_array_push(v___y_2556_, v___x_2585_);
                if v_isShared_2577_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2576_, 1);
                    crate::leanh::lean_ctor_set(v___x_2576_, 1, v___x_2587_);
                    crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2586_);
                    v___x_2589_ = v___x_2576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
    mut v___x_2596_: *mut crate::leanh::LeanObject,
    mut v_sz_2597_: *mut crate::leanh::LeanObject,
    mut v_i_2598_: *mut crate::leanh::LeanObject,
    mut v_bs_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2602_: usize = 0;
    let mut v_i_boxed_2603_: usize = 0;
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2602_ = crate::leanh::lean_unbox_usize(v_sz_2597_);
    crate::leanh::lean_dec(v_sz_2597_);
    v_i_boxed_2603_ = crate::leanh::lean_unbox_usize(v_i_2598_);
    crate::leanh::lean_dec(v_i_2598_);
    v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_2594_, v_a_2595_, v___x_2596_, v_sz_boxed_2602_, v_i_boxed_2603_, v_bs_2599_, v___y_2600_);
    crate::leanh::lean_dec(v_a_2595_);
    return v_res_2604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v___x_2607_: *mut crate::leanh::LeanObject,
    mut v_sz_2608_: usize,
    mut v_i_2609_: usize,
    mut v_bs_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2613_ = lean_usize_dec_lt(v_i_2609_, v_sz_2608_);
                if v___x_2613_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2607_);
                    v___x_2614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v_bs_2610_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v___y_2611_);
                    return v___x_2614_;
                } else {
                    v_v_2615_ = lean_array_uget_borrowed(v_bs_2610_, v_i_2609_);
                    v___x_2616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_2606_, v_v_2615_);
                    if crate::leanh::lean_obj_tag(v___x_2616_) == 1 {
                        v_val_2617_ = crate::leanh::lean_ctor_get(v___x_2616_, 0);
                        crate::leanh::lean_inc(v_val_2617_);
                        crate::leanh::lean_dec_ref_known(v___x_2616_, 1);
                        v___x_2618_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2619_ = lean_array_uset(v_bs_2610_, v_i_2609_, v___x_2618_);
                        v___x_2620_ = 1usize;
                        v___x_2621_ = lean_usize_add(v_i_2609_, v___x_2620_);
                        v___x_2622_ = lean_array_uset(v_bs_x27_2619_, v_i_2609_, v_val_2617_);
                        v_i_2609_ = v___x_2621_;
                        v_bs_2610_ = v___x_2622_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_2615_);
                        crate::leanh::lean_dec(v___x_2616_);
                        crate::leanh::lean_dec_ref(v_bs_2610_);
                        v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0;
                        v___x_2625_ = lean_string_append(v___x_2607_, v___x_2624_);
                        v___x_2626_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_v_2615_,
                                v___x_2613_,
                            );
                        v___x_2627_ = lean_string_append(v___x_2625_, v___x_2626_);
                        crate::leanh::lean_dec_ref(v___x_2626_);
                        v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1;
                        v___x_2629_ = lean_string_append(v___x_2627_, v___x_2628_);
                        v___x_2630_ = 3;
                        v___x_2631_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2631_, 0, v___x_2629_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2631_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2630_,
                        );
                        v___x_2632_ = lean_array_get_size(v___y_2611_);
                        v___x_2633_ = lean_array_push(v___y_2611_, v___x_2631_);
                        v___x_2634_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2632_);
                        crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                        return v___x_2634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v___x_2636_: *mut crate::leanh::LeanObject,
    mut v_sz_2637_: *mut crate::leanh::LeanObject,
    mut v_i_2638_: *mut crate::leanh::LeanObject,
    mut v_bs_2639_: *mut crate::leanh::LeanObject,
    mut v___y_2640_: *mut crate::leanh::LeanObject,
    mut v___y_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2642_: usize = 0;
    let mut v_i_boxed_2643_: usize = 0;
    let mut v_res_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2642_ = crate::leanh::lean_unbox_usize(v_sz_2637_);
    crate::leanh::lean_dec(v_sz_2637_);
    v_i_boxed_2643_ = crate::leanh::lean_unbox_usize(v_i_2638_);
    crate::leanh::lean_dec(v_i_2638_);
    v_res_2644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_2635_, v___x_2636_, v_sz_boxed_2642_, v_i_boxed_2643_, v_bs_2639_, v___y_2640_);
    crate::leanh::lean_dec(v_a_2635_);
    return v_res_2644_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(
    mut v_env_2645_: *mut crate::leanh::LeanObject,
    mut v_opts_2646_: *mut crate::leanh::LeanObject,
    mut v_sz_2647_: usize,
    mut v_i_2648_: usize,
    mut v_bs_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_a_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: usize = 0;
    let mut v___x_2667_: usize = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2650_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
                if v___x_2650_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_2645_);
                    v___x_2651_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2651_, 0, v_bs_2649_);
                    return v___x_2651_;
                } else {
                    v___x_2652_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
                    v_v_2653_ = lean_array_uget_borrowed(v_bs_2649_, v_i_2648_);
                    crate::leanh::lean_inc(v_v_2653_);
                    crate::leanh::lean_inc_ref(v_env_2645_);
                    v___x_2654_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2645_,
                            v_opts_2646_,
                            v___x_2652_,
                            v_v_2653_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2654_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_2649_);
                        crate::leanh::lean_dec_ref(v_env_2645_);
                        v_a_2655_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2662_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2662_ == 0 {
                            v___x_2657_ = v___x_2654_;
                            v_isShared_2658_ = v_isSharedCheck_2662_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2655_);
                            crate::leanh::lean_dec(v___x_2654_);
                            v___x_2657_ = crate::leanh::lean_box(0);
                            v_isShared_2658_ = v_isSharedCheck_2662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2663_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
                        crate::leanh::lean_inc(v_a_2663_);
                        crate::leanh::lean_dec_ref_known(v___x_2654_, 1);
                        v___x_2664_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2665_ = lean_array_uset(v_bs_2649_, v_i_2648_, v___x_2664_);
                        v___x_2666_ = 1usize;
                        v___x_2667_ = lean_usize_add(v_i_2648_, v___x_2666_);
                        v___x_2668_ = lean_array_uset(v_bs_x27_2665_, v_i_2648_, v_a_2663_);
                        v_i_2648_ = v___x_2667_;
                        v_bs_2649_ = v___x_2668_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2658_ == 0 {
                    v___x_2660_ = v___x_2657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
                    v___x_2660_ = v_reuseFailAlloc_2661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(
    mut v_env_2670_: *mut crate::leanh::LeanObject,
    mut v_opts_2671_: *mut crate::leanh::LeanObject,
    mut v_sz_2672_: *mut crate::leanh::LeanObject,
    mut v_i_2673_: *mut crate::leanh::LeanObject,
    mut v_bs_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2675_: usize = 0;
    let mut v_i_boxed_2676_: usize = 0;
    let mut v_res_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2675_ = crate::leanh::lean_unbox_usize(v_sz_2672_);
    crate::leanh::lean_dec(v_sz_2672_);
    v_i_boxed_2676_ = crate::leanh::lean_unbox_usize(v_i_2673_);
    crate::leanh::lean_dec(v_i_2673_);
    v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_2670_, v_opts_2671_, v_sz_boxed_2675_, v_i_boxed_2676_, v_bs_2674_);
    crate::leanh::lean_dec_ref(v_opts_2671_);
    return v_res_2677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(
    mut v_env_2678_: *mut crate::leanh::LeanObject,
    mut v_opts_2679_: *mut crate::leanh::LeanObject,
    mut v_as_2680_: *mut crate::leanh::LeanObject,
    mut v_sz_2681_: usize,
    mut v_i_2682_: usize,
    mut v_b_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_a_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: usize = 0;
    let mut v_reuseFailAlloc_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
                if v___x_2684_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_2678_);
                    v___x_2685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2685_, 0, v_b_2683_);
                    return v___x_2685_;
                } else {
                    v___x_2686_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
                    v_a_2687_ = lean_array_uget_borrowed(v_as_2680_, v_i_2682_);
                    crate::leanh::lean_inc(v_a_2687_);
                    crate::leanh::lean_inc_ref(v_env_2678_);
                    v___x_2688_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2678_,
                            v_opts_2679_,
                            v___x_2686_,
                            v_a_2687_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2688_) == 0 {
                        crate::leanh::lean_dec_ref(v_b_2683_);
                        crate::leanh::lean_dec_ref(v_env_2678_);
                        v_a_2689_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                        v_isSharedCheck_2696_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2688_)) as u8;
                        if v_isSharedCheck_2696_ == 0 {
                            v___x_2691_ = v___x_2688_;
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2689_);
                            crate::leanh::lean_dec(v___x_2688_);
                            v___x_2691_ = crate::leanh::lean_box(0);
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2697_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                        crate::leanh::lean_inc(v_a_2697_);
                        crate::leanh::lean_dec_ref_known(v___x_2688_, 1);
                        v_name_2698_ = crate::leanh::lean_ctor_get(v_a_2697_, 0);
                        v_config_2699_ = crate::leanh::lean_ctor_get(v_a_2697_, 1);
                        v_isSharedCheck_2710_ = (!crate::leanh::lean_is_exclusive(v_a_2697_)) as u8;
                        if v_isSharedCheck_2710_ == 0 {
                            v___x_2701_ = v_a_2697_;
                            v_isShared_2702_ = v_isSharedCheck_2710_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_config_2699_);
                            crate::leanh::lean_inc(v_name_2698_);
                            crate::leanh::lean_dec(v_a_2697_);
                            v___x_2701_ = crate::leanh::lean_box(0);
                            v_isShared_2702_ = v_isSharedCheck_2710_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2692_ == 0 {
                    v___x_2694_ = v___x_2691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
                    v___x_2694_ = v_reuseFailAlloc_2695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2694_;
            }
            3 => {
                if v_isShared_2702_ == 0 {
                    v___x_2704_ = v___x_2701_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_name_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_config_2699_);
                    v___x_2704_ = v_reuseFailAlloc_2709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2705_ = lean_array_push(v_b_2683_, v___x_2704_);
                v___x_2706_ = 1usize;
                v___x_2707_ = lean_usize_add(v_i_2682_, v___x_2706_);
                v_i_2682_ = v___x_2707_;
                v_b_2683_ = v___x_2705_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(
    mut v_env_2711_: *mut crate::leanh::LeanObject,
    mut v_opts_2712_: *mut crate::leanh::LeanObject,
    mut v_as_2713_: *mut crate::leanh::LeanObject,
    mut v_sz_2714_: *mut crate::leanh::LeanObject,
    mut v_i_2715_: *mut crate::leanh::LeanObject,
    mut v_b_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2717_: usize = 0;
    let mut v_i_boxed_2718_: usize = 0;
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2717_ = crate::leanh::lean_unbox_usize(v_sz_2714_);
    crate::leanh::lean_dec(v_sz_2714_);
    v_i_boxed_2718_ = crate::leanh::lean_unbox_usize(v_i_2715_);
    crate::leanh::lean_dec(v_i_2715_);
    v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_2711_, v_opts_2712_, v_as_2713_, v_sz_boxed_2717_, v_i_boxed_2718_, v_b_2716_);
    crate::leanh::lean_dec_ref(v_as_2713_);
    crate::leanh::lean_dec_ref(v_opts_2712_);
    return v_res_2719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(
    mut v_env_2720_: *mut crate::leanh::LeanObject,
    mut v_opts_2721_: *mut crate::leanh::LeanObject,
    mut v_as_2722_: *mut crate::leanh::LeanObject,
    mut v_sz_2723_: usize,
    mut v_i_2724_: usize,
    mut v_b_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: usize = 0;
    let mut v___x_2749_: usize = 0;
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2726_ = lean_usize_dec_lt(v_i_2724_, v_sz_2723_);
                if v___x_2726_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_2720_);
                    v___x_2727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2727_, 0, v_b_2725_);
                    return v___x_2727_;
                } else {
                    v___x_2728_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
                    v_a_2729_ = lean_array_uget_borrowed(v_as_2722_, v_i_2724_);
                    crate::leanh::lean_inc(v_a_2729_);
                    crate::leanh::lean_inc_ref(v_env_2720_);
                    v___x_2730_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2720_,
                            v_opts_2721_,
                            v___x_2728_,
                            v_a_2729_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2730_) == 0 {
                        crate::leanh::lean_dec_ref(v_b_2725_);
                        crate::leanh::lean_dec_ref(v_env_2720_);
                        v_a_2731_ = crate::leanh::lean_ctor_get(v___x_2730_, 0);
                        v_isSharedCheck_2738_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2730_)) as u8;
                        if v_isSharedCheck_2738_ == 0 {
                            v___x_2733_ = v___x_2730_;
                            v_isShared_2734_ = v_isSharedCheck_2738_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2731_);
                            crate::leanh::lean_dec(v___x_2730_);
                            v___x_2733_ = crate::leanh::lean_box(0);
                            v_isShared_2734_ = v_isSharedCheck_2738_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2739_ = crate::leanh::lean_ctor_get(v___x_2730_, 0);
                        crate::leanh::lean_inc(v_a_2739_);
                        crate::leanh::lean_dec_ref_known(v___x_2730_, 1);
                        v_name_2740_ = crate::leanh::lean_ctor_get(v_a_2739_, 0);
                        v_config_2741_ = crate::leanh::lean_ctor_get(v_a_2739_, 1);
                        v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v_a_2739_)) as u8;
                        if v_isSharedCheck_2752_ == 0 {
                            v___x_2743_ = v_a_2739_;
                            v_isShared_2744_ = v_isSharedCheck_2752_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_config_2741_);
                            crate::leanh::lean_inc(v_name_2740_);
                            crate::leanh::lean_dec(v_a_2739_);
                            v___x_2743_ = crate::leanh::lean_box(0);
                            v_isShared_2744_ = v_isSharedCheck_2752_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2734_ == 0 {
                    v___x_2736_ = v___x_2733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
                    v___x_2736_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2736_;
            }
            3 => {
                if v_isShared_2744_ == 0 {
                    v___x_2746_ = v___x_2743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_name_2740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_config_2741_);
                    v___x_2746_ = v_reuseFailAlloc_2751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2747_ = lean_array_push(v_b_2725_, v___x_2746_);
                v___x_2748_ = 1usize;
                v___x_2749_ = lean_usize_add(v_i_2724_, v___x_2748_);
                v_i_2724_ = v___x_2749_;
                v_b_2725_ = v___x_2747_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(
    mut v_env_2753_: *mut crate::leanh::LeanObject,
    mut v_opts_2754_: *mut crate::leanh::LeanObject,
    mut v_as_2755_: *mut crate::leanh::LeanObject,
    mut v_sz_2756_: *mut crate::leanh::LeanObject,
    mut v_i_2757_: *mut crate::leanh::LeanObject,
    mut v_b_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2759_: usize = 0;
    let mut v_i_boxed_2760_: usize = 0;
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2759_ = crate::leanh::lean_unbox_usize(v_sz_2756_);
    crate::leanh::lean_dec(v_sz_2756_);
    v_i_boxed_2760_ = crate::leanh::lean_unbox_usize(v_i_2757_);
    crate::leanh::lean_dec(v_i_2757_);
    v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_2753_, v_opts_2754_, v_as_2755_, v_sz_boxed_2759_, v_i_boxed_2760_, v_b_2758_);
    crate::leanh::lean_dec_ref(v_as_2755_);
    crate::leanh::lean_dec_ref(v_opts_2754_);
    return v_res_2761_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(
    mut v_t_2762_: *mut crate::leanh::LeanObject,
    mut v_k_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2762_) == 0 {
                    v_k_2764_ = crate::leanh::lean_ctor_get(v_t_2762_, 1);
                    v_v_2765_ = crate::leanh::lean_ctor_get(v_t_2762_, 2);
                    v_l_2766_ = crate::leanh::lean_ctor_get(v_t_2762_, 3);
                    v_r_2767_ = crate::leanh::lean_ctor_get(v_t_2762_, 4);
                    v___x_2768_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2763_, v_k_2764_);
                    match v___x_2768_ {
                        0 => {
                            v_t_2762_ = v_l_2766_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2765_);
                            v___x_2770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2770_, 0, v_v_2765_);
                            return v___x_2770_;
                        }
                        _ => {
                            v_t_2762_ = v_r_2767_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2772_ = crate::leanh::lean_box(0);
                    return v___x_2772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(
    mut v_t_2773_: *mut crate::leanh::LeanObject,
    mut v_k_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_2773_, v_k_2774_);
    crate::leanh::lean_dec(v_k_2774_);
    crate::leanh::lean_dec(v_t_2773_);
    return v_res_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(
    mut v_k_2776_: *mut crate::leanh::LeanObject,
    mut v_v_2777_: *mut crate::leanh::LeanObject,
    mut v_t_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2787_: u8 = 0;
    let mut v_impl_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v_size_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_unused_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_unused_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2889_: u8 = 0;
    let mut v_unused_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v_k_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_unused_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_unused_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v_size_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v_unused_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut v_unused_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_unused_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v_k_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_unused_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_unused_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2778_) == 0 {
                    v_size_2779_ = crate::leanh::lean_ctor_get(v_t_2778_, 0);
                    v_k_2780_ = crate::leanh::lean_ctor_get(v_t_2778_, 1);
                    v_v_2781_ = crate::leanh::lean_ctor_get(v_t_2778_, 2);
                    v_l_2782_ = crate::leanh::lean_ctor_get(v_t_2778_, 3);
                    v_r_2783_ = crate::leanh::lean_ctor_get(v_t_2778_, 4);
                    v_isSharedCheck_3063_ = (!crate::leanh::lean_is_exclusive(v_t_2778_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_2785_ = v_t_2778_;
                        v_isShared_2786_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2783_);
                        crate::leanh::lean_inc(v_l_2782_);
                        crate::leanh::lean_inc(v_v_2781_);
                        crate::leanh::lean_inc(v_k_2780_);
                        crate::leanh::lean_inc(v_size_2779_);
                        crate::leanh::lean_dec(v_t_2778_);
                        v___x_2785_ = crate::leanh::lean_box(0);
                        v_isShared_2786_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3064_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3065_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3064_);
                    crate::leanh::lean_ctor_set(v___x_3065_, 1, v_k_2776_);
                    crate::leanh::lean_ctor_set(v___x_3065_, 2, v_v_2777_);
                    crate::leanh::lean_ctor_set(v___x_3065_, 3, v_t_2778_);
                    crate::leanh::lean_ctor_set(v___x_3065_, 4, v_t_2778_);
                    return v___x_3065_;
                }
            }
            1 => {
                v___x_2787_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2776_, v_k_2780_);
                match v___x_2787_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2779_);
                        v_impl_2788_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_2776_, v_v_2777_, v_l_2782_);
                        v___x_2789_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_2783_) == 0 {
                            v_size_2790_ = crate::leanh::lean_ctor_get(v_r_2783_, 0);
                            v_size_2791_ = crate::leanh::lean_ctor_get(v_impl_2788_, 0);
                            crate::leanh::lean_inc(v_size_2791_);
                            v_k_2792_ = crate::leanh::lean_ctor_get(v_impl_2788_, 1);
                            crate::leanh::lean_inc(v_k_2792_);
                            v_v_2793_ = crate::leanh::lean_ctor_get(v_impl_2788_, 2);
                            crate::leanh::lean_inc(v_v_2793_);
                            v_l_2794_ = crate::leanh::lean_ctor_get(v_impl_2788_, 3);
                            crate::leanh::lean_inc(v_l_2794_);
                            v_r_2795_ = crate::leanh::lean_ctor_get(v_impl_2788_, 4);
                            crate::leanh::lean_inc(v_r_2795_);
                            v___x_2796_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2797_ = lean_nat_mul(v___x_2796_, v_size_2790_);
                            v___x_2798_ = lean_nat_dec_lt(v___x_2797_, v_size_2791_);
                            crate::leanh::lean_dec(v___x_2797_);
                            if v___x_2798_ == 0 {
                                crate::leanh::lean_dec(v_r_2795_);
                                crate::leanh::lean_dec(v_l_2794_);
                                crate::leanh::lean_dec(v_v_2793_);
                                crate::leanh::lean_dec(v_k_2792_);
                                v___x_2799_ = lean_nat_add(v___x_2789_, v_size_2791_);
                                crate::leanh::lean_dec(v_size_2791_);
                                v___x_2800_ = lean_nat_add(v___x_2799_, v_size_2790_);
                                crate::leanh::lean_dec(v___x_2799_);
                                if v_isShared_2786_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v_impl_2788_);
                                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2800_);
                                    v___x_2802_ = v___x_2785_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2803_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2803_,
                                        0,
                                        v___x_2800_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2803_,
                                        1,
                                        v_k_2780_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2803_,
                                        2,
                                        v_v_2781_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2803_,
                                        3,
                                        v_impl_2788_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2803_,
                                        4,
                                        v_r_2783_,
                                    );
                                    v___x_2802_ = v_reuseFailAlloc_2803_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2869_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2788_)) as u8;
                                if v_isSharedCheck_2869_ == 0 {
                                    v_unused_2870_ = crate::leanh::lean_ctor_get(v_impl_2788_, 4);
                                    crate::leanh::lean_dec(v_unused_2870_);
                                    v_unused_2871_ = crate::leanh::lean_ctor_get(v_impl_2788_, 3);
                                    crate::leanh::lean_dec(v_unused_2871_);
                                    v_unused_2872_ = crate::leanh::lean_ctor_get(v_impl_2788_, 2);
                                    crate::leanh::lean_dec(v_unused_2872_);
                                    v_unused_2873_ = crate::leanh::lean_ctor_get(v_impl_2788_, 1);
                                    crate::leanh::lean_dec(v_unused_2873_);
                                    v_unused_2874_ = crate::leanh::lean_ctor_get(v_impl_2788_, 0);
                                    crate::leanh::lean_dec(v_unused_2874_);
                                    v___x_2805_ = v_impl_2788_;
                                    v_isShared_2806_ = v_isSharedCheck_2869_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2788_);
                                    v___x_2805_ = crate::leanh::lean_box(0);
                                    v_isShared_2806_ = v_isSharedCheck_2869_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2875_ = crate::leanh::lean_ctor_get(v_impl_2788_, 3);
                            crate::leanh::lean_inc(v_l_2875_);
                            if crate::leanh::lean_obj_tag(v_l_2875_) == 0 {
                                v_r_2876_ = crate::leanh::lean_ctor_get(v_impl_2788_, 4);
                                v_k_2877_ = crate::leanh::lean_ctor_get(v_impl_2788_, 1);
                                v_v_2878_ = crate::leanh::lean_ctor_get(v_impl_2788_, 2);
                                v_isSharedCheck_2889_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2788_)) as u8;
                                if v_isSharedCheck_2889_ == 0 {
                                    v_unused_2890_ = crate::leanh::lean_ctor_get(v_impl_2788_, 3);
                                    crate::leanh::lean_dec(v_unused_2890_);
                                    v_unused_2891_ = crate::leanh::lean_ctor_get(v_impl_2788_, 0);
                                    crate::leanh::lean_dec(v_unused_2891_);
                                    v___x_2880_ = v_impl_2788_;
                                    v_isShared_2881_ = v_isSharedCheck_2889_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2876_);
                                    crate::leanh::lean_inc(v_v_2878_);
                                    crate::leanh::lean_inc(v_k_2877_);
                                    crate::leanh::lean_dec(v_impl_2788_);
                                    v___x_2880_ = crate::leanh::lean_box(0);
                                    v_isShared_2881_ = v_isSharedCheck_2889_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2892_ = crate::leanh::lean_ctor_get(v_impl_2788_, 4);
                                crate::leanh::lean_inc(v_r_2892_);
                                if crate::leanh::lean_obj_tag(v_r_2892_) == 0 {
                                    v_k_2893_ = crate::leanh::lean_ctor_get(v_impl_2788_, 1);
                                    v_v_2894_ = crate::leanh::lean_ctor_get(v_impl_2788_, 2);
                                    v_isSharedCheck_2917_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2788_)) as u8;
                                    if v_isSharedCheck_2917_ == 0 {
                                        v_unused_2918_ =
                                            crate::leanh::lean_ctor_get(v_impl_2788_, 4);
                                        crate::leanh::lean_dec(v_unused_2918_);
                                        v_unused_2919_ =
                                            crate::leanh::lean_ctor_get(v_impl_2788_, 3);
                                        crate::leanh::lean_dec(v_unused_2919_);
                                        v_unused_2920_ =
                                            crate::leanh::lean_ctor_get(v_impl_2788_, 0);
                                        crate::leanh::lean_dec(v_unused_2920_);
                                        v___x_2896_ = v_impl_2788_;
                                        v_isShared_2897_ = v_isSharedCheck_2917_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2894_);
                                        crate::leanh::lean_inc(v_k_2893_);
                                        crate::leanh::lean_dec(v_impl_2788_);
                                        v___x_2896_ = crate::leanh::lean_box(0);
                                        v_isShared_2897_ = v_isSharedCheck_2917_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2921_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2786_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2785_, 4, v_r_2892_);
                                        crate::leanh::lean_ctor_set(v___x_2785_, 3, v_impl_2788_);
                                        crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2921_);
                                        v___x_2923_ = v___x_2785_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2924_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2924_,
                                            0,
                                            v___x_2921_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2924_,
                                            1,
                                            v_k_2780_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2924_,
                                            2,
                                            v_v_2781_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2924_,
                                            3,
                                            v_impl_2788_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2924_,
                                            4,
                                            v_r_2892_,
                                        );
                                        v___x_2923_ = v_reuseFailAlloc_2924_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2781_);
                        crate::leanh::lean_dec(v_k_2780_);
                        if v_isShared_2786_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_2777_);
                            crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_2776_);
                            v___x_2926_ = v___x_2785_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2927_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_size_2779_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2776_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2777_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_l_2782_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_r_2783_);
                            v___x_2926_ = v_reuseFailAlloc_2927_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2779_);
                        v_impl_2928_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_2776_, v_v_2777_, v_r_2783_);
                        v___x_2929_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_2782_) == 0 {
                            v_size_2930_ = crate::leanh::lean_ctor_get(v_l_2782_, 0);
                            v_size_2931_ = crate::leanh::lean_ctor_get(v_impl_2928_, 0);
                            crate::leanh::lean_inc(v_size_2931_);
                            v_k_2932_ = crate::leanh::lean_ctor_get(v_impl_2928_, 1);
                            crate::leanh::lean_inc(v_k_2932_);
                            v_v_2933_ = crate::leanh::lean_ctor_get(v_impl_2928_, 2);
                            crate::leanh::lean_inc(v_v_2933_);
                            v_l_2934_ = crate::leanh::lean_ctor_get(v_impl_2928_, 3);
                            crate::leanh::lean_inc(v_l_2934_);
                            v_r_2935_ = crate::leanh::lean_ctor_get(v_impl_2928_, 4);
                            crate::leanh::lean_inc(v_r_2935_);
                            v___x_2936_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2937_ = lean_nat_mul(v___x_2936_, v_size_2930_);
                            v___x_2938_ = lean_nat_dec_lt(v___x_2937_, v_size_2931_);
                            crate::leanh::lean_dec(v___x_2937_);
                            if v___x_2938_ == 0 {
                                crate::leanh::lean_dec(v_r_2935_);
                                crate::leanh::lean_dec(v_l_2934_);
                                crate::leanh::lean_dec(v_v_2933_);
                                crate::leanh::lean_dec(v_k_2932_);
                                v___x_2939_ = lean_nat_add(v___x_2929_, v_size_2930_);
                                v___x_2940_ = lean_nat_add(v___x_2939_, v_size_2931_);
                                crate::leanh::lean_dec(v_size_2931_);
                                crate::leanh::lean_dec(v___x_2939_);
                                if v_isShared_2786_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v_impl_2928_);
                                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2940_);
                                    v___x_2942_ = v___x_2785_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2943_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2943_,
                                        0,
                                        v___x_2940_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2943_,
                                        1,
                                        v_k_2780_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2943_,
                                        2,
                                        v_v_2781_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2943_,
                                        3,
                                        v_l_2782_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2943_,
                                        4,
                                        v_impl_2928_,
                                    );
                                    v___x_2942_ = v_reuseFailAlloc_2943_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3007_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2928_)) as u8;
                                if v_isSharedCheck_3007_ == 0 {
                                    v_unused_3008_ = crate::leanh::lean_ctor_get(v_impl_2928_, 4);
                                    crate::leanh::lean_dec(v_unused_3008_);
                                    v_unused_3009_ = crate::leanh::lean_ctor_get(v_impl_2928_, 3);
                                    crate::leanh::lean_dec(v_unused_3009_);
                                    v_unused_3010_ = crate::leanh::lean_ctor_get(v_impl_2928_, 2);
                                    crate::leanh::lean_dec(v_unused_3010_);
                                    v_unused_3011_ = crate::leanh::lean_ctor_get(v_impl_2928_, 1);
                                    crate::leanh::lean_dec(v_unused_3011_);
                                    v_unused_3012_ = crate::leanh::lean_ctor_get(v_impl_2928_, 0);
                                    crate::leanh::lean_dec(v_unused_3012_);
                                    v___x_2945_ = v_impl_2928_;
                                    v_isShared_2946_ = v_isSharedCheck_3007_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2928_);
                                    v___x_2945_ = crate::leanh::lean_box(0);
                                    v_isShared_2946_ = v_isSharedCheck_3007_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3013_ = crate::leanh::lean_ctor_get(v_impl_2928_, 3);
                            crate::leanh::lean_inc(v_l_3013_);
                            if crate::leanh::lean_obj_tag(v_l_3013_) == 0 {
                                v_r_3014_ = crate::leanh::lean_ctor_get(v_impl_2928_, 4);
                                v_k_3015_ = crate::leanh::lean_ctor_get(v_impl_2928_, 1);
                                v_v_3016_ = crate::leanh::lean_ctor_get(v_impl_2928_, 2);
                                v_isSharedCheck_3039_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2928_)) as u8;
                                if v_isSharedCheck_3039_ == 0 {
                                    v_unused_3040_ = crate::leanh::lean_ctor_get(v_impl_2928_, 3);
                                    crate::leanh::lean_dec(v_unused_3040_);
                                    v_unused_3041_ = crate::leanh::lean_ctor_get(v_impl_2928_, 0);
                                    crate::leanh::lean_dec(v_unused_3041_);
                                    v___x_3018_ = v_impl_2928_;
                                    v_isShared_3019_ = v_isSharedCheck_3039_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3014_);
                                    crate::leanh::lean_inc(v_v_3016_);
                                    crate::leanh::lean_inc(v_k_3015_);
                                    crate::leanh::lean_dec(v_impl_2928_);
                                    v___x_3018_ = crate::leanh::lean_box(0);
                                    v_isShared_3019_ = v_isSharedCheck_3039_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3042_ = crate::leanh::lean_ctor_get(v_impl_2928_, 4);
                                crate::leanh::lean_inc(v_r_3042_);
                                if crate::leanh::lean_obj_tag(v_r_3042_) == 0 {
                                    v_k_3043_ = crate::leanh::lean_ctor_get(v_impl_2928_, 1);
                                    v_v_3044_ = crate::leanh::lean_ctor_get(v_impl_2928_, 2);
                                    v_isSharedCheck_3055_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2928_)) as u8;
                                    if v_isSharedCheck_3055_ == 0 {
                                        v_unused_3056_ =
                                            crate::leanh::lean_ctor_get(v_impl_2928_, 4);
                                        crate::leanh::lean_dec(v_unused_3056_);
                                        v_unused_3057_ =
                                            crate::leanh::lean_ctor_get(v_impl_2928_, 3);
                                        crate::leanh::lean_dec(v_unused_3057_);
                                        v_unused_3058_ =
                                            crate::leanh::lean_ctor_get(v_impl_2928_, 0);
                                        crate::leanh::lean_dec(v_unused_3058_);
                                        v___x_3046_ = v_impl_2928_;
                                        v_isShared_3047_ = v_isSharedCheck_3055_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3044_);
                                        crate::leanh::lean_inc(v_k_3043_);
                                        crate::leanh::lean_dec(v_impl_2928_);
                                        v___x_3046_ = crate::leanh::lean_box(0);
                                        v_isShared_3047_ = v_isSharedCheck_3055_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3059_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2786_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2785_, 4, v_impl_2928_);
                                        crate::leanh::lean_ctor_set(v___x_2785_, 3, v_r_3042_);
                                        crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_3059_);
                                        v___x_3061_ = v___x_2785_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3062_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3062_,
                                            0,
                                            v___x_3059_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3062_,
                                            1,
                                            v_k_2780_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3062_,
                                            2,
                                            v_v_2781_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3062_,
                                            3,
                                            v_r_3042_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3062_,
                                            4,
                                            v_impl_2928_,
                                        );
                                        v___x_3061_ = v_reuseFailAlloc_3062_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2802_;
            }
            3 => {
                v_size_2807_ = crate::leanh::lean_ctor_get(v_l_2794_, 0);
                v_size_2808_ = crate::leanh::lean_ctor_get(v_r_2795_, 0);
                v_k_2809_ = crate::leanh::lean_ctor_get(v_r_2795_, 1);
                v_v_2810_ = crate::leanh::lean_ctor_get(v_r_2795_, 2);
                v_l_2811_ = crate::leanh::lean_ctor_get(v_r_2795_, 3);
                v_r_2812_ = crate::leanh::lean_ctor_get(v_r_2795_, 4);
                v___x_2813_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2814_ = lean_nat_mul(v___x_2813_, v_size_2807_);
                v___x_2815_ = lean_nat_dec_lt(v_size_2808_, v___x_2814_);
                crate::leanh::lean_dec(v___x_2814_);
                if v___x_2815_ == 0 {
                    crate::leanh::lean_inc(v_r_2812_);
                    crate::leanh::lean_inc(v_l_2811_);
                    crate::leanh::lean_inc(v_v_2810_);
                    crate::leanh::lean_inc(v_k_2809_);
                    v_isSharedCheck_2844_ = (!crate::leanh::lean_is_exclusive(v_r_2795_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v_unused_2845_ = crate::leanh::lean_ctor_get(v_r_2795_, 4);
                        crate::leanh::lean_dec(v_unused_2845_);
                        v_unused_2846_ = crate::leanh::lean_ctor_get(v_r_2795_, 3);
                        crate::leanh::lean_dec(v_unused_2846_);
                        v_unused_2847_ = crate::leanh::lean_ctor_get(v_r_2795_, 2);
                        crate::leanh::lean_dec(v_unused_2847_);
                        v_unused_2848_ = crate::leanh::lean_ctor_get(v_r_2795_, 1);
                        crate::leanh::lean_dec(v_unused_2848_);
                        v_unused_2849_ = crate::leanh::lean_ctor_get(v_r_2795_, 0);
                        crate::leanh::lean_dec(v_unused_2849_);
                        v___x_2817_ = v_r_2795_;
                        v_isShared_2818_ = v_isSharedCheck_2844_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2795_);
                        v___x_2817_ = crate::leanh::lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2844_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2785_);
                    v___x_2850_ = lean_nat_add(v___x_2789_, v_size_2791_);
                    crate::leanh::lean_dec(v_size_2791_);
                    v___x_2851_ = lean_nat_add(v___x_2850_, v_size_2790_);
                    crate::leanh::lean_dec(v___x_2850_);
                    v___x_2852_ = lean_nat_add(v___x_2789_, v_size_2790_);
                    v___x_2853_ = lean_nat_add(v___x_2852_, v_size_2808_);
                    crate::leanh::lean_dec(v___x_2852_);
                    crate::leanh::lean_inc_ref(v_r_2783_);
                    if v_isShared_2806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2805_, 4, v_r_2783_);
                        crate::leanh::lean_ctor_set(v___x_2805_, 3, v_r_2795_);
                        crate::leanh::lean_ctor_set(v___x_2805_, 2, v_v_2781_);
                        crate::leanh::lean_ctor_set(v___x_2805_, 1, v_k_2780_);
                        crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2853_);
                        v___x_2855_ = v___x_2805_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2868_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2853_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_k_2780_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_v_2781_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_r_2795_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_r_2783_);
                        v___x_2855_ = v_reuseFailAlloc_2868_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2819_ = lean_nat_add(v___x_2789_, v_size_2791_);
                crate::leanh::lean_dec(v_size_2791_);
                v___x_2820_ = lean_nat_add(v___x_2819_, v_size_2790_);
                crate::leanh::lean_dec(v___x_2819_);
                v___x_2832_ = lean_nat_add(v___x_2789_, v_size_2807_);
                if crate::leanh::lean_obj_tag(v_l_2811_) == 0 {
                    v_size_2842_ = crate::leanh::lean_ctor_get(v_l_2811_, 0);
                    crate::leanh::lean_inc(v_size_2842_);
                    v___y_2834_ = v_size_2842_;
                    state = 8;
                    continue;
                } else {
                    v___x_2843_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2834_ = v___x_2843_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2825_ = lean_nat_add(v___y_2822_, v___y_2824_);
                crate::leanh::lean_dec(v___y_2824_);
                crate::leanh::lean_dec(v___y_2822_);
                if v_isShared_2818_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2817_, 4, v_r_2783_);
                    crate::leanh::lean_ctor_set(v___x_2817_, 3, v_r_2812_);
                    crate::leanh::lean_ctor_set(v___x_2817_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v___x_2817_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v___x_2817_, 0, v___x_2825_);
                    v___x_2827_ = v___x_2817_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_r_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_r_2783_);
                    v___x_2827_ = v_reuseFailAlloc_2831_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2805_, 4, v___x_2827_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 3, v___y_2823_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 2, v_v_2810_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 1, v_k_2809_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2820_);
                    v___x_2829_ = v___x_2805_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_k_2809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_v_2810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 3, v___y_2823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 4, v___x_2827_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2829_;
            }
            8 => {
                v___x_2835_ = lean_nat_add(v___x_2832_, v___y_2834_);
                crate::leanh::lean_dec(v___y_2834_);
                crate::leanh::lean_dec(v___x_2832_);
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v_l_2811_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v_l_2794_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_2793_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_2792_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2835_);
                    v___x_2837_ = v___x_2785_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_l_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_l_2811_);
                    v___x_2837_ = v_reuseFailAlloc_2841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2838_ = lean_nat_add(v___x_2789_, v_size_2790_);
                if crate::leanh::lean_obj_tag(v_r_2812_) == 0 {
                    v_size_2839_ = crate::leanh::lean_ctor_get(v_r_2812_, 0);
                    crate::leanh::lean_inc(v_size_2839_);
                    v___y_2822_ = v___x_2838_;
                    v___y_2823_ = v___x_2837_;
                    v___y_2824_ = v_size_2839_;
                    state = 5;
                    continue;
                } else {
                    v___x_2840_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2822_ = v___x_2838_;
                    v___y_2823_ = v___x_2837_;
                    v___y_2824_ = v___x_2840_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2862_ = (!crate::leanh::lean_is_exclusive(v_r_2783_)) as u8;
                if v_isSharedCheck_2862_ == 0 {
                    v_unused_2863_ = crate::leanh::lean_ctor_get(v_r_2783_, 4);
                    crate::leanh::lean_dec(v_unused_2863_);
                    v_unused_2864_ = crate::leanh::lean_ctor_get(v_r_2783_, 3);
                    crate::leanh::lean_dec(v_unused_2864_);
                    v_unused_2865_ = crate::leanh::lean_ctor_get(v_r_2783_, 2);
                    crate::leanh::lean_dec(v_unused_2865_);
                    v_unused_2866_ = crate::leanh::lean_ctor_get(v_r_2783_, 1);
                    crate::leanh::lean_dec(v_unused_2866_);
                    v_unused_2867_ = crate::leanh::lean_ctor_get(v_r_2783_, 0);
                    crate::leanh::lean_dec(v_unused_2867_);
                    v___x_2857_ = v_r_2783_;
                    v_isShared_2858_ = v_isSharedCheck_2862_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2783_);
                    v___x_2857_ = crate::leanh::lean_box(0);
                    v_isShared_2858_ = v_isSharedCheck_2862_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2857_, 4, v___x_2855_);
                    crate::leanh::lean_ctor_set(v___x_2857_, 3, v_l_2794_);
                    crate::leanh::lean_ctor_set(v___x_2857_, 2, v_v_2793_);
                    crate::leanh::lean_ctor_set(v___x_2857_, 1, v_k_2792_);
                    crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2851_);
                    v___x_2860_ = v___x_2857_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2861_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_l_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 4, v___x_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2861_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2860_;
            }
            13 => {
                v___x_2882_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_2876_);
                if v_isShared_2881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2880_, 3, v_r_2876_);
                    crate::leanh::lean_ctor_set(v___x_2880_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v___x_2880_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v___x_2880_, 0, v___x_2789_);
                    v___x_2884_ = v___x_2880_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2888_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_r_2876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 4, v_r_2876_);
                    v___x_2884_ = v_reuseFailAlloc_2888_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v___x_2884_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v_l_2875_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_2878_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_2877_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2882_);
                    v___x_2886_ = v___x_2785_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_l_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 4, v___x_2884_);
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2886_;
            }
            16 => {
                v_k_2898_ = crate::leanh::lean_ctor_get(v_r_2892_, 1);
                v_v_2899_ = crate::leanh::lean_ctor_get(v_r_2892_, 2);
                v_isSharedCheck_2913_ = (!crate::leanh::lean_is_exclusive(v_r_2892_)) as u8;
                if v_isSharedCheck_2913_ == 0 {
                    v_unused_2914_ = crate::leanh::lean_ctor_get(v_r_2892_, 4);
                    crate::leanh::lean_dec(v_unused_2914_);
                    v_unused_2915_ = crate::leanh::lean_ctor_get(v_r_2892_, 3);
                    crate::leanh::lean_dec(v_unused_2915_);
                    v_unused_2916_ = crate::leanh::lean_ctor_get(v_r_2892_, 0);
                    crate::leanh::lean_dec(v_unused_2916_);
                    v___x_2901_ = v_r_2892_;
                    v_isShared_2902_ = v_isSharedCheck_2913_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2899_);
                    crate::leanh::lean_inc(v_k_2898_);
                    crate::leanh::lean_dec(v_r_2892_);
                    v___x_2901_ = crate::leanh::lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2913_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2903_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2901_, 4, v_l_2875_);
                    crate::leanh::lean_ctor_set(v___x_2901_, 3, v_l_2875_);
                    crate::leanh::lean_ctor_set(v___x_2901_, 2, v_v_2894_);
                    crate::leanh::lean_ctor_set(v___x_2901_, 1, v_k_2893_);
                    crate::leanh::lean_ctor_set(v___x_2901_, 0, v___x_2789_);
                    v___x_2905_ = v___x_2901_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_l_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_l_2875_);
                    v___x_2905_ = v_reuseFailAlloc_2912_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2896_, 4, v_l_2875_);
                    crate::leanh::lean_ctor_set(v___x_2896_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v___x_2896_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v___x_2896_, 0, v___x_2789_);
                    v___x_2907_ = v___x_2896_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 3, v_l_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_l_2875_);
                    v___x_2907_ = v_reuseFailAlloc_2911_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v___x_2907_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v___x_2905_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_2899_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_2898_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2903_);
                    v___x_2909_ = v___x_2785_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_k_2898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_v_2899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 3, v___x_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 4, v___x_2907_);
                    v___x_2909_ = v_reuseFailAlloc_2910_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2909_;
            }
            21 => {
                return v___x_2923_;
            }
            22 => {
                return v___x_2926_;
            }
            23 => {
                return v___x_2942_;
            }
            24 => {
                v_size_2947_ = crate::leanh::lean_ctor_get(v_l_2934_, 0);
                v_k_2948_ = crate::leanh::lean_ctor_get(v_l_2934_, 1);
                v_v_2949_ = crate::leanh::lean_ctor_get(v_l_2934_, 2);
                v_l_2950_ = crate::leanh::lean_ctor_get(v_l_2934_, 3);
                v_r_2951_ = crate::leanh::lean_ctor_get(v_l_2934_, 4);
                v_size_2952_ = crate::leanh::lean_ctor_get(v_r_2935_, 0);
                v___x_2953_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2954_ = lean_nat_mul(v___x_2953_, v_size_2952_);
                v___x_2955_ = lean_nat_dec_lt(v_size_2947_, v___x_2954_);
                crate::leanh::lean_dec(v___x_2954_);
                if v___x_2955_ == 0 {
                    crate::leanh::lean_inc(v_r_2951_);
                    crate::leanh::lean_inc(v_l_2950_);
                    crate::leanh::lean_inc(v_v_2949_);
                    crate::leanh::lean_inc(v_k_2948_);
                    v_isSharedCheck_2983_ = (!crate::leanh::lean_is_exclusive(v_l_2934_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v_unused_2984_ = crate::leanh::lean_ctor_get(v_l_2934_, 4);
                        crate::leanh::lean_dec(v_unused_2984_);
                        v_unused_2985_ = crate::leanh::lean_ctor_get(v_l_2934_, 3);
                        crate::leanh::lean_dec(v_unused_2985_);
                        v_unused_2986_ = crate::leanh::lean_ctor_get(v_l_2934_, 2);
                        crate::leanh::lean_dec(v_unused_2986_);
                        v_unused_2987_ = crate::leanh::lean_ctor_get(v_l_2934_, 1);
                        crate::leanh::lean_dec(v_unused_2987_);
                        v_unused_2988_ = crate::leanh::lean_ctor_get(v_l_2934_, 0);
                        crate::leanh::lean_dec(v_unused_2988_);
                        v___x_2957_ = v_l_2934_;
                        v_isShared_2958_ = v_isSharedCheck_2983_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2934_);
                        v___x_2957_ = crate::leanh::lean_box(0);
                        v_isShared_2958_ = v_isSharedCheck_2983_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2785_);
                    v___x_2989_ = lean_nat_add(v___x_2929_, v_size_2930_);
                    v___x_2990_ = lean_nat_add(v___x_2989_, v_size_2931_);
                    crate::leanh::lean_dec(v_size_2931_);
                    v___x_2991_ = lean_nat_add(v___x_2989_, v_size_2947_);
                    crate::leanh::lean_dec(v___x_2989_);
                    crate::leanh::lean_inc_ref(v_l_2782_);
                    if v_isShared_2946_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2945_, 4, v_l_2934_);
                        crate::leanh::lean_ctor_set(v___x_2945_, 3, v_l_2782_);
                        crate::leanh::lean_ctor_set(v___x_2945_, 2, v_v_2781_);
                        crate::leanh::lean_ctor_set(v___x_2945_, 1, v_k_2780_);
                        crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2991_);
                        v___x_2993_ = v___x_2945_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2991_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_k_2780_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_v_2781_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_l_2782_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_l_2934_);
                        v___x_2993_ = v_reuseFailAlloc_3006_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2959_ = lean_nat_add(v___x_2929_, v_size_2930_);
                v___x_2960_ = lean_nat_add(v___x_2959_, v_size_2931_);
                crate::leanh::lean_dec(v_size_2931_);
                if crate::leanh::lean_obj_tag(v_l_2950_) == 0 {
                    v_size_2981_ = crate::leanh::lean_ctor_get(v_l_2950_, 0);
                    crate::leanh::lean_inc(v_size_2981_);
                    v___y_2973_ = v_size_2981_;
                    state = 29;
                    continue;
                } else {
                    v___x_2982_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2973_ = v___x_2982_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2965_ = lean_nat_add(v___y_2962_, v___y_2964_);
                crate::leanh::lean_dec(v___y_2964_);
                crate::leanh::lean_dec(v___y_2962_);
                if v_isShared_2958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2957_, 4, v_r_2935_);
                    crate::leanh::lean_ctor_set(v___x_2957_, 3, v_r_2951_);
                    crate::leanh::lean_ctor_set(v___x_2957_, 2, v_v_2933_);
                    crate::leanh::lean_ctor_set(v___x_2957_, 1, v_k_2932_);
                    crate::leanh::lean_ctor_set(v___x_2957_, 0, v___x_2965_);
                    v___x_2967_ = v___x_2957_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2971_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_k_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_v_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_r_2951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_r_2935_);
                    v___x_2967_ = v_reuseFailAlloc_2971_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2945_, 4, v___x_2967_);
                    crate::leanh::lean_ctor_set(v___x_2945_, 3, v___y_2963_);
                    crate::leanh::lean_ctor_set(v___x_2945_, 2, v_v_2949_);
                    crate::leanh::lean_ctor_set(v___x_2945_, 1, v_k_2948_);
                    crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2960_);
                    v___x_2969_ = v___x_2945_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_k_2948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_v_2949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 3, v___y_2963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 4, v___x_2967_);
                    v___x_2969_ = v_reuseFailAlloc_2970_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2969_;
            }
            29 => {
                v___x_2974_ = lean_nat_add(v___x_2959_, v___y_2973_);
                crate::leanh::lean_dec(v___y_2973_);
                crate::leanh::lean_dec(v___x_2959_);
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v_l_2950_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2974_);
                    v___x_2976_ = v___x_2785_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_l_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_l_2950_);
                    v___x_2976_ = v_reuseFailAlloc_2980_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2977_ = lean_nat_add(v___x_2929_, v_size_2952_);
                if crate::leanh::lean_obj_tag(v_r_2951_) == 0 {
                    v_size_2978_ = crate::leanh::lean_ctor_get(v_r_2951_, 0);
                    crate::leanh::lean_inc(v_size_2978_);
                    v___y_2962_ = v___x_2977_;
                    v___y_2963_ = v___x_2976_;
                    v___y_2964_ = v_size_2978_;
                    state = 26;
                    continue;
                } else {
                    v___x_2979_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2962_ = v___x_2977_;
                    v___y_2963_ = v___x_2976_;
                    v___y_2964_ = v___x_2979_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3000_ = (!crate::leanh::lean_is_exclusive(v_l_2782_)) as u8;
                if v_isSharedCheck_3000_ == 0 {
                    v_unused_3001_ = crate::leanh::lean_ctor_get(v_l_2782_, 4);
                    crate::leanh::lean_dec(v_unused_3001_);
                    v_unused_3002_ = crate::leanh::lean_ctor_get(v_l_2782_, 3);
                    crate::leanh::lean_dec(v_unused_3002_);
                    v_unused_3003_ = crate::leanh::lean_ctor_get(v_l_2782_, 2);
                    crate::leanh::lean_dec(v_unused_3003_);
                    v_unused_3004_ = crate::leanh::lean_ctor_get(v_l_2782_, 1);
                    crate::leanh::lean_dec(v_unused_3004_);
                    v_unused_3005_ = crate::leanh::lean_ctor_get(v_l_2782_, 0);
                    crate::leanh::lean_dec(v_unused_3005_);
                    v___x_2995_ = v_l_2782_;
                    v_isShared_2996_ = v_isSharedCheck_3000_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2782_);
                    v___x_2995_ = crate::leanh::lean_box(0);
                    v_isShared_2996_ = v_isSharedCheck_3000_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2995_, 4, v_r_2935_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 3, v___x_2993_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 2, v_v_2933_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 1, v_k_2932_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 0, v___x_2990_);
                    v___x_2998_ = v___x_2995_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2999_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_k_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_v_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 3, v___x_2993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_r_2935_);
                    v___x_2998_ = v_reuseFailAlloc_2999_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2998_;
            }
            34 => {
                v_k_3020_ = crate::leanh::lean_ctor_get(v_l_3013_, 1);
                v_v_3021_ = crate::leanh::lean_ctor_get(v_l_3013_, 2);
                v_isSharedCheck_3035_ = (!crate::leanh::lean_is_exclusive(v_l_3013_)) as u8;
                if v_isSharedCheck_3035_ == 0 {
                    v_unused_3036_ = crate::leanh::lean_ctor_get(v_l_3013_, 4);
                    crate::leanh::lean_dec(v_unused_3036_);
                    v_unused_3037_ = crate::leanh::lean_ctor_get(v_l_3013_, 3);
                    crate::leanh::lean_dec(v_unused_3037_);
                    v_unused_3038_ = crate::leanh::lean_ctor_get(v_l_3013_, 0);
                    crate::leanh::lean_dec(v_unused_3038_);
                    v___x_3023_ = v_l_3013_;
                    v_isShared_3024_ = v_isSharedCheck_3035_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3021_);
                    crate::leanh::lean_inc(v_k_3020_);
                    crate::leanh::lean_dec(v_l_3013_);
                    v___x_3023_ = crate::leanh::lean_box(0);
                    v_isShared_3024_ = v_isSharedCheck_3035_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3025_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_3014_, 2);
                if v_isShared_3024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3023_, 4, v_r_3014_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 3, v_r_3014_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 0, v___x_2929_);
                    v___x_3027_ = v___x_3023_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_2929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_r_3014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 4, v_r_3014_);
                    v___x_3027_ = v_reuseFailAlloc_3034_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_3014_);
                if v_isShared_3019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3018_, 3, v_r_3014_);
                    crate::leanh::lean_ctor_set(v___x_3018_, 0, v___x_2929_);
                    v___x_3029_ = v___x_3018_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_2929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_k_3015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_v_3016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_r_3014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 4, v_r_3014_);
                    v___x_3029_ = v_reuseFailAlloc_3033_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v___x_3029_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v___x_3027_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_3021_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_3020_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_3025_);
                    v___x_3031_ = v___x_2785_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_k_3020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_v_3021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 3, v___x_3027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 4, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3032_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3031_;
            }
            39 => {
                v___x_3048_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3046_, 4, v_l_3013_);
                    crate::leanh::lean_ctor_set(v___x_3046_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v___x_3046_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v___x_3046_, 0, v___x_2929_);
                    v___x_3050_ = v___x_3046_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_2929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_k_2780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_v_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_l_3013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_l_3013_);
                    v___x_3050_ = v_reuseFailAlloc_3054_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2786_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2785_, 4, v_r_3042_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 3, v___x_3050_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 2, v_v_3044_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 1, v_k_3043_);
                    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_3048_);
                    v___x_3052_ = v___x_2785_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_k_3043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_v_3044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 3, v___x_3050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_r_3042_);
                    v___x_3052_ = v_reuseFailAlloc_3053_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3052_;
            }
            42 => {
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(
    mut v___x_3069_: *mut crate::leanh::LeanObject,
    mut v_as_3070_: *mut crate::leanh::LeanObject,
    mut v_i_3071_: usize,
    mut v_stop_3072_: usize,
    mut v_b_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: usize = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_usize_dec_eq(v_i_3071_, v_stop_3072_);
                if v___x_3076_ == 0 {
                    v___x_3077_ = lean_array_uget_borrowed(v_as_3070_, v_i_3071_);
                    v_name_3078_ = crate::leanh::lean_ctor_get(v___x_3077_, 1);
                    v_kind_3079_ = crate::leanh::lean_ctor_get(v___x_3077_, 2);
                    v___x_3080_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_3073_, v_name_3078_);
                    if crate::leanh::lean_obj_tag(v___x_3080_) == 1 {
                        crate::leanh::lean_dec(v_b_3073_);
                        v_val_3081_ = crate::leanh::lean_ctor_get(v___x_3080_, 0);
                        crate::leanh::lean_inc(v_val_3081_);
                        crate::leanh::lean_dec_ref_known(v___x_3080_, 1);
                        v_kind_3082_ = crate::leanh::lean_ctor_get(v_val_3081_, 2);
                        crate::leanh::lean_inc(v_kind_3082_);
                        crate::leanh::lean_dec(v_val_3081_);
                        v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0;
                        v___x_3084_ = lean_string_append(v___x_3069_, v___x_3083_);
                        v___x_3085_ = 1;
                        crate::leanh::lean_inc(v_name_3078_);
                        v___x_3086_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_3078_,
                                v___x_3085_,
                            );
                        v___x_3087_ = lean_string_append(v___x_3084_, v___x_3086_);
                        crate::leanh::lean_dec_ref(v___x_3086_);
                        v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1;
                        v___x_3089_ = lean_string_append(v___x_3087_, v___x_3088_);
                        v___x_3090_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_3082_,
                                v___x_3085_,
                            );
                        v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
                        crate::leanh::lean_dec_ref(v___x_3090_);
                        v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2;
                        v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
                        crate::leanh::lean_inc(v_kind_3079_);
                        v___x_3094_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_3079_,
                                v___x_3085_,
                            );
                        v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
                        crate::leanh::lean_dec_ref(v___x_3094_);
                        v___x_3096_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                        v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
                        v___x_3098_ = 3;
                        v___x_3099_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3099_, 0, v___x_3097_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3099_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3098_,
                        );
                        v___x_3100_ = lean_array_get_size(v___y_3074_);
                        v___x_3101_ = lean_array_push(v___y_3074_, v___x_3099_);
                        v___x_3102_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3102_, 0, v___x_3100_);
                        crate::leanh::lean_ctor_set(v___x_3102_, 1, v___x_3101_);
                        return v___x_3102_;
                    } else {
                        crate::leanh::lean_dec(v___x_3080_);
                        crate::leanh::lean_inc(v___x_3077_);
                        crate::leanh::lean_inc(v_name_3078_);
                        v___x_3103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_3078_, v___x_3077_, v_b_3073_);
                        v___x_3104_ = 1usize;
                        v___x_3105_ = lean_usize_add(v_i_3071_, v___x_3104_);
                        v_i_3071_ = v___x_3105_;
                        v_b_3073_ = v___x_3103_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3069_);
                    v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3107_, 0, v_b_3073_);
                    crate::leanh::lean_ctor_set(v___x_3107_, 1, v___y_3074_);
                    return v___x_3107_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(
    mut v___x_3108_: *mut crate::leanh::LeanObject,
    mut v_as_3109_: *mut crate::leanh::LeanObject,
    mut v_i_3110_: *mut crate::leanh::LeanObject,
    mut v_stop_3111_: *mut crate::leanh::LeanObject,
    mut v_b_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3115_: usize = 0;
    let mut v_stop_boxed_3116_: usize = 0;
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3115_ = crate::leanh::lean_unbox_usize(v_i_3110_);
    crate::leanh::lean_dec(v_i_3110_);
    v_stop_boxed_3116_ = crate::leanh::lean_unbox_usize(v_stop_3111_);
    crate::leanh::lean_dec(v_stop_3111_);
    v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3108_, v_as_3109_, v_i_boxed_3115_, v_stop_boxed_3116_, v_b_3112_, v___y_3113_);
    crate::leanh::lean_dec_ref(v_as_3109_);
    return v_res_3117_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv(
    mut v_env_3124_: *mut crate::leanh::LeanObject,
    mut v_opts_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3149_: usize = 0;
    let mut v___x_3150_: usize = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___y_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3203_: usize = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3208_: usize = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3213_: usize = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3227_: usize = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v_lintDriver_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v___y_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3266_: usize = 0;
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3276_: usize = 0;
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3282_: usize = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3291_: usize = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3297_: usize = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: u8 = 0;
    let mut v_testDriver_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriver_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_a_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_a_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3346_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v_a_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_a_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_a_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v___y_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: usize = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3409_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: usize = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut v_a_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u8 = 0;
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_env_3124_);
                v___x_3136_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(
                    v_env_3124_,
                    v_opts_3125_,
                );
                v___x_3137_ =
                    l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                        v___x_3136_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3137_) == 0 {
                    v_a_3138_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    crate::leanh::lean_inc(v_a_3138_);
                    crate::leanh::lean_dec_ref_known(v___x_3137_, 1);
                    v___x_3139_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
                    crate::leanh::lean_inc_ref(v_opts_3125_);
                    crate::leanh::lean_inc_ref_n(v_env_3124_, 2);
                    v___f_3140_ = crate::leanh::lean_alloc_closure(
                        l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_3140_, 0, v_env_3124_);
                    crate::leanh::lean_closure_set(v___f_3140_, 1, v_opts_3125_);
                    crate::leanh::lean_closure_set(v___f_3140_, 2, v___x_3139_);
                    v___x_3141_ = l_Lake_targetAttr;
                    v___x_3142_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_3124_, v___x_3141_, v___f_3140_);
                    v___x_3143_ =
                        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                            v___x_3142_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3143_) == 0 {
                        v_a_3144_ = crate::leanh::lean_ctor_get(v___x_3143_, 0);
                        crate::leanh::lean_inc(v_a_3144_);
                        crate::leanh::lean_dec_ref_known(v___x_3143_, 1);
                        v_baseName_3145_ = crate::leanh::lean_ctor_get(v_a_3138_, 0);
                        v_keyName_3146_ = crate::leanh::lean_ctor_get(v_a_3138_, 1);
                        v_config_3147_ = crate::leanh::lean_ctor_get(v_a_3138_, 3);
                        v_toArray_3148_ = crate::leanh::lean_ctor_get(v_a_3144_, 1);
                        v_sz_3149_ = lean_array_size(v_toArray_3148_);
                        v___x_3150_ = 0usize;
                        crate::leanh::lean_inc_ref(v_toArray_3148_);
                        crate::leanh::lean_inc(v_keyName_3146_);
                        v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_3146_, v_sz_3149_, v___x_3150_, v_toArray_3148_, v_a_3126_);
                        if crate::leanh::lean_obj_tag(v___x_3151_) == 0 {
                            v_a_3152_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                            v_a_3153_ = crate::leanh::lean_ctor_get(v___x_3151_, 1);
                            v_isSharedCheck_3420_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                            if v_isSharedCheck_3420_ == 0 {
                                v___x_3155_ = v___x_3151_;
                                v_isShared_3156_ = v_isSharedCheck_3420_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3153_);
                                crate::leanh::lean_inc(v_a_3152_);
                                crate::leanh::lean_dec(v___x_3151_);
                                v___x_3155_ = crate::leanh::lean_box(0);
                                v_isShared_3156_ = v_isSharedCheck_3420_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3144_);
                            crate::leanh::lean_dec(v_a_3138_);
                            crate::leanh::lean_dec_ref(v_opts_3125_);
                            crate::leanh::lean_dec_ref(v_env_3124_);
                            v_a_3421_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                            v_a_3422_ = crate::leanh::lean_ctor_get(v___x_3151_, 1);
                            v_isSharedCheck_3429_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                            if v_isSharedCheck_3429_ == 0 {
                                v___x_3424_ = v___x_3151_;
                                v_isShared_3425_ = v_isSharedCheck_3429_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3422_);
                                crate::leanh::lean_inc(v_a_3421_);
                                crate::leanh::lean_dec(v___x_3151_);
                                v___x_3424_ = crate::leanh::lean_box(0);
                                v_isShared_3425_ = v_isSharedCheck_3429_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3138_);
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        crate::leanh::lean_dec_ref(v_env_3124_);
                        v_a_3430_ = crate::leanh::lean_ctor_get(v___x_3143_, 0);
                        crate::leanh::lean_inc(v_a_3430_);
                        crate::leanh::lean_dec_ref_known(v___x_3143_, 1);
                        v___x_3431_ = lean_io_error_to_string(v_a_3430_);
                        v___x_3432_ = 3;
                        v___x_3433_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3431_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3433_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3432_,
                        );
                        v___x_3434_ = lean_array_get_size(v_a_3126_);
                        v___x_3435_ = lean_array_push(v_a_3126_, v___x_3433_);
                        v___x_3436_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3436_, 0, v___x_3434_);
                        crate::leanh::lean_ctor_set(v___x_3436_, 1, v___x_3435_);
                        return v___x_3436_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    crate::leanh::lean_inc(v_a_3437_);
                    crate::leanh::lean_dec_ref_known(v___x_3137_, 1);
                    v___x_3438_ = lean_io_error_to_string(v_a_3437_);
                    v___x_3439_ = 3;
                    v___x_3440_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3438_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3440_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3439_,
                    );
                    v___x_3441_ = lean_array_get_size(v_a_3126_);
                    v___x_3442_ = lean_array_push(v_a_3126_, v___x_3440_);
                    v___x_3443_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3443_, 0, v___x_3441_);
                    crate::leanh::lean_ctor_set(v___x_3443_, 1, v___x_3442_);
                    return v___x_3443_;
                }
            }
            1 => {
                v___x_3131_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3131_, 0, v_a_3129_);
                crate::leanh::lean_ctor_set(v___x_3131_, 1, v_a_3130_);
                return v___x_3131_;
            }
            2 => {
                v___x_3135_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3135_, 0, v_a_3133_);
                crate::leanh::lean_ctor_set(v___x_3135_, 1, v_a_3134_);
                return v___x_3135_;
            }
            3 => {
                v___x_3183_ = l_Lake_instTypeNameScriptFn_unsafe__1;
                v___x_3184_ = 0;
                crate::leanh::lean_inc(v_baseName_3145_);
                v___x_3185_ = l_Lean_Name_toString(v_baseName_3145_, v___x_3184_);
                v___x_3186_ = crate::leanh::lean_box((v___x_3184_) as usize);
                crate::leanh::lean_inc_ref(v___x_3185_);
                crate::leanh::lean_inc_ref(v_opts_3125_);
                crate::leanh::lean_inc_ref(v_env_3124_);
                v___f_3187_ = crate::leanh::lean_alloc_closure(
                    l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed as *mut core::ffi::c_void,
                    8,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_3187_, 0, v___x_3186_);
                crate::leanh::lean_closure_set(v___f_3187_, 1, v_env_3124_);
                crate::leanh::lean_closure_set(v___f_3187_, 2, v_opts_3125_);
                crate::leanh::lean_closure_set(v___f_3187_, 3, v___x_3183_);
                crate::leanh::lean_closure_set(v___f_3187_, 4, v___x_3185_);
                v___x_3188_ = crate::leanh::lean_box(1);
                v___x_3189_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3391_ = lean_array_get_size(v_a_3152_);
                v___x_3414_ = lean_nat_dec_lt(v___x_3189_, v___x_3391_);
                if v___x_3414_ == 0 {
                    v_a_3393_ = v___x_3188_;
                    v_a_3394_ = v_a_3153_;
                    state = 27;
                    continue;
                } else {
                    v___x_3415_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
                    if v___x_3415_ == 0 {
                        if v___x_3414_ == 0 {
                            v_a_3393_ = v___x_3188_;
                            v_a_3394_ = v_a_3153_;
                            state = 27;
                            continue;
                        } else {
                            v___x_3416_ = lean_usize_of_nat(v___x_3391_);
                            crate::leanh::lean_inc_ref(v___x_3185_);
                            v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3416_, v___x_3188_, v_a_3153_);
                            v___y_3402_ = v___x_3417_;
                            state = 28;
                            continue;
                        }
                    } else {
                        v___x_3418_ = lean_usize_of_nat(v___x_3391_);
                        crate::leanh::lean_inc_ref(v___x_3185_);
                        v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3418_, v___x_3188_, v_a_3153_);
                        v___y_3402_ = v___x_3419_;
                        state = 28;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3168_ =
                    l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                        v___y_3167_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3168_) == 0 {
                    v_a_3169_ = crate::leanh::lean_ctor_get(v___x_3168_, 0);
                    crate::leanh::lean_inc(v_a_3169_);
                    crate::leanh::lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3170_, 0, v_a_3138_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 1, v___y_3161_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 2, v_a_3169_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 3, v_a_3152_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 4, v___y_3158_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 5, v___y_3165_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 6, v___y_3159_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 7, v___y_3164_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 8, v___y_3163_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 9, v___y_3162_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 10, v___y_3166_);
                    if v_isShared_3156_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3155_, 1, v___y_3160_);
                        crate::leanh::lean_ctor_set(v___x_3155_, 0, v___x_3170_);
                        v___x_3172_ = v___x_3155_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___y_3160_);
                        v___x_3172_ = v_reuseFailAlloc_3173_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3166_);
                    crate::leanh::lean_dec_ref(v___y_3165_);
                    crate::leanh::lean_dec_ref(v___y_3164_);
                    crate::leanh::lean_dec_ref(v___y_3163_);
                    crate::leanh::lean_dec_ref(v___y_3162_);
                    crate::leanh::lean_dec_ref(v___y_3161_);
                    crate::leanh::lean_dec(v___y_3159_);
                    crate::leanh::lean_dec(v___y_3158_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3138_);
                    v_a_3174_ = crate::leanh::lean_ctor_get(v___x_3168_, 0);
                    crate::leanh::lean_inc(v_a_3174_);
                    crate::leanh::lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3175_ = lean_io_error_to_string(v_a_3174_);
                    v___x_3176_ = 3;
                    v___x_3177_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3177_, 0, v___x_3175_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3177_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3176_,
                    );
                    v___x_3178_ = lean_array_get_size(v___y_3160_);
                    v___x_3179_ = lean_array_push(v___y_3160_, v___x_3177_);
                    if v_isShared_3156_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3155_, 1);
                        crate::leanh::lean_ctor_set(v___x_3155_, 1, v___x_3179_);
                        crate::leanh::lean_ctor_set(v___x_3155_, 0, v___x_3178_);
                        v___x_3181_ = v___x_3155_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
                        v___x_3181_ = v_reuseFailAlloc_3182_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3172_;
            }
            6 => {
                return v___x_3181_;
            }
            7 => {
                v___x_3200_ = l_Lake_LakefileConfig_loadFromEnv___closed__0;
                v___x_3201_ = l_Lake_moduleFacetAttr;
                crate::leanh::lean_inc_ref_n(v_env_3124_, 2);
                v___x_3202_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3201_, v_env_3124_);
                v_sz_3203_ = lean_array_size(v___x_3202_);
                v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_3124_, v_opts_3125_, v___x_3202_, v_sz_3203_, v___x_3150_, v___x_3200_);
                crate::leanh::lean_dec_ref(v___x_3202_);
                if crate::leanh::lean_obj_tag(v___x_3204_) == 0 {
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v___y_3158_ = v___y_3191_;
                    v___y_3159_ = v___y_3192_;
                    v___y_3160_ = v_a_3199_;
                    v___y_3161_ = v___y_3193_;
                    v___y_3162_ = v___y_3197_;
                    v___y_3163_ = v___y_3196_;
                    v___y_3164_ = v___y_3195_;
                    v___y_3165_ = v___y_3194_;
                    v___y_3166_ = v_a_3198_;
                    v___y_3167_ = v___x_3204_;
                    state = 4;
                    continue;
                } else {
                    v_a_3205_ = crate::leanh::lean_ctor_get(v___x_3204_, 0);
                    crate::leanh::lean_inc(v_a_3205_);
                    crate::leanh::lean_dec_ref_known(v___x_3204_, 1);
                    v___x_3206_ = l_Lake_packageFacetAttr;
                    crate::leanh::lean_inc_ref_n(v_env_3124_, 2);
                    v___x_3207_ =
                        l_Lake_OrderedTagAttribute_getAllEntries(v___x_3206_, v_env_3124_);
                    v_sz_3208_ = lean_array_size(v___x_3207_);
                    v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_3124_, v_opts_3125_, v___x_3207_, v_sz_3208_, v___x_3150_, v_a_3205_);
                    crate::leanh::lean_dec_ref(v___x_3207_);
                    if crate::leanh::lean_obj_tag(v___x_3209_) == 0 {
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        crate::leanh::lean_dec_ref(v_env_3124_);
                        v___y_3158_ = v___y_3191_;
                        v___y_3159_ = v___y_3192_;
                        v___y_3160_ = v_a_3199_;
                        v___y_3161_ = v___y_3193_;
                        v___y_3162_ = v___y_3197_;
                        v___y_3163_ = v___y_3196_;
                        v___y_3164_ = v___y_3195_;
                        v___y_3165_ = v___y_3194_;
                        v___y_3166_ = v_a_3198_;
                        v___y_3167_ = v___x_3209_;
                        state = 4;
                        continue;
                    } else {
                        v_a_3210_ = crate::leanh::lean_ctor_get(v___x_3209_, 0);
                        crate::leanh::lean_inc(v_a_3210_);
                        crate::leanh::lean_dec_ref_known(v___x_3209_, 1);
                        v___x_3211_ = l_Lake_libraryFacetAttr;
                        crate::leanh::lean_inc_ref(v_env_3124_);
                        v___x_3212_ =
                            l_Lake_OrderedTagAttribute_getAllEntries(v___x_3211_, v_env_3124_);
                        v_sz_3213_ = lean_array_size(v___x_3212_);
                        v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_3124_, v_opts_3125_, v___x_3212_, v_sz_3213_, v___x_3150_, v_a_3210_);
                        crate::leanh::lean_dec_ref(v___x_3212_);
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        v___y_3158_ = v___y_3191_;
                        v___y_3159_ = v___y_3192_;
                        v___y_3160_ = v_a_3199_;
                        v___y_3161_ = v___y_3193_;
                        v___y_3162_ = v___y_3197_;
                        v___y_3163_ = v___y_3196_;
                        v___y_3164_ = v___y_3195_;
                        v___y_3165_ = v___y_3194_;
                        v___y_3166_ = v_a_3198_;
                        v___y_3167_ = v___x_3214_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3225_ = l_Lake_lintDriverAttr;
                crate::leanh::lean_inc_ref(v_env_3124_);
                v___x_3226_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3225_, v_env_3124_);
                v_sz_3227_ = lean_array_size(v___x_3226_);
                crate::leanh::lean_inc_ref(v___x_3185_);
                v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_3144_, v___y_3218_, v___x_3185_, v_sz_3227_, v___x_3150_, v___x_3226_, v_a_3224_);
                if crate::leanh::lean_obj_tag(v___x_3228_) == 0 {
                    v_a_3229_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                    crate::leanh::lean_inc(v_a_3229_);
                    v_a_3230_ = crate::leanh::lean_ctor_get(v___x_3228_, 1);
                    crate::leanh::lean_inc(v_a_3230_);
                    crate::leanh::lean_dec_ref_known(v___x_3228_, 2);
                    v___x_3231_ = lean_array_get_size(v_a_3229_);
                    v___x_3232_ = lean_nat_dec_lt(v___y_3217_, v___x_3231_);
                    if v___x_3232_ == 0 {
                        v___x_3233_ = lean_nat_dec_lt(v___x_3189_, v___x_3231_);
                        if v___x_3233_ == 0 {
                            crate::leanh::lean_dec(v_a_3229_);
                            crate::leanh::lean_dec_ref(v___x_3185_);
                            v_lintDriver_3234_ = crate::leanh::lean_ctor_get(v_config_3147_, 14);
                            crate::leanh::lean_inc_ref(v_lintDriver_3234_);
                            v___y_3191_ = v___y_3216_;
                            v___y_3192_ = v___y_3218_;
                            v___y_3193_ = v___y_3219_;
                            v___y_3194_ = v___y_3222_;
                            v___y_3195_ = v___y_3221_;
                            v___y_3196_ = v___y_3220_;
                            v___y_3197_ = v_a_3223_;
                            v_a_3198_ = v_lintDriver_3234_;
                            v_a_3199_ = v_a_3230_;
                            state = 7;
                            continue;
                        } else {
                            v_lintDriver_3235_ = crate::leanh::lean_ctor_get(v_config_3147_, 14);
                            v___x_3236_ = lean_string_utf8_byte_size(v_lintDriver_3235_);
                            v___x_3237_ = lean_nat_dec_eq(v___x_3236_, v___x_3189_);
                            if v___x_3237_ == 0 {
                                crate::leanh::lean_dec(v_a_3229_);
                                crate::leanh::lean_dec_ref(v_a_3223_);
                                crate::leanh::lean_dec_ref(v___y_3222_);
                                crate::leanh::lean_dec_ref(v___y_3221_);
                                crate::leanh::lean_dec_ref(v___y_3220_);
                                crate::leanh::lean_dec_ref(v___y_3219_);
                                crate::leanh::lean_dec(v___y_3218_);
                                crate::leanh::lean_dec(v___y_3216_);
                                crate::leanh::lean_del_object(v___x_3155_);
                                crate::leanh::lean_dec(v_a_3152_);
                                crate::leanh::lean_dec(v_a_3138_);
                                crate::leanh::lean_dec_ref(v_opts_3125_);
                                crate::leanh::lean_dec_ref(v_env_3124_);
                                v___x_3238_ = l_Lake_LakefileConfig_loadFromEnv___closed__1;
                                v___x_3239_ = lean_string_append(v___x_3185_, v___x_3238_);
                                v___x_3240_ = 3;
                                v___x_3241_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3241_, 0, v___x_3239_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3241_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_3240_,
                                );
                                v___x_3242_ = lean_array_get_size(v_a_3230_);
                                v___x_3243_ = lean_array_push(v_a_3230_, v___x_3241_);
                                v_a_3133_ = v___x_3242_;
                                v_a_3134_ = v___x_3243_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3185_);
                                v___x_3244_ = lean_array_fget(v_a_3229_, v___x_3189_);
                                crate::leanh::lean_dec(v_a_3229_);
                                v___x_3245_ = l_Lean_Name_toString(v___x_3244_, v___x_3237_);
                                v___y_3191_ = v___y_3216_;
                                v___y_3192_ = v___y_3218_;
                                v___y_3193_ = v___y_3219_;
                                v___y_3194_ = v___y_3222_;
                                v___y_3195_ = v___y_3221_;
                                v___y_3196_ = v___y_3220_;
                                v___y_3197_ = v_a_3223_;
                                v_a_3198_ = v___x_3245_;
                                v_a_3199_ = v_a_3230_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3229_);
                        crate::leanh::lean_dec_ref(v_a_3223_);
                        crate::leanh::lean_dec_ref(v___y_3222_);
                        crate::leanh::lean_dec_ref(v___y_3221_);
                        crate::leanh::lean_dec_ref(v___y_3220_);
                        crate::leanh::lean_dec_ref(v___y_3219_);
                        crate::leanh::lean_dec(v___y_3218_);
                        crate::leanh::lean_dec(v___y_3216_);
                        crate::leanh::lean_del_object(v___x_3155_);
                        crate::leanh::lean_dec(v_a_3152_);
                        crate::leanh::lean_dec(v_a_3138_);
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        crate::leanh::lean_dec_ref(v_env_3124_);
                        v___x_3246_ = l_Lake_LakefileConfig_loadFromEnv___closed__2;
                        v___x_3247_ = lean_string_append(v___x_3185_, v___x_3246_);
                        v___x_3248_ = 3;
                        v___x_3249_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3249_, 0, v___x_3247_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3249_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3248_,
                        );
                        v___x_3250_ = lean_array_get_size(v_a_3230_);
                        v___x_3251_ = lean_array_push(v_a_3230_, v___x_3249_);
                        v_a_3133_ = v___x_3250_;
                        v_a_3134_ = v___x_3251_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_3223_);
                    crate::leanh::lean_dec_ref(v___y_3222_);
                    crate::leanh::lean_dec_ref(v___y_3221_);
                    crate::leanh::lean_dec_ref(v___y_3220_);
                    crate::leanh::lean_dec_ref(v___y_3219_);
                    crate::leanh::lean_dec(v___y_3218_);
                    crate::leanh::lean_dec(v___y_3216_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_del_object(v___x_3155_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3138_);
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3252_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                    v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3228_, 1);
                    v_isSharedCheck_3260_ = (!crate::leanh::lean_is_exclusive(v___x_3228_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3255_ = v___x_3228_;
                        v_isShared_3256_ = v_isSharedCheck_3260_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3253_);
                        crate::leanh::lean_inc(v_a_3252_);
                        crate::leanh::lean_dec(v___x_3228_);
                        v___x_3255_ = crate::leanh::lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3260_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3256_ == 0 {
                    v___x_3258_ = v___x_3255_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3259_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3258_;
            }
            11 => {
                v___x_3264_ = l_Lake_defaultTargetAttr;
                crate::leanh::lean_inc_ref(v_env_3124_);
                v___x_3265_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3264_, v_env_3124_);
                v_sz_3266_ = lean_array_size(v___x_3265_);
                crate::leanh::lean_inc_ref(v___x_3185_);
                crate::leanh::lean_inc(v_a_3144_);
                v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_3144_, v___x_3185_, v_sz_3266_, v___x_3150_, v___x_3265_, v_a_3263_);
                if crate::leanh::lean_obj_tag(v___x_3267_) == 0 {
                    v_a_3268_ = crate::leanh::lean_ctor_get(v___x_3267_, 0);
                    crate::leanh::lean_inc(v_a_3268_);
                    v_a_3269_ = crate::leanh::lean_ctor_get(v___x_3267_, 1);
                    crate::leanh::lean_inc(v_a_3269_);
                    crate::leanh::lean_dec_ref_known(v___x_3267_, 2);
                    v___x_3270_ = l_Lake_scriptAttr;
                    crate::leanh::lean_inc_ref(v_env_3124_);
                    v___x_3271_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_3124_, v___x_3270_, v___f_3187_, v_a_3269_);
                    if crate::leanh::lean_obj_tag(v___x_3271_) == 0 {
                        v_a_3272_ = crate::leanh::lean_ctor_get(v___x_3271_, 0);
                        crate::leanh::lean_inc(v_a_3272_);
                        v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3271_, 1);
                        crate::leanh::lean_inc(v_a_3273_);
                        crate::leanh::lean_dec_ref_known(v___x_3271_, 2);
                        v___x_3274_ = l_Lake_defaultScriptAttr;
                        crate::leanh::lean_inc_ref(v_env_3124_);
                        v___x_3275_ =
                            l_Lake_OrderedTagAttribute_getAllEntries(v___x_3274_, v_env_3124_);
                        v_sz_3276_ = lean_array_size(v___x_3275_);
                        crate::leanh::lean_inc_ref(v___x_3185_);
                        v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_3272_, v___x_3185_, v_sz_3276_, v___x_3150_, v___x_3275_, v_a_3273_);
                        if crate::leanh::lean_obj_tag(v___x_3277_) == 0 {
                            v_a_3278_ = crate::leanh::lean_ctor_get(v___x_3277_, 0);
                            crate::leanh::lean_inc(v_a_3278_);
                            v_a_3279_ = crate::leanh::lean_ctor_get(v___x_3277_, 1);
                            crate::leanh::lean_inc(v_a_3279_);
                            crate::leanh::lean_dec_ref_known(v___x_3277_, 2);
                            v___x_3280_ = l_Lake_postUpdateAttr;
                            crate::leanh::lean_inc_ref_n(v_env_3124_, 2);
                            v___x_3281_ =
                                l_Lake_OrderedTagAttribute_getAllEntries(v___x_3280_, v_env_3124_);
                            v_sz_3282_ = lean_array_size(v___x_3281_);
                            crate::leanh::lean_inc(v_keyName_3146_);
                            v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_3124_, v_opts_3125_, v_keyName_3146_, v_sz_3282_, v___x_3150_, v___x_3281_, v_a_3279_);
                            if crate::leanh::lean_obj_tag(v___x_3283_) == 0 {
                                v_a_3284_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                                v_a_3285_ = crate::leanh::lean_ctor_get(v___x_3283_, 1);
                                v_isSharedCheck_3341_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                                if v_isSharedCheck_3341_ == 0 {
                                    v___x_3287_ = v___x_3283_;
                                    v_isShared_3288_ = v_isSharedCheck_3341_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3285_);
                                    crate::leanh::lean_inc(v_a_3284_);
                                    crate::leanh::lean_dec(v___x_3283_);
                                    v___x_3287_ = crate::leanh::lean_box(0);
                                    v_isShared_3288_ = v_isSharedCheck_3341_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3278_);
                                crate::leanh::lean_dec(v_a_3272_);
                                crate::leanh::lean_dec(v_a_3268_);
                                crate::leanh::lean_dec(v___y_3262_);
                                crate::leanh::lean_dec_ref(v___x_3185_);
                                crate::leanh::lean_del_object(v___x_3155_);
                                crate::leanh::lean_dec(v_a_3152_);
                                crate::leanh::lean_dec(v_a_3144_);
                                crate::leanh::lean_dec(v_a_3138_);
                                crate::leanh::lean_dec_ref(v_opts_3125_);
                                crate::leanh::lean_dec_ref(v_env_3124_);
                                v_a_3342_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                                v_a_3343_ = crate::leanh::lean_ctor_get(v___x_3283_, 1);
                                v_isSharedCheck_3350_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                                if v_isSharedCheck_3350_ == 0 {
                                    v___x_3345_ = v___x_3283_;
                                    v_isShared_3346_ = v_isSharedCheck_3350_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3343_);
                                    crate::leanh::lean_inc(v_a_3342_);
                                    crate::leanh::lean_dec(v___x_3283_);
                                    v___x_3345_ = crate::leanh::lean_box(0);
                                    v_isShared_3346_ = v_isSharedCheck_3350_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3272_);
                            crate::leanh::lean_dec(v_a_3268_);
                            crate::leanh::lean_dec(v___y_3262_);
                            crate::leanh::lean_dec_ref(v___x_3185_);
                            crate::leanh::lean_del_object(v___x_3155_);
                            crate::leanh::lean_dec(v_a_3152_);
                            crate::leanh::lean_dec(v_a_3144_);
                            crate::leanh::lean_dec(v_a_3138_);
                            crate::leanh::lean_dec_ref(v_opts_3125_);
                            crate::leanh::lean_dec_ref(v_env_3124_);
                            v_a_3351_ = crate::leanh::lean_ctor_get(v___x_3277_, 0);
                            v_a_3352_ = crate::leanh::lean_ctor_get(v___x_3277_, 1);
                            v_isSharedCheck_3359_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3277_)) as u8;
                            if v_isSharedCheck_3359_ == 0 {
                                v___x_3354_ = v___x_3277_;
                                v_isShared_3355_ = v_isSharedCheck_3359_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3352_);
                                crate::leanh::lean_inc(v_a_3351_);
                                crate::leanh::lean_dec(v___x_3277_);
                                v___x_3354_ = crate::leanh::lean_box(0);
                                v_isShared_3355_ = v_isSharedCheck_3359_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3268_);
                        crate::leanh::lean_dec(v___y_3262_);
                        crate::leanh::lean_dec_ref(v___x_3185_);
                        crate::leanh::lean_del_object(v___x_3155_);
                        crate::leanh::lean_dec(v_a_3152_);
                        crate::leanh::lean_dec(v_a_3144_);
                        crate::leanh::lean_dec(v_a_3138_);
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        crate::leanh::lean_dec_ref(v_env_3124_);
                        v_a_3360_ = crate::leanh::lean_ctor_get(v___x_3271_, 0);
                        v_a_3361_ = crate::leanh::lean_ctor_get(v___x_3271_, 1);
                        v_isSharedCheck_3368_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3271_)) as u8;
                        if v_isSharedCheck_3368_ == 0 {
                            v___x_3363_ = v___x_3271_;
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3361_);
                            crate::leanh::lean_inc(v_a_3360_);
                            crate::leanh::lean_dec(v___x_3271_);
                            v___x_3363_ = crate::leanh::lean_box(0);
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3262_);
                    crate::leanh::lean_dec_ref(v___f_3187_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_del_object(v___x_3155_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3144_);
                    crate::leanh::lean_dec(v_a_3138_);
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3369_ = crate::leanh::lean_ctor_get(v___x_3267_, 0);
                    v_a_3370_ = crate::leanh::lean_ctor_get(v___x_3267_, 1);
                    v_isSharedCheck_3377_ = (!crate::leanh::lean_is_exclusive(v___x_3267_)) as u8;
                    if v_isSharedCheck_3377_ == 0 {
                        v___x_3372_ = v___x_3267_;
                        v_isShared_3373_ = v_isSharedCheck_3377_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3370_);
                        crate::leanh::lean_inc(v_a_3369_);
                        crate::leanh::lean_dec(v___x_3267_);
                        v___x_3372_ = crate::leanh::lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3377_;
                        state = 22;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3289_ = l_Lake_packageDepAttr;
                crate::leanh::lean_inc_ref_n(v_env_3124_, 2);
                v___x_3290_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3289_, v_env_3124_);
                v_sz_3291_ = lean_array_size(v___x_3290_);
                v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_3124_, v_opts_3125_, v_sz_3291_, v___x_3150_, v___x_3290_);
                v___x_3293_ =
                    l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                        v___x_3292_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3293_) == 0 {
                    crate::leanh::lean_del_object(v___x_3287_);
                    v_a_3294_ = crate::leanh::lean_ctor_get(v___x_3293_, 0);
                    crate::leanh::lean_inc(v_a_3294_);
                    crate::leanh::lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3295_ = l_Lake_testDriverAttr;
                    crate::leanh::lean_inc_ref(v_env_3124_);
                    v___x_3296_ =
                        l_Lake_OrderedTagAttribute_getAllEntries(v___x_3295_, v_env_3124_);
                    v_sz_3297_ = lean_array_size(v___x_3296_);
                    crate::leanh::lean_inc_ref(v___x_3185_);
                    crate::leanh::lean_inc(v_a_3144_);
                    v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_3144_, v_a_3272_, v___x_3185_, v_sz_3297_, v___x_3150_, v___x_3296_, v_a_3285_);
                    if crate::leanh::lean_obj_tag(v___x_3298_) == 0 {
                        v_a_3299_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        crate::leanh::lean_inc(v_a_3299_);
                        v_a_3300_ = crate::leanh::lean_ctor_get(v___x_3298_, 1);
                        crate::leanh::lean_inc(v_a_3300_);
                        crate::leanh::lean_dec_ref_known(v___x_3298_, 2);
                        v___x_3301_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3302_ = lean_array_get_size(v_a_3299_);
                        v___x_3303_ = lean_nat_dec_lt(v___x_3301_, v___x_3302_);
                        if v___x_3303_ == 0 {
                            v___x_3304_ = lean_nat_dec_lt(v___x_3189_, v___x_3302_);
                            if v___x_3304_ == 0 {
                                crate::leanh::lean_dec(v_a_3299_);
                                v_testDriver_3305_ =
                                    crate::leanh::lean_ctor_get(v_config_3147_, 12);
                                crate::leanh::lean_inc_ref(v_testDriver_3305_);
                                v___y_3216_ = v___y_3262_;
                                v___y_3217_ = v___x_3301_;
                                v___y_3218_ = v_a_3272_;
                                v___y_3219_ = v_a_3294_;
                                v___y_3220_ = v_a_3284_;
                                v___y_3221_ = v_a_3278_;
                                v___y_3222_ = v_a_3268_;
                                v_a_3223_ = v_testDriver_3305_;
                                v_a_3224_ = v_a_3300_;
                                state = 8;
                                continue;
                            } else {
                                v_testDriver_3306_ =
                                    crate::leanh::lean_ctor_get(v_config_3147_, 12);
                                v___x_3307_ = lean_string_utf8_byte_size(v_testDriver_3306_);
                                v___x_3308_ = lean_nat_dec_eq(v___x_3307_, v___x_3189_);
                                if v___x_3308_ == 0 {
                                    crate::leanh::lean_dec(v_a_3299_);
                                    crate::leanh::lean_dec(v_a_3294_);
                                    crate::leanh::lean_dec(v_a_3284_);
                                    crate::leanh::lean_dec(v_a_3278_);
                                    crate::leanh::lean_dec(v_a_3272_);
                                    crate::leanh::lean_dec(v_a_3268_);
                                    crate::leanh::lean_dec(v___y_3262_);
                                    crate::leanh::lean_del_object(v___x_3155_);
                                    crate::leanh::lean_dec(v_a_3152_);
                                    crate::leanh::lean_dec(v_a_3144_);
                                    crate::leanh::lean_dec(v_a_3138_);
                                    crate::leanh::lean_dec_ref(v_opts_3125_);
                                    crate::leanh::lean_dec_ref(v_env_3124_);
                                    v___x_3309_ = l_Lake_LakefileConfig_loadFromEnv___closed__3;
                                    v___x_3310_ = lean_string_append(v___x_3185_, v___x_3309_);
                                    v___x_3311_ = 3;
                                    v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3310_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_3312_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_3311_,
                                    );
                                    v___x_3313_ = lean_array_get_size(v_a_3300_);
                                    v___x_3314_ = lean_array_push(v_a_3300_, v___x_3312_);
                                    v_a_3129_ = v___x_3313_;
                                    v_a_3130_ = v___x_3314_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3315_ = lean_array_fget(v_a_3299_, v___x_3189_);
                                    crate::leanh::lean_dec(v_a_3299_);
                                    v___x_3316_ = l_Lean_Name_toString(v___x_3315_, v___x_3308_);
                                    v___y_3216_ = v___y_3262_;
                                    v___y_3217_ = v___x_3301_;
                                    v___y_3218_ = v_a_3272_;
                                    v___y_3219_ = v_a_3294_;
                                    v___y_3220_ = v_a_3284_;
                                    v___y_3221_ = v_a_3278_;
                                    v___y_3222_ = v_a_3268_;
                                    v_a_3223_ = v___x_3316_;
                                    v_a_3224_ = v_a_3300_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3299_);
                            crate::leanh::lean_dec(v_a_3294_);
                            crate::leanh::lean_dec(v_a_3284_);
                            crate::leanh::lean_dec(v_a_3278_);
                            crate::leanh::lean_dec(v_a_3272_);
                            crate::leanh::lean_dec(v_a_3268_);
                            crate::leanh::lean_dec(v___y_3262_);
                            crate::leanh::lean_del_object(v___x_3155_);
                            crate::leanh::lean_dec(v_a_3152_);
                            crate::leanh::lean_dec(v_a_3144_);
                            crate::leanh::lean_dec(v_a_3138_);
                            crate::leanh::lean_dec_ref(v_opts_3125_);
                            crate::leanh::lean_dec_ref(v_env_3124_);
                            v___x_3317_ = l_Lake_LakefileConfig_loadFromEnv___closed__4;
                            v___x_3318_ = lean_string_append(v___x_3185_, v___x_3317_);
                            v___x_3319_ = 3;
                            v___x_3320_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3318_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3320_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_3319_,
                            );
                            v___x_3321_ = lean_array_get_size(v_a_3300_);
                            v___x_3322_ = lean_array_push(v_a_3300_, v___x_3320_);
                            v_a_3129_ = v___x_3321_;
                            v_a_3130_ = v___x_3322_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3294_);
                        crate::leanh::lean_dec(v_a_3284_);
                        crate::leanh::lean_dec(v_a_3278_);
                        crate::leanh::lean_dec(v_a_3272_);
                        crate::leanh::lean_dec(v_a_3268_);
                        crate::leanh::lean_dec(v___y_3262_);
                        crate::leanh::lean_dec_ref(v___x_3185_);
                        crate::leanh::lean_del_object(v___x_3155_);
                        crate::leanh::lean_dec(v_a_3152_);
                        crate::leanh::lean_dec(v_a_3144_);
                        crate::leanh::lean_dec(v_a_3138_);
                        crate::leanh::lean_dec_ref(v_opts_3125_);
                        crate::leanh::lean_dec_ref(v_env_3124_);
                        v_a_3323_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        v_a_3324_ = crate::leanh::lean_ctor_get(v___x_3298_, 1);
                        v_isSharedCheck_3331_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3331_ == 0 {
                            v___x_3326_ = v___x_3298_;
                            v_isShared_3327_ = v_isSharedCheck_3331_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3324_);
                            crate::leanh::lean_inc(v_a_3323_);
                            crate::leanh::lean_dec(v___x_3298_);
                            v___x_3326_ = crate::leanh::lean_box(0);
                            v_isShared_3327_ = v_isSharedCheck_3331_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3284_);
                    crate::leanh::lean_dec(v_a_3278_);
                    crate::leanh::lean_dec(v_a_3272_);
                    crate::leanh::lean_dec(v_a_3268_);
                    crate::leanh::lean_dec(v___y_3262_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_del_object(v___x_3155_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3144_);
                    crate::leanh::lean_dec(v_a_3138_);
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3332_ = crate::leanh::lean_ctor_get(v___x_3293_, 0);
                    crate::leanh::lean_inc(v_a_3332_);
                    crate::leanh::lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3333_ = lean_io_error_to_string(v_a_3332_);
                    v___x_3334_ = 3;
                    v___x_3335_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3333_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3334_,
                    );
                    v___x_3336_ = lean_array_get_size(v_a_3285_);
                    v___x_3337_ = lean_array_push(v_a_3285_, v___x_3335_);
                    if v_isShared_3288_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3287_, 1);
                        crate::leanh::lean_ctor_set(v___x_3287_, 1, v___x_3337_);
                        crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3336_);
                        v___x_3339_ = v___x_3287_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3336_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3337_);
                        v___x_3339_ = v_reuseFailAlloc_3340_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_3327_ == 0 {
                    v___x_3329_ = v___x_3326_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_a_3324_);
                    v___x_3329_ = v_reuseFailAlloc_3330_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3329_;
            }
            15 => {
                return v___x_3339_;
            }
            16 => {
                if v_isShared_3346_ == 0 {
                    v___x_3348_ = v___x_3345_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3348_;
            }
            18 => {
                if v_isShared_3355_ == 0 {
                    v___x_3357_ = v___x_3354_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_a_3352_);
                    v___x_3357_ = v_reuseFailAlloc_3358_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3357_;
            }
            20 => {
                if v_isShared_3364_ == 0 {
                    v___x_3366_ = v___x_3363_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_a_3361_);
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3366_;
            }
            22 => {
                if v_isShared_3373_ == 0 {
                    v___x_3375_ = v___x_3372_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3376_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_a_3370_);
                    v___x_3375_ = v_reuseFailAlloc_3376_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3375_;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_3380_) == 0 {
                    v_a_3381_ = crate::leanh::lean_ctor_get(v___y_3380_, 1);
                    crate::leanh::lean_inc(v_a_3381_);
                    crate::leanh::lean_dec_ref_known(v___y_3380_, 2);
                    v___y_3262_ = v___y_3379_;
                    v_a_3263_ = v_a_3381_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3379_);
                    crate::leanh::lean_dec_ref(v___f_3187_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_del_object(v___x_3155_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3144_);
                    crate::leanh::lean_dec(v_a_3138_);
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3382_ = crate::leanh::lean_ctor_get(v___y_3380_, 0);
                    v_a_3383_ = crate::leanh::lean_ctor_get(v___y_3380_, 1);
                    v_isSharedCheck_3390_ = (!crate::leanh::lean_is_exclusive(v___y_3380_)) as u8;
                    if v_isSharedCheck_3390_ == 0 {
                        v___x_3385_ = v___y_3380_;
                        v_isShared_3386_ = v_isSharedCheck_3390_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3383_);
                        crate::leanh::lean_inc(v_a_3382_);
                        crate::leanh::lean_dec(v___y_3380_);
                        v___x_3385_ = crate::leanh::lean_box(0);
                        v_isShared_3386_ = v_isSharedCheck_3390_;
                        state = 25;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_3386_ == 0 {
                    v___x_3388_ = v___x_3385_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
                    v___x_3388_ = v_reuseFailAlloc_3389_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3388_;
            }
            27 => {
                v___x_3395_ = lean_nat_dec_lt(v___x_3189_, v___x_3391_);
                if v___x_3395_ == 0 {
                    v___y_3262_ = v_a_3393_;
                    v_a_3263_ = v_a_3394_;
                    state = 11;
                    continue;
                } else {
                    v___x_3396_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
                    if v___x_3396_ == 0 {
                        if v___x_3395_ == 0 {
                            v___y_3262_ = v_a_3393_;
                            v_a_3263_ = v_a_3394_;
                            state = 11;
                            continue;
                        } else {
                            v___x_3397_ = lean_usize_of_nat(v___x_3391_);
                            crate::leanh::lean_inc_ref(v___x_3185_);
                            v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3397_, v___x_3188_, v_a_3394_);
                            v___y_3379_ = v_a_3393_;
                            v___y_3380_ = v___x_3398_;
                            state = 24;
                            continue;
                        }
                    } else {
                        v___x_3399_ = lean_usize_of_nat(v___x_3391_);
                        crate::leanh::lean_inc_ref(v___x_3185_);
                        v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3399_, v___x_3188_, v_a_3394_);
                        v___y_3379_ = v_a_3393_;
                        v___y_3380_ = v___x_3400_;
                        state = 24;
                        continue;
                    }
                }
            }
            28 => {
                if crate::leanh::lean_obj_tag(v___y_3402_) == 0 {
                    v_a_3403_ = crate::leanh::lean_ctor_get(v___y_3402_, 0);
                    crate::leanh::lean_inc(v_a_3403_);
                    v_a_3404_ = crate::leanh::lean_ctor_get(v___y_3402_, 1);
                    crate::leanh::lean_inc(v_a_3404_);
                    crate::leanh::lean_dec_ref_known(v___y_3402_, 2);
                    v_a_3393_ = v_a_3403_;
                    v_a_3394_ = v_a_3404_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___f_3187_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_del_object(v___x_3155_);
                    crate::leanh::lean_dec(v_a_3152_);
                    crate::leanh::lean_dec(v_a_3144_);
                    crate::leanh::lean_dec(v_a_3138_);
                    crate::leanh::lean_dec_ref(v_opts_3125_);
                    crate::leanh::lean_dec_ref(v_env_3124_);
                    v_a_3405_ = crate::leanh::lean_ctor_get(v___y_3402_, 0);
                    v_a_3406_ = crate::leanh::lean_ctor_get(v___y_3402_, 1);
                    v_isSharedCheck_3413_ = (!crate::leanh::lean_is_exclusive(v___y_3402_)) as u8;
                    if v_isSharedCheck_3413_ == 0 {
                        v___x_3408_ = v___y_3402_;
                        v_isShared_3409_ = v_isSharedCheck_3413_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3406_);
                        crate::leanh::lean_inc(v_a_3405_);
                        crate::leanh::lean_dec(v___y_3402_);
                        v___x_3408_ = crate::leanh::lean_box(0);
                        v_isShared_3409_ = v_isSharedCheck_3413_;
                        state = 29;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_3409_ == 0 {
                    v___x_3411_ = v___x_3408_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_a_3406_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3411_;
            }
            31 => {
                if v_isShared_3425_ == 0 {
                    v___x_3427_ = v___x_3424_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_a_3422_);
                    v___x_3427_ = v_reuseFailAlloc_3428_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___boxed(
    mut v_env_3444_: *mut crate::leanh::LeanObject,
    mut v_opts_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lake_LakefileConfig_loadFromEnv(v_env_3444_, v_opts_3445_, v_a_3446_);
    return v_res_3448_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(
    mut v_00_u03b2_3449_: *mut crate::leanh::LeanObject,
    mut v_env_3450_: *mut crate::leanh::LeanObject,
    mut v_attr_3451_: *mut crate::leanh::LeanObject,
    mut v_f_3452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_3450_, v_attr_3451_, v_f_3452_);
    return v___x_3453_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(
    mut v_00_u03b2_3454_: *mut crate::leanh::LeanObject,
    mut v_env_3455_: *mut crate::leanh::LeanObject,
    mut v_attr_3456_: *mut crate::leanh::LeanObject,
    mut v_f_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_3454_, v_env_3455_, v_attr_3456_, v_f_3457_);
    crate::leanh::lean_dec_ref(v_attr_3456_);
    return v_res_3458_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(
    mut v_00_u03b2_3459_: *mut crate::leanh::LeanObject,
    mut v_inst_3460_: *mut crate::leanh::LeanObject,
    mut v_t_3461_: *mut crate::leanh::LeanObject,
    mut v_k_3462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_3461_, v_k_3462_);
    return v___x_3463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(
    mut v_00_u03b2_3464_: *mut crate::leanh::LeanObject,
    mut v_inst_3465_: *mut crate::leanh::LeanObject,
    mut v_t_3466_: *mut crate::leanh::LeanObject,
    mut v_k_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(
            v_00_u03b2_3464_,
            v_inst_3465_,
            v_t_3466_,
            v_k_3467_,
        );
    crate::leanh::lean_dec(v_k_3467_);
    crate::leanh::lean_dec(v_t_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(
    mut v_00_u03b2_3469_: *mut crate::leanh::LeanObject,
    mut v_k_3470_: *mut crate::leanh::LeanObject,
    mut v_v_3471_: *mut crate::leanh::LeanObject,
    mut v_t_3472_: *mut crate::leanh::LeanObject,
    mut v_hl_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_3470_, v_v_3471_, v_t_3472_);
    return v___x_3474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(
    mut v_00_u03b4_3475_: *mut crate::leanh::LeanObject,
    mut v_t_3476_: *mut crate::leanh::LeanObject,
    mut v_k_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_3476_, v_k_3477_);
    return v___x_3478_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(
    mut v_00_u03b4_3479_: *mut crate::leanh::LeanObject,
    mut v_t_3480_: *mut crate::leanh::LeanObject,
    mut v_k_3481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(
            v_00_u03b4_3479_,
            v_t_3480_,
            v_k_3481_,
        );
    crate::leanh::lean_dec(v_k_3481_);
    crate::leanh::lean_dec(v_t_3480_);
    return v_res_3482_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(
    mut v_00_u03b2_3483_: *mut crate::leanh::LeanObject,
    mut v_env_3484_: *mut crate::leanh::LeanObject,
    mut v_attr_3485_: *mut crate::leanh::LeanObject,
    mut v_f_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_3484_, v_attr_3485_, v_f_3486_, v___y_3487_);
    return v___x_3489_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(
    mut v_00_u03b2_3490_: *mut crate::leanh::LeanObject,
    mut v_env_3491_: *mut crate::leanh::LeanObject,
    mut v_attr_3492_: *mut crate::leanh::LeanObject,
    mut v_f_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3496_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_3490_, v_env_3491_, v_attr_3492_, v_f_3493_, v___y_3494_);
    crate::leanh::lean_dec_ref(v_attr_3492_);
    return v_res_3496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(
    mut v___x_3497_: *mut crate::leanh::LeanObject,
    mut v___x_3498_: *mut crate::leanh::LeanObject,
    mut v_as_3499_: *mut crate::leanh::LeanObject,
    mut v_i_3500_: usize,
    mut v_stop_3501_: usize,
    mut v_b_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3497_, v_as_3499_, v_i_3500_, v_stop_3501_, v_b_3502_, v___y_3503_);
    return v___x_3505_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(
    mut v___x_3506_: *mut crate::leanh::LeanObject,
    mut v___x_3507_: *mut crate::leanh::LeanObject,
    mut v_as_3508_: *mut crate::leanh::LeanObject,
    mut v_i_3509_: *mut crate::leanh::LeanObject,
    mut v_stop_3510_: *mut crate::leanh::LeanObject,
    mut v_b_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3514_: usize = 0;
    let mut v_stop_boxed_3515_: usize = 0;
    let mut v_res_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3514_ = crate::leanh::lean_unbox_usize(v_i_3509_);
    crate::leanh::lean_dec(v_i_3509_);
    v_stop_boxed_3515_ = crate::leanh::lean_unbox_usize(v_stop_3510_);
    crate::leanh::lean_dec(v_stop_3510_);
    v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_3506_, v___x_3507_, v_as_3508_, v_i_boxed_3514_, v_stop_boxed_3515_, v_b_3511_, v___y_3512_);
    crate::leanh::lean_dec_ref(v_as_3508_);
    crate::leanh::lean_dec(v___x_3507_);
    return v_res_3516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(
    mut v_00_u03b2_3517_: *mut crate::leanh::LeanObject,
    mut v_f_3518_: *mut crate::leanh::LeanObject,
    mut v_as_3519_: *mut crate::leanh::LeanObject,
    mut v_i_3520_: usize,
    mut v_stop_3521_: usize,
    mut v_b_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_3518_, v_as_3519_, v_i_3520_, v_stop_3521_, v_b_3522_);
    return v___x_3523_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(
    mut v_00_u03b2_3524_: *mut crate::leanh::LeanObject,
    mut v_f_3525_: *mut crate::leanh::LeanObject,
    mut v_as_3526_: *mut crate::leanh::LeanObject,
    mut v_i_3527_: *mut crate::leanh::LeanObject,
    mut v_stop_3528_: *mut crate::leanh::LeanObject,
    mut v_b_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3530_: usize = 0;
    let mut v_stop_boxed_3531_: usize = 0;
    let mut v_res_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3530_ = crate::leanh::lean_unbox_usize(v_i_3527_);
    crate::leanh::lean_dec(v_i_3527_);
    v_stop_boxed_3531_ = crate::leanh::lean_unbox_usize(v_stop_3528_);
    crate::leanh::lean_dec(v_stop_3528_);
    v_res_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_3524_, v_f_3525_, v_as_3526_, v_i_boxed_3530_, v_stop_boxed_3531_, v_b_3529_);
    crate::leanh::lean_dec_ref(v_as_3526_);
    return v_res_3532_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(
    mut v_00_u03b2_3533_: *mut crate::leanh::LeanObject,
    mut v_f_3534_: *mut crate::leanh::LeanObject,
    mut v_as_3535_: *mut crate::leanh::LeanObject,
    mut v_i_3536_: usize,
    mut v_stop_3537_: usize,
    mut v_b_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_3534_, v_as_3535_, v_i_3536_, v_stop_3537_, v_b_3538_, v___y_3539_);
    return v___x_3541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(
    mut v_00_u03b2_3542_: *mut crate::leanh::LeanObject,
    mut v_f_3543_: *mut crate::leanh::LeanObject,
    mut v_as_3544_: *mut crate::leanh::LeanObject,
    mut v_i_3545_: *mut crate::leanh::LeanObject,
    mut v_stop_3546_: *mut crate::leanh::LeanObject,
    mut v_b_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3550_: usize = 0;
    let mut v_stop_boxed_3551_: usize = 0;
    let mut v_res_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3550_ = crate::leanh::lean_unbox_usize(v_i_3545_);
    crate::leanh::lean_dec(v_i_3545_);
    v_stop_boxed_3551_ = crate::leanh::lean_unbox_usize(v_stop_3546_);
    crate::leanh::lean_dec(v_stop_3546_);
    v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_3542_, v_f_3543_, v_as_3544_, v_i_boxed_3550_, v_stop_boxed_3551_, v_b_3547_, v___y_3548_);
    crate::leanh::lean_dec_ref(v_as_3544_);
    return v_res_3552_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_AttributesCore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Lean_Eval(builtin);
}

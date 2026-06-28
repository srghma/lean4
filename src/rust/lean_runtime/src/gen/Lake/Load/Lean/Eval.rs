// Lean compiler output
// Module: Lake.Load.Lean.Eval
// Imports: Lake.Config.Workspace Lake.Config.LakefileConfig Lean.DocString Lake.DSL.AttributesCore
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 97, 116, 32, 39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [39, 44, 32, 96, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value:
    LeanStringObject<54> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value:
    LeanStringObject<55> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3_value
) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [112, 111, 115, 116, 45, 117, 112, 100, 97, 116, 101, 32, 104, 111, 111, 107, 32, 119, 97, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 44, 32, 98, 117, 116, 32, 119, 97, 115, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 105, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 32, 119, 97, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 44, 32, 98, 117, 116, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 117, 110, 100, 101, 114, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [58, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 32, 104, 97, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 114, 111, 111, 116, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [39, 32, 97, 115, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 115, 99, 114, 105, 112, 116, 32, 111, 114, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 116, 101, 115, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [39, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 108, 105, 110, 116, 32, 100, 114, 105, 118, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 115, 99, 114, 105, 112, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [58, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 32, 119, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 100, 101, 102, 105, 110, 101, 100, 32, 97, 115, 32, 97, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 44, 32, 98, 117, 116, 32, 116, 104, 101, 110, 32, 114, 101, 100, 101, 102, 105, 110, 101, 100, 32, 97, 115, 32, 97, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_LakefileConfig_loadFromEnv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__0_value) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__1_value: LeanStringObject<52> =
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
            58, 32, 99, 97, 110, 110, 111, 116, 32, 98, 111, 116, 104, 32, 115, 101, 116, 32, 108,
            105, 110, 116, 68, 114, 105, 118, 101, 114, 32, 97, 110, 100, 32, 117, 115, 101, 32,
            64, 91, 108, 105, 110, 116, 95, 100, 114, 105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__1_value) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__2_value: LeanStringObject<61> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LakefileConfig_loadFromEnv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__2_value) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__3_value: LeanStringObject<52> =
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
            58, 32, 99, 97, 110, 110, 111, 116, 32, 98, 111, 116, 104, 32, 115, 101, 116, 32, 116,
            101, 115, 116, 68, 114, 105, 118, 101, 114, 32, 97, 110, 100, 32, 117, 115, 101, 32,
            64, 91, 116, 101, 115, 116, 95, 100, 114, 105, 118, 101, 114, 93, 0,
        ],
    };
static mut l_Lake_LakefileConfig_loadFromEnv___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__3_value) as *mut LeanObject;
pub static l_Lake_LakefileConfig_loadFromEnv___closed__4_value: LeanStringObject<71> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LakefileConfig_loadFromEnv___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakefileConfig_loadFromEnv___closed__4_value) as *mut LeanObject;
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(
    mut v_inst_1780_: *mut LeanObject,
    mut v_const_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    v___x_1782_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__0;
    v___x_1783_ = 1;
    v___x_1784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_const_1781_,
        v___x_1783_,
    );
    v___x_1785_ = lean_string_append(v___x_1782_, v___x_1784_);
    lean_dec_ref(v___x_1784_);
    v___x_1786_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__1;
    v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
    v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_inst_1780_,
        v___x_1783_,
    );
    v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
    lean_dec_ref(v___x_1788_);
    v___x_1790_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg___closed__2;
    v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
    v___x_1792_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1792_, 0, v___x_1791_);
    return v___x_1792_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType(
    mut v_00_u03b1_1793_: *mut LeanObject,
    mut v_inst_1794_: *mut LeanObject,
    mut v_const_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ =
        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(
            v_inst_1794_,
            v_const_1795_,
        );
    return v___x_1796_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
    mut v_env_1799_: *mut LeanObject,
    mut v_opts_1800_: *mut LeanObject,
    mut v_inst_1801_: *mut LeanObject,
    mut v_const_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    v___x_1803_ = 0;
    lean_inc(v_const_1802_);
    lean_inc_ref(v_env_1799_);
    v___x_1804_ = l_Lean_Environment_find_x3f(v_env_1799_, v_const_1802_, v___x_1803_);
    if lean_obj_tag(v___x_1804_) == 0 {
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: u8 = 0;
        let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1801_);
        lean_dec_ref(v_env_1799_);
        v___x_1805_ =
            l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__0;
        v___x_1806_ = 1;
        v___x_1807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_const_1802_,
            v___x_1806_,
        );
        v___x_1808_ = lean_string_append(v___x_1805_, v___x_1807_);
        lean_dec_ref(v___x_1807_);
        v___x_1809_ =
            l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
        v___x_1810_ = lean_string_append(v___x_1808_, v___x_1809_);
        v___x_1811_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1811_, 0, v___x_1810_);
        return v___x_1811_;
    } else {
        let mut v_val_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        v_val_1812_ = lean_ctor_get(v___x_1804_, 0);
        lean_inc(v_val_1812_);
        lean_dec_ref_known(v___x_1804_, 1);
        v___x_1813_ = l_Lean_ConstantInfo_type(v_val_1812_);
        lean_dec(v_val_1812_);
        if lean_obj_tag(v___x_1813_) == 4 {
            let mut v_declName_1814_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1815_: u8 = 0;
            v_declName_1814_ = lean_ctor_get(v___x_1813_, 0);
            lean_inc(v_declName_1814_);
            lean_dec_ref_known(v___x_1813_, 2);
            v___x_1815_ = lean_name_eq(v_declName_1814_, v_inst_1801_);
            lean_dec(v_declName_1814_);
            if v___x_1815_ == 0 {
                let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_env_1799_);
                v___x_1816_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_1801_, v_const_1802_);
                return v___x_1816_;
            } else {
                let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_inst_1801_);
                v___x_1817_ = l_Lean_Environment_evalConst___redArg(
                    v_env_1799_,
                    v_opts_1800_,
                    v_const_1802_,
                    v___x_1815_,
                );
                lean_dec(v_const_1802_);
                lean_dec_ref(v_env_1799_);
                return v___x_1817_;
            }
        } else {
            let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_1813_);
            lean_dec_ref(v_env_1799_);
            v___x_1818_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck_throwUnexpectedType___redArg(v_inst_1801_, v_const_1802_);
            return v___x_1818_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___boxed(
    mut v_env_1819_: *mut LeanObject,
    mut v_opts_1820_: *mut LeanObject,
    mut v_inst_1821_: *mut LeanObject,
    mut v_const_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1823_: *mut LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_1819_,
        v_opts_1820_,
        v_inst_1821_,
        v_const_1822_,
    );
    lean_dec_ref(v_opts_1820_);
    return v_res_1823_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(
    mut v_env_1824_: *mut LeanObject,
    mut v_opts_1825_: *mut LeanObject,
    mut v_00_u03b1_1826_: *mut LeanObject,
    mut v_inst_1827_: *mut LeanObject,
    mut v_const_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    v___x_1829_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_1824_,
        v_opts_1825_,
        v_inst_1827_,
        v_const_1828_,
    );
    return v___x_1829_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___boxed(
    mut v_env_1830_: *mut LeanObject,
    mut v_opts_1831_: *mut LeanObject,
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_inst_1833_: *mut LeanObject,
    mut v_const_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1835_: *mut LeanObject = core::ptr::null_mut();
    v_res_1835_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck(
        v_env_1830_,
        v_opts_1831_,
        v_00_u03b1_1832_,
        v_inst_1833_,
        v_const_1834_,
    );
    lean_dec_ref(v_opts_1831_);
    return v_res_1835_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0(
    mut v_declName_1837_: *mut LeanObject,
    mut v_map_1838_: *mut LeanObject,
    mut v_toPure_1839_: *mut LeanObject,
    mut v_____do__lift_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1841_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
    v___x_1842_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v___x_1841_,
        v_declName_1837_,
        v_____do__lift_1840_,
        v_map_1838_,
    );
    v___x_1843_ = lean_apply_2(v_toPure_1839_, lean_box(0), v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1(
    mut v_toPure_1844_: *mut LeanObject,
    mut v_f_1845_: *mut LeanObject,
    mut v_toBind_1846_: *mut LeanObject,
    mut v_map_1847_: *mut LeanObject,
    mut v_declName_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_1848_);
    v___f_1849_ = lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1849_, 0, v_declName_1848_);
    lean_closure_set(v___f_1849_, 1, v_map_1847_);
    lean_closure_set(v___f_1849_, 2, v_toPure_1844_);
    v___x_1850_ = lean_apply_1(v_f_1845_, v_declName_1848_);
    v___x_1851_ = lean_apply_4(
        v_toBind_1846_,
        lean_box(0),
        lean_box(0),
        v___x_1850_,
        v___f_1849_,
    );
    return v___x_1851_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
    mut v_env_1852_: *mut LeanObject,
    mut v_attr_1853_: *mut LeanObject,
    mut v_inst_1854_: *mut LeanObject,
    mut v_f_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    v_toApplicative_1856_ = lean_ctor_get(v_inst_1854_, 0);
    v_toBind_1857_ = lean_ctor_get(v_inst_1854_, 1);
    v_toPure_1858_ = lean_ctor_get(v_toApplicative_1856_, 1);
    v_entries_1859_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1853_, v_env_1852_);
    v___x_1860_ = lean_box(1);
    v___x_1861_ = lean_unsigned_to_nat(0);
    v___x_1862_ = lean_array_get_size(v_entries_1859_);
    v___x_1863_ = lean_nat_dec_lt(v___x_1861_, v___x_1862_);
    if v___x_1863_ == 0 {
        let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1858_);
        lean_dec_ref(v_entries_1859_);
        lean_dec(v_f_1855_);
        lean_dec_ref(v_inst_1854_);
        v___x_1864_ = lean_apply_2(v_toPure_1858_, lean_box(0), v___x_1860_);
        return v___x_1864_;
    } else {
        let mut v___f_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: u8 = 0;
        lean_inc(v_toBind_1857_);
        lean_inc(v_toPure_1858_);
        v___f_1865_ = lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_1865_, 0, v_toPure_1858_);
        lean_closure_set(v___f_1865_, 1, v_f_1855_);
        lean_closure_set(v___f_1865_, 2, v_toBind_1857_);
        v___x_1866_ = lean_nat_dec_le(v___x_1862_, v___x_1862_);
        if v___x_1866_ == 0 {
            if v___x_1863_ == 0 {
                let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1858_);
                lean_dec_ref(v___f_1865_);
                lean_dec_ref(v_entries_1859_);
                lean_dec_ref(v_inst_1854_);
                v___x_1867_ = lean_apply_2(v_toPure_1858_, lean_box(0), v___x_1860_);
                return v___x_1867_;
            } else {
                let mut v___x_1868_: usize = 0;
                let mut v___x_1869_: usize = 0;
                let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
                v___x_1868_ = 0usize;
                v___x_1869_ = lean_usize_of_nat(v___x_1862_);
                v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
            v___x_1871_ = 0usize;
            v___x_1872_ = lean_usize_of_nat(v___x_1862_);
            v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_env_1874_: *mut LeanObject,
    mut v_attr_1875_: *mut LeanObject,
    mut v_inst_1876_: *mut LeanObject,
    mut v_f_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1878_: *mut LeanObject = core::ptr::null_mut();
    v_res_1878_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
        v_env_1874_,
        v_attr_1875_,
        v_inst_1876_,
        v_f_1877_,
    );
    lean_dec_ref(v_attr_1875_);
    return v_res_1878_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(
    mut v_m_1879_: *mut LeanObject,
    mut v_00_u03b2_1880_: *mut LeanObject,
    mut v_env_1881_: *mut LeanObject,
    mut v_attr_1882_: *mut LeanObject,
    mut v_inst_1883_: *mut LeanObject,
    mut v_f_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    v___x_1885_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg(
        v_env_1881_,
        v_attr_1882_,
        v_inst_1883_,
        v_f_1884_,
    );
    return v___x_1885_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___boxed(
    mut v_m_1886_: *mut LeanObject,
    mut v_00_u03b2_1887_: *mut LeanObject,
    mut v_env_1888_: *mut LeanObject,
    mut v_attr_1889_: *mut LeanObject,
    mut v_inst_1890_: *mut LeanObject,
    mut v_f_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1892_: *mut LeanObject = core::ptr::null_mut();
    v_res_1892_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap(
        v_m_1886_,
        v_00_u03b2_1887_,
        v_env_1888_,
        v_attr_1889_,
        v_inst_1890_,
        v_f_1891_,
    );
    lean_dec_ref(v_attr_1889_);
    return v_res_1892_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0(
    mut v_declName_1893_: *mut LeanObject,
    mut v_map_1894_: *mut LeanObject,
    mut v_toPure_1895_: *mut LeanObject,
    mut v_____do__lift_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_declName_1893_,
        v_____do__lift_1896_,
        v_map_1894_,
    );
    v___x_1898_ = lean_apply_2(v_toPure_1895_, lean_box(0), v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1(
    mut v_toPure_1899_: *mut LeanObject,
    mut v_f_1900_: *mut LeanObject,
    mut v_toBind_1901_: *mut LeanObject,
    mut v_map_1902_: *mut LeanObject,
    mut v_declName_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_1903_);
    v___f_1904_ = lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1904_, 0, v_declName_1903_);
    lean_closure_set(v___f_1904_, 1, v_map_1902_);
    lean_closure_set(v___f_1904_, 2, v_toPure_1899_);
    v___x_1905_ = lean_apply_1(v_f_1900_, v_declName_1903_);
    v___x_1906_ = lean_apply_4(
        v_toBind_1901_,
        lean_box(0),
        lean_box(0),
        v___x_1905_,
        v___f_1904_,
    );
    return v___x_1906_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
    mut v_env_1907_: *mut LeanObject,
    mut v_attr_1908_: *mut LeanObject,
    mut v_inst_1909_: *mut LeanObject,
    mut v_f_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: u8 = 0;
    v_toApplicative_1911_ = lean_ctor_get(v_inst_1909_, 0);
    v_toBind_1912_ = lean_ctor_get(v_inst_1909_, 1);
    v_toPure_1913_ = lean_ctor_get(v_toApplicative_1911_, 1);
    v_entries_1914_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1908_, v_env_1907_);
    v___x_1915_ = lean_box(1);
    v___x_1916_ = lean_unsigned_to_nat(0);
    v___x_1917_ = lean_array_get_size(v_entries_1914_);
    v___x_1918_ = lean_nat_dec_lt(v___x_1916_, v___x_1917_);
    if v___x_1918_ == 0 {
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1913_);
        lean_dec_ref(v_entries_1914_);
        lean_dec(v_f_1910_);
        lean_dec_ref(v_inst_1909_);
        v___x_1919_ = lean_apply_2(v_toPure_1913_, lean_box(0), v___x_1915_);
        return v___x_1919_;
    } else {
        let mut v___f_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: u8 = 0;
        lean_inc(v_toBind_1912_);
        lean_inc(v_toPure_1913_);
        v___f_1920_ = lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_1920_, 0, v_toPure_1913_);
        lean_closure_set(v___f_1920_, 1, v_f_1910_);
        lean_closure_set(v___f_1920_, 2, v_toBind_1912_);
        v___x_1921_ = lean_nat_dec_le(v___x_1917_, v___x_1917_);
        if v___x_1921_ == 0 {
            if v___x_1918_ == 0 {
                let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1913_);
                lean_dec_ref(v___f_1920_);
                lean_dec_ref(v_entries_1914_);
                lean_dec_ref(v_inst_1909_);
                v___x_1922_ = lean_apply_2(v_toPure_1913_, lean_box(0), v___x_1915_);
                return v___x_1922_;
            } else {
                let mut v___x_1923_: usize = 0;
                let mut v___x_1924_: usize = 0;
                let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
                v___x_1923_ = 0usize;
                v___x_1924_ = lean_usize_of_nat(v___x_1917_);
                v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
            v___x_1926_ = 0usize;
            v___x_1927_ = lean_usize_of_nat(v___x_1917_);
            v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_env_1929_: *mut LeanObject,
    mut v_attr_1930_: *mut LeanObject,
    mut v_inst_1931_: *mut LeanObject,
    mut v_f_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
        v_env_1929_,
        v_attr_1930_,
        v_inst_1931_,
        v_f_1932_,
    );
    lean_dec_ref(v_attr_1930_);
    return v_res_1933_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(
    mut v_m_1934_: *mut LeanObject,
    mut v_00_u03b2_1935_: *mut LeanObject,
    mut v_env_1936_: *mut LeanObject,
    mut v_attr_1937_: *mut LeanObject,
    mut v_inst_1938_: *mut LeanObject,
    mut v_f_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    v___x_1940_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___redArg(
        v_env_1936_,
        v_attr_1937_,
        v_inst_1938_,
        v_f_1939_,
    );
    return v___x_1940_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___boxed(
    mut v_m_1941_: *mut LeanObject,
    mut v_00_u03b2_1942_: *mut LeanObject,
    mut v_env_1943_: *mut LeanObject,
    mut v_attr_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
    mut v_f_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1947_: *mut LeanObject = core::ptr::null_mut();
    v_res_1947_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap(
        v_m_1941_,
        v_00_u03b2_1942_,
        v_env_1943_,
        v_attr_1944_,
        v_inst_1945_,
        v_f_1946_,
    );
    lean_dec_ref(v_attr_1944_);
    return v_res_1947_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0(
    mut v_map_1948_: *mut LeanObject,
    mut v_declName_1949_: *mut LeanObject,
    mut v_toPure_1950_: *mut LeanObject,
    mut v_____do__lift_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
    v___x_1953_ = l_Lake_RBArray_insert___redArg(
        v___x_1952_,
        v_map_1948_,
        v_declName_1949_,
        v_____do__lift_1951_,
    );
    v___x_1954_ = lean_apply_2(v_toPure_1950_, lean_box(0), v___x_1953_);
    return v___x_1954_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1(
    mut v_toPure_1955_: *mut LeanObject,
    mut v_f_1956_: *mut LeanObject,
    mut v_toBind_1957_: *mut LeanObject,
    mut v_map_1958_: *mut LeanObject,
    mut v_declName_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_1959_);
    v___f_1960_ = lean_alloc_closure(
        l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1960_, 0, v_map_1958_);
    lean_closure_set(v___f_1960_, 1, v_declName_1959_);
    lean_closure_set(v___f_1960_, 2, v_toPure_1955_);
    v___x_1961_ = lean_apply_1(v_f_1956_, v_declName_1959_);
    v___x_1962_ = lean_apply_4(
        v_toBind_1957_,
        lean_box(0),
        lean_box(0),
        v___x_1961_,
        v___f_1960_,
    );
    return v___x_1962_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
    mut v_env_1963_: *mut LeanObject,
    mut v_attr_1964_: *mut LeanObject,
    mut v_inst_1965_: *mut LeanObject,
    mut v_f_1966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    v_toApplicative_1967_ = lean_ctor_get(v_inst_1965_, 0);
    v_toBind_1968_ = lean_ctor_get(v_inst_1965_, 1);
    v_toPure_1969_ = lean_ctor_get(v_toApplicative_1967_, 1);
    v_entries_1970_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1964_, v_env_1963_);
    v___x_1971_ = lean_array_get_size(v_entries_1970_);
    v___x_1972_ = l_Lake_RBArray_mkEmpty___redArg(v___x_1971_);
    v___x_1973_ = lean_unsigned_to_nat(0);
    v___x_1974_ = lean_nat_dec_lt(v___x_1973_, v___x_1971_);
    if v___x_1974_ == 0 {
        let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1969_);
        lean_dec_ref(v_entries_1970_);
        lean_dec(v_f_1966_);
        lean_dec_ref(v_inst_1965_);
        v___x_1975_ = lean_apply_2(v_toPure_1969_, lean_box(0), v___x_1972_);
        return v___x_1975_;
    } else {
        let mut v___f_1976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: u8 = 0;
        lean_inc(v_toBind_1968_);
        lean_inc(v_toPure_1969_);
        v___f_1976_ = lean_alloc_closure(
            l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg___lam__1
                as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_1976_, 0, v_toPure_1969_);
        lean_closure_set(v___f_1976_, 1, v_f_1966_);
        lean_closure_set(v___f_1976_, 2, v_toBind_1968_);
        v___x_1977_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
        if v___x_1977_ == 0 {
            if v___x_1974_ == 0 {
                let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1969_);
                lean_dec_ref(v___f_1976_);
                lean_dec_ref(v_entries_1970_);
                lean_dec_ref(v_inst_1965_);
                v___x_1978_ = lean_apply_2(v_toPure_1969_, lean_box(0), v___x_1972_);
                return v___x_1978_;
            } else {
                let mut v___x_1979_: usize = 0;
                let mut v___x_1980_: usize = 0;
                let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
                v___x_1979_ = 0usize;
                v___x_1980_ = lean_usize_of_nat(v___x_1971_);
                v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
            v___x_1982_ = 0usize;
            v___x_1983_ = lean_usize_of_nat(v___x_1971_);
            v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_env_1985_: *mut LeanObject,
    mut v_attr_1986_: *mut LeanObject,
    mut v_inst_1987_: *mut LeanObject,
    mut v_f_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_res_1989_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
        v_env_1985_,
        v_attr_1986_,
        v_inst_1987_,
        v_f_1988_,
    );
    lean_dec_ref(v_attr_1986_);
    return v_res_1989_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(
    mut v_m_1990_: *mut LeanObject,
    mut v_00_u03b2_1991_: *mut LeanObject,
    mut v_env_1992_: *mut LeanObject,
    mut v_attr_1993_: *mut LeanObject,
    mut v_inst_1994_: *mut LeanObject,
    mut v_f_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___redArg(
        v_env_1992_,
        v_attr_1993_,
        v_inst_1994_,
        v_f_1995_,
    );
    return v___x_1996_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___boxed(
    mut v_m_1997_: *mut LeanObject,
    mut v_00_u03b2_1998_: *mut LeanObject,
    mut v_env_1999_: *mut LeanObject,
    mut v_attr_2000_: *mut LeanObject,
    mut v_inst_2001_: *mut LeanObject,
    mut v_f_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2003_: *mut LeanObject = core::ptr::null_mut();
    v_res_2003_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap(
        v_m_1997_,
        v_00_u03b2_1998_,
        v_env_1999_,
        v_attr_2000_,
        v_inst_2001_,
        v_f_2002_,
    );
    lean_dec_ref(v_attr_2000_);
    return v_res_2003_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(
    mut v_env_2010_: *mut LeanObject,
    mut v_opts_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lake_packageAttr;
    lean_inc_ref(v_env_2010_);
    v___x_2013_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_2012_, v_env_2010_);
    v___x_2014_ = lean_array_to_list(v___x_2013_);
    if lean_obj_tag(v___x_2014_) == 0 {
        let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_2010_);
        v___x_2015_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__1;
        return v___x_2015_;
    } else {
        let mut v_tail_2016_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2016_ = lean_ctor_get(v___x_2014_, 1);
        lean_inc(v_tail_2016_);
        if lean_obj_tag(v_tail_2016_) == 0 {
            let mut v_head_2017_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
            v_head_2017_ = lean_ctor_get(v___x_2014_, 0);
            lean_inc(v_head_2017_);
            lean_dec_ref_known(v___x_2014_, 2);
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
            let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_2014_, 2);
            lean_dec(v_tail_2016_);
            lean_dec_ref(v_env_2010_);
            v___x_2020_ =
                l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___closed__3;
            return v___x_2020_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv___boxed(
    mut v_env_2021_: *mut LeanObject,
    mut v_opts_2022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2023_: *mut LeanObject = core::ptr::null_mut();
    v_res_2023_ =
        l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_2021_, v_opts_2022_);
    lean_dec_ref(v_opts_2022_);
    return v_res_2023_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
    mut v_e_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut v_a_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_2024_) == 0 {
                    v_a_2026_ = lean_ctor_get(v_e_2024_, 0);
                    v_isSharedCheck_2034_ = (!lean_is_exclusive(v_e_2024_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2028_ = v_e_2024_;
                        v_isShared_2029_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2026_);
                        lean_dec(v_e_2024_);
                        v___x_2028_ = lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2035_ = lean_ctor_get(v_e_2024_, 0);
                    v_isSharedCheck_2042_ = (!lean_is_exclusive(v_e_2024_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v___x_2037_ = v_e_2024_;
                        v_isShared_2038_ = v_isSharedCheck_2042_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2035_);
                        lean_dec(v_e_2024_);
                        v___x_2037_ = lean_box(0);
                        v_isShared_2038_ = v_isSharedCheck_2042_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2030_ = lean_mk_io_user_error(v_a_2026_);
                if v_isShared_2029_ == 0 {
                    lean_ctor_set_tag(v___x_2028_, 1);
                    lean_ctor_set(v___x_2028_, 0, v___x_2030_);
                    v___x_2032_ = v___x_2028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
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
                    lean_ctor_set_tag(v___x_2037_, 0);
                    v___x_2040_ = v___x_2037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
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
    mut v_e_2043_: *mut LeanObject,
    mut v_a_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2045_: *mut LeanObject = core::ptr::null_mut();
    v_res_2045_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_2043_);
    return v_res_2045_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(
    mut v_00_u03b1_2046_: *mut LeanObject,
    mut v_e_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_2047_);
    return v___x_2049_;
}
pub unsafe fn l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___boxed(
    mut v_00_u03b1_2050_: *mut LeanObject,
    mut v_e_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2053_: *mut LeanObject = core::ptr::null_mut();
    v_res_2053_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(v_00_u03b1_2050_, v_e_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__0(
    mut v_env_2054_: *mut LeanObject,
    mut v_opts_2055_: *mut LeanObject,
    mut v___x_2056_: *mut LeanObject,
    mut v_name_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v___x_2058_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_2054_,
        v_opts_2055_,
        v___x_2056_,
        v_name_2057_,
    );
    return v___x_2058_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed(
    mut v_env_2059_: *mut LeanObject,
    mut v_opts_2060_: *mut LeanObject,
    mut v___x_2061_: *mut LeanObject,
    mut v_name_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lake_LakefileConfig_loadFromEnv___lam__0(
        v_env_2059_,
        v_opts_2060_,
        v___x_2061_,
        v_name_2062_,
    );
    lean_dec_ref(v_opts_2060_);
    return v_res_2063_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__1(
    mut v___x_2065_: u8,
    mut v_env_2066_: *mut LeanObject,
    mut v_opts_2067_: *mut LeanObject,
    mut v___x_2068_: *mut LeanObject,
    mut v___x_2069_: *mut LeanObject,
    mut v_scriptName_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_scriptName_2070_, 2);
    v___x_2073_ = l_Lean_Name_toString(v_scriptName_2070_, v___x_2065_);
    lean_inc_ref(v_env_2066_);
    v___x_2074_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
        v_env_2066_,
        v_opts_2067_,
        v___x_2068_,
        v_scriptName_2070_,
    );
    v___x_2075_ =
        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_2074_);
    if lean_obj_tag(v___x_2075_) == 0 {
        let mut v_a_2076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: u8 = 0;
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
        lean_inc(v_a_2076_);
        lean_dec_ref_known(v___x_2075_, 1);
        v___x_2077_ = 1;
        v___x_2078_ = l_Lean_findDocString_x3f(v_env_2066_, v_scriptName_2070_, v___x_2077_);
        if lean_obj_tag(v___x_2078_) == 0 {
            let mut v_a_2079_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
            v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
            lean_inc(v_a_2079_);
            lean_dec_ref_known(v___x_2078_, 1);
            v___x_2080_ = l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0;
            v___x_2081_ = lean_string_append(v___x_2069_, v___x_2080_);
            v___x_2082_ = lean_string_append(v___x_2081_, v___x_2073_);
            lean_dec_ref(v___x_2073_);
            v___x_2083_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_2083_, 0, v___x_2082_);
            lean_ctor_set(v___x_2083_, 1, v_a_2076_);
            lean_ctor_set(v___x_2083_, 2, v_a_2079_);
            v___x_2084_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2084_, 0, v___x_2083_);
            lean_ctor_set(v___x_2084_, 1, v___y_2071_);
            return v___x_2084_;
        } else {
            let mut v_a_2085_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2087_: u8 = 0;
            let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_2076_);
            lean_dec_ref(v___x_2073_);
            lean_dec_ref(v___x_2069_);
            v_a_2085_ = lean_ctor_get(v___x_2078_, 0);
            lean_inc(v_a_2085_);
            lean_dec_ref_known(v___x_2078_, 1);
            v___x_2086_ = lean_io_error_to_string(v_a_2085_);
            v___x_2087_ = 3;
            v___x_2088_ = lean_alloc_ctor(0, 1, (1) as u32);
            lean_ctor_set(v___x_2088_, 0, v___x_2086_);
            lean_ctor_set_uint8(
                v___x_2088_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                v___x_2087_,
            );
            v___x_2089_ = lean_array_get_size(v___y_2071_);
            v___x_2090_ = lean_array_push(v___y_2071_, v___x_2088_);
            v___x_2091_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2091_, 0, v___x_2089_);
            lean_ctor_set(v___x_2091_, 1, v___x_2090_);
            return v___x_2091_;
        }
    } else {
        let mut v_a_2092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: u8 = 0;
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2073_);
        lean_dec(v_scriptName_2070_);
        lean_dec_ref(v___x_2069_);
        lean_dec_ref(v_env_2066_);
        v_a_2092_ = lean_ctor_get(v___x_2075_, 0);
        lean_inc(v_a_2092_);
        lean_dec_ref_known(v___x_2075_, 1);
        v___x_2093_ = lean_io_error_to_string(v_a_2092_);
        v___x_2094_ = 3;
        v___x_2095_ = lean_alloc_ctor(0, 1, (1) as u32);
        lean_ctor_set(v___x_2095_, 0, v___x_2093_);
        lean_ctor_set_uint8(
            v___x_2095_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_2094_,
        );
        v___x_2096_ = lean_array_get_size(v___y_2071_);
        v___x_2097_ = lean_array_push(v___y_2071_, v___x_2095_);
        v___x_2098_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2098_, 0, v___x_2096_);
        lean_ctor_set(v___x_2098_, 1, v___x_2097_);
        return v___x_2098_;
    }
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(
    mut v___x_2099_: *mut LeanObject,
    mut v_env_2100_: *mut LeanObject,
    mut v_opts_2101_: *mut LeanObject,
    mut v___x_2102_: *mut LeanObject,
    mut v___x_2103_: *mut LeanObject,
    mut v_scriptName_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_50967__boxed_2107_: u8 = 0;
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v___x_50967__boxed_2107_ = (lean_unbox(v___x_2099_) as u8);
    v_res_2108_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(
        v___x_50967__boxed_2107_,
        v_env_2100_,
        v_opts_2101_,
        v___x_2102_,
        v___x_2103_,
        v_scriptName_2104_,
        v___y_2105_,
    );
    lean_dec_ref(v_opts_2101_);
    return v_res_2108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(
    mut v_env_2111_: *mut LeanObject,
    mut v_opts_2112_: *mut LeanObject,
    mut v___x_2113_: *mut LeanObject,
    mut v_sz_2114_: usize,
    mut v_i_2115_: usize,
    mut v_bs_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: usize = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2123_ = lean_usize_dec_lt(v_i_2115_, v_sz_2114_);
                if v___x_2123_ == 0 {
                    lean_dec(v___x_2113_);
                    lean_dec_ref(v_env_2111_);
                    v___x_2124_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2124_, 0, v_bs_2116_);
                    lean_ctor_set(v___x_2124_, 1, v___y_2117_);
                    return v___x_2124_;
                } else {
                    v___x_2125_ =
                        l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
                    v_v_2126_ = lean_array_uget_borrowed(v_bs_2116_, v_i_2115_);
                    lean_inc(v_v_2126_);
                    lean_inc_ref(v_env_2111_);
                    v___x_2127_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2111_,
                            v_opts_2112_,
                            v___x_2125_,
                            v_v_2126_,
                        );
                    if lean_obj_tag(v___x_2127_) == 0 {
                        lean_dec_ref(v_bs_2116_);
                        lean_dec(v___x_2113_);
                        lean_dec_ref(v_env_2111_);
                        v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
                        lean_inc(v_a_2128_);
                        lean_dec_ref_known(v___x_2127_, 1);
                        v___x_2129_ = 3;
                        v___x_2130_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2130_, 0, v_a_2128_);
                        lean_ctor_set_uint8(
                            v___x_2130_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2129_,
                        );
                        v___x_2131_ = lean_array_get_size(v___y_2117_);
                        v___x_2132_ = lean_array_push(v___y_2117_, v___x_2130_);
                        v_a_2120_ = v___x_2131_;
                        v_a_2121_ = v___x_2132_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2133_ = lean_ctor_get(v___x_2127_, 0);
                        lean_inc(v_a_2133_);
                        lean_dec_ref_known(v___x_2127_, 1);
                        v_pkg_2134_ = lean_ctor_get(v_a_2133_, 0);
                        lean_inc(v_pkg_2134_);
                        v_fn_2135_ = lean_ctor_get(v_a_2133_, 1);
                        lean_inc_ref(v_fn_2135_);
                        lean_dec(v_a_2133_);
                        v___x_2136_ = lean_name_eq(v_pkg_2134_, v___x_2113_);
                        if v___x_2136_ == 0 {
                            lean_dec_ref(v_fn_2135_);
                            lean_dec_ref(v_bs_2116_);
                            lean_dec_ref(v_env_2111_);
                            v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0;
                            v___x_2138_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_pkg_2134_,
                                    v___x_2123_,
                                );
                            v___x_2139_ = lean_string_append(v___x_2137_, v___x_2138_);
                            lean_dec_ref(v___x_2138_);
                            v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1;
                            v___x_2141_ = lean_string_append(v___x_2139_, v___x_2140_);
                            v___x_2142_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2113_,
                                    v___x_2123_,
                                );
                            v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
                            lean_dec_ref(v___x_2142_);
                            v___x_2144_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                            v___x_2145_ = lean_string_append(v___x_2143_, v___x_2144_);
                            v___x_2146_ = 3;
                            v___x_2147_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                            lean_ctor_set_uint8(
                                v___x_2147_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_2146_,
                            );
                            v___x_2148_ = lean_array_get_size(v___y_2117_);
                            v___x_2149_ = lean_array_push(v___y_2117_, v___x_2147_);
                            v_a_2120_ = v___x_2148_;
                            v_a_2121_ = v___x_2149_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_pkg_2134_);
                            v___x_2150_ = lean_unsigned_to_nat(0);
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
                v___x_2122_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2122_, 0, v_a_2120_);
                lean_ctor_set(v___x_2122_, 1, v_a_2121_);
                return v___x_2122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(
    mut v_env_2156_: *mut LeanObject,
    mut v_opts_2157_: *mut LeanObject,
    mut v___x_2158_: *mut LeanObject,
    mut v_sz_2159_: *mut LeanObject,
    mut v_i_2160_: *mut LeanObject,
    mut v_bs_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2164_: usize = 0;
    let mut v_i_boxed_2165_: usize = 0;
    let mut v_res_2166_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2164_ = lean_unbox_usize(v_sz_2159_);
    lean_dec(v_sz_2159_);
    v_i_boxed_2165_ = lean_unbox_usize(v_i_2160_);
    lean_dec(v_i_2160_);
    v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_2156_, v_opts_2157_, v___x_2158_, v_sz_boxed_2164_, v_i_boxed_2165_, v_bs_2161_, v___y_2162_);
    lean_dec_ref(v_opts_2157_);
    return v_res_2166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(
    mut v___x_2170_: *mut LeanObject,
    mut v_sz_2171_: usize,
    mut v_i_2172_: usize,
    mut v_bs_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2176_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
                if v___x_2176_ == 0 {
                    lean_dec(v___x_2170_);
                    v___x_2177_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2177_, 0, v_bs_2173_);
                    lean_ctor_set(v___x_2177_, 1, v___y_2174_);
                    return v___x_2177_;
                } else {
                    v_v_2178_ = lean_array_uget(v_bs_2173_, v_i_2172_);
                    v_pkg_2179_ = lean_ctor_get(v_v_2178_, 0);
                    v_name_2180_ = lean_ctor_get(v_v_2178_, 1);
                    v___x_2181_ = lean_name_eq(v_pkg_2179_, v___x_2170_);
                    if v___x_2181_ == 0 {
                        lean_inc(v_name_2180_);
                        lean_inc(v_pkg_2179_);
                        lean_dec(v_v_2178_);
                        lean_dec_ref(v_bs_2173_);
                        v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__0;
                        v___x_2183_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_2180_,
                                v___x_2176_,
                            );
                        v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
                        lean_dec_ref(v___x_2183_);
                        v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__1;
                        v___x_2186_ = lean_string_append(v___x_2184_, v___x_2185_);
                        v___x_2187_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_pkg_2179_,
                                v___x_2176_,
                            );
                        v___x_2188_ = lean_string_append(v___x_2186_, v___x_2187_);
                        lean_dec_ref(v___x_2187_);
                        v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2___closed__2;
                        v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
                        v___x_2191_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2170_,
                                v___x_2176_,
                            );
                        v___x_2192_ = lean_string_append(v___x_2190_, v___x_2191_);
                        lean_dec_ref(v___x_2191_);
                        v___x_2193_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                        v___x_2194_ = lean_string_append(v___x_2192_, v___x_2193_);
                        v___x_2195_ = 3;
                        v___x_2196_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2196_, 0, v___x_2194_);
                        lean_ctor_set_uint8(
                            v___x_2196_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2195_,
                        );
                        v___x_2197_ = lean_array_get_size(v___y_2174_);
                        v___x_2198_ = lean_array_push(v___y_2174_, v___x_2196_);
                        v___x_2199_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                        lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                        return v___x_2199_;
                    } else {
                        v___x_2200_ = lean_unsigned_to_nat(0);
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
    mut v___x_2206_: *mut LeanObject,
    mut v_sz_2207_: *mut LeanObject,
    mut v_i_2208_: *mut LeanObject,
    mut v_bs_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2212_: usize = 0;
    let mut v_i_boxed_2213_: usize = 0;
    let mut v_res_2214_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2212_ = lean_unbox_usize(v_sz_2207_);
    lean_dec(v_sz_2207_);
    v_i_boxed_2213_ = lean_unbox_usize(v_i_2208_);
    lean_dec(v_i_2208_);
    v_res_2214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v___x_2206_, v_sz_boxed_2212_, v_i_boxed_2213_, v_bs_2209_, v___y_2210_);
    return v_res_2214_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(
    mut v_t_2215_: *mut LeanObject,
    mut v_k_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2215_) == 0 {
                    v_k_2217_ = lean_ctor_get(v_t_2215_, 1);
                    v_v_2218_ = lean_ctor_get(v_t_2215_, 2);
                    v_l_2219_ = lean_ctor_get(v_t_2215_, 3);
                    v_r_2220_ = lean_ctor_get(v_t_2215_, 4);
                    v___x_2221_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2216_, v_k_2217_);
                    match v___x_2221_ {
                        0 => {
                            v_t_2215_ = v_l_2219_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2218_);
                            v___x_2223_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2223_, 0, v_v_2218_);
                            return v___x_2223_;
                        }
                        _ => {
                            v_t_2215_ = v_r_2220_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2225_ = lean_box(0);
                    return v___x_2225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(
    mut v_t_2226_: *mut LeanObject,
    mut v_k_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_2226_, v_k_2227_);
    lean_dec(v_k_2227_);
    lean_dec(v_t_2226_);
    return v_res_2228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(
    mut v_a_2231_: *mut LeanObject,
    mut v___x_2232_: *mut LeanObject,
    mut v_sz_2233_: usize,
    mut v_i_2234_: usize,
    mut v_bs_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: usize = 0;
    let mut v___x_2248_: usize = 0;
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v_unused_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = lean_usize_dec_lt(v_i_2234_, v_sz_2233_);
                if v___x_2238_ == 0 {
                    lean_dec_ref(v___x_2232_);
                    lean_dec_ref(v_a_2231_);
                    v___x_2239_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2239_, 0, v_bs_2235_);
                    lean_ctor_set(v___x_2239_, 1, v___y_2236_);
                    return v___x_2239_;
                } else {
                    v_toTreeMap_2240_ = lean_ctor_get(v_a_2231_, 0);
                    v_v_2241_ = lean_array_uget_borrowed(v_bs_2235_, v_i_2234_);
                    v___x_2242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2240_, v_v_2241_);
                    if lean_obj_tag(v___x_2242_) == 1 {
                        v_val_2243_ = lean_ctor_get(v___x_2242_, 0);
                        lean_inc(v_val_2243_);
                        lean_dec_ref_known(v___x_2242_, 1);
                        v_name_2244_ = lean_ctor_get(v_val_2243_, 1);
                        lean_inc(v_name_2244_);
                        lean_dec(v_val_2243_);
                        v___x_2245_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2246_ = lean_array_uset(v_bs_2235_, v_i_2234_, v___x_2245_);
                        v___x_2247_ = 1usize;
                        v___x_2248_ = lean_usize_add(v_i_2234_, v___x_2247_);
                        v___x_2249_ = lean_array_uset(v_bs_x27_2246_, v_i_2234_, v_name_2244_);
                        v_i_2234_ = v___x_2248_;
                        v_bs_2235_ = v___x_2249_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_v_2241_);
                        lean_dec(v___x_2242_);
                        lean_dec_ref(v_bs_2235_);
                        v_isSharedCheck_2267_ = (!lean_is_exclusive(v_a_2231_)) as u8;
                        if v_isSharedCheck_2267_ == 0 {
                            v_unused_2268_ = lean_ctor_get(v_a_2231_, 1);
                            lean_dec(v_unused_2268_);
                            v_unused_2269_ = lean_ctor_get(v_a_2231_, 0);
                            lean_dec(v_unused_2269_);
                            v___x_2252_ = v_a_2231_;
                            v_isShared_2253_ = v_isSharedCheck_2267_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2231_);
                            v___x_2252_ = lean_box(0);
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
                lean_dec_ref(v___x_2256_);
                v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1;
                v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
                v___x_2260_ = 3;
                v___x_2261_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2261_, 0, v___x_2259_);
                lean_ctor_set_uint8(
                    v___x_2261_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2260_,
                );
                v___x_2262_ = lean_array_get_size(v___y_2236_);
                v___x_2263_ = lean_array_push(v___y_2236_, v___x_2261_);
                if v_isShared_2253_ == 0 {
                    lean_ctor_set_tag(v___x_2252_, 1);
                    lean_ctor_set(v___x_2252_, 1, v___x_2263_);
                    lean_ctor_set(v___x_2252_, 0, v___x_2262_);
                    v___x_2265_ = v___x_2252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2262_);
                    lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2263_);
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
    mut v_a_2270_: *mut LeanObject,
    mut v___x_2271_: *mut LeanObject,
    mut v_sz_2272_: *mut LeanObject,
    mut v_i_2273_: *mut LeanObject,
    mut v_bs_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2277_: usize = 0;
    let mut v_i_boxed_2278_: usize = 0;
    let mut v_res_2279_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2272_);
    lean_dec(v_sz_2272_);
    v_i_boxed_2278_ = lean_unbox_usize(v_i_2273_);
    lean_dec(v_i_2273_);
    v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_2270_, v___x_2271_, v_sz_boxed_2277_, v_i_boxed_2278_, v_bs_2274_, v___y_2275_);
    return v_res_2279_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(
    mut v_f_2280_: *mut LeanObject,
    mut v_as_2281_: *mut LeanObject,
    mut v_i_2282_: usize,
    mut v_stop_2283_: usize,
    mut v_b_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_a_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: usize = 0;
    let mut v___x_2300_: usize = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2285_ = lean_usize_dec_eq(v_i_2282_, v_stop_2283_);
                if v___x_2285_ == 0 {
                    v___x_2286_ = lean_array_uget_borrowed(v_as_2281_, v_i_2282_);
                    lean_inc_ref(v_f_2280_);
                    lean_inc(v___x_2286_);
                    v___x_2287_ = lean_apply_1(v_f_2280_, v___x_2286_);
                    if lean_obj_tag(v___x_2287_) == 0 {
                        lean_dec_ref(v_b_2284_);
                        lean_dec_ref(v_f_2280_);
                        v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
                        v_isSharedCheck_2295_ = (!lean_is_exclusive(v___x_2287_)) as u8;
                        if v_isSharedCheck_2295_ == 0 {
                            v___x_2290_ = v___x_2287_;
                            v_isShared_2291_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2288_);
                            lean_dec(v___x_2287_);
                            v___x_2290_ = lean_box(0);
                            v_isShared_2291_ = v_isSharedCheck_2295_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2296_ = lean_ctor_get(v___x_2287_, 0);
                        lean_inc(v_a_2296_);
                        lean_dec_ref_known(v___x_2287_, 1);
                        v___x_2297_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0;
                        lean_inc(v___x_2286_);
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
                    lean_dec_ref(v_f_2280_);
                    v___x_2302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2302_, 0, v_b_2284_);
                    return v___x_2302_;
                }
            }
            1 => {
                if v_isShared_2291_ == 0 {
                    v___x_2293_ = v___x_2290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
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
    mut v_f_2303_: *mut LeanObject,
    mut v_as_2304_: *mut LeanObject,
    mut v_i_2305_: *mut LeanObject,
    mut v_stop_2306_: *mut LeanObject,
    mut v_b_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2308_: usize = 0;
    let mut v_stop_boxed_2309_: usize = 0;
    let mut v_res_2310_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2308_ = lean_unbox_usize(v_i_2305_);
    lean_dec(v_i_2305_);
    v_stop_boxed_2309_ = lean_unbox_usize(v_stop_2306_);
    lean_dec(v_stop_2306_);
    v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2303_, v_as_2304_, v_i_boxed_2308_, v_stop_boxed_2309_, v_b_2307_);
    lean_dec_ref(v_as_2304_);
    return v_res_2310_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(
    mut v_env_2311_: *mut LeanObject,
    mut v_attr_2312_: *mut LeanObject,
    mut v_f_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_entries_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    v_entries_2314_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_2312_, v_env_2311_);
    v___x_2315_ = lean_array_get_size(v_entries_2314_);
    v___x_2316_ = l_Lake_RBArray_mkEmpty___redArg(v___x_2315_);
    v___x_2317_ = lean_unsigned_to_nat(0);
    v___x_2318_ = lean_nat_dec_lt(v___x_2317_, v___x_2315_);
    if v___x_2318_ == 0 {
        let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_entries_2314_);
        lean_dec_ref(v_f_2313_);
        v___x_2319_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2319_, 0, v___x_2316_);
        return v___x_2319_;
    } else {
        let mut v___x_2320_: u8 = 0;
        v___x_2320_ = lean_nat_dec_le(v___x_2315_, v___x_2315_);
        if v___x_2320_ == 0 {
            if v___x_2318_ == 0 {
                let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_entries_2314_);
                lean_dec_ref(v_f_2313_);
                v___x_2321_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2321_, 0, v___x_2316_);
                return v___x_2321_;
            } else {
                let mut v___x_2322_: usize = 0;
                let mut v___x_2323_: usize = 0;
                let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
                v___x_2322_ = 0usize;
                v___x_2323_ = lean_usize_of_nat(v___x_2315_);
                v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2313_, v_entries_2314_, v___x_2322_, v___x_2323_, v___x_2316_);
                lean_dec_ref(v_entries_2314_);
                return v___x_2324_;
            }
        } else {
            let mut v___x_2325_: usize = 0;
            let mut v___x_2326_: usize = 0;
            let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
            v___x_2325_ = 0usize;
            v___x_2326_ = lean_usize_of_nat(v___x_2315_);
            v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_2313_, v_entries_2314_, v___x_2325_, v___x_2326_, v___x_2316_);
            lean_dec_ref(v_entries_2314_);
            return v___x_2327_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(
    mut v_env_2328_: *mut LeanObject,
    mut v_attr_2329_: *mut LeanObject,
    mut v_f_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_2328_, v_attr_2329_, v_f_2330_);
    lean_dec_ref(v_attr_2329_);
    return v_res_2331_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(
    mut v_f_2332_: *mut LeanObject,
    mut v_as_2333_: *mut LeanObject,
    mut v_i_2334_: usize,
    mut v_stop_2335_: usize,
    mut v_b_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: usize = 0;
    let mut v___x_2346_: usize = 0;
    let mut v_a_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2339_ = lean_usize_dec_eq(v_i_2334_, v_stop_2335_);
                if v___x_2339_ == 0 {
                    v___x_2340_ = lean_array_uget_borrowed(v_as_2333_, v_i_2334_);
                    lean_inc_ref(v_f_2332_);
                    lean_inc(v___x_2340_);
                    v___x_2341_ = lean_apply_3(v_f_2332_, v___x_2340_, v___y_2337_, lean_box(0));
                    if lean_obj_tag(v___x_2341_) == 0 {
                        v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
                        lean_inc(v_a_2342_);
                        v_a_2343_ = lean_ctor_get(v___x_2341_, 1);
                        lean_inc(v_a_2343_);
                        lean_dec_ref_known(v___x_2341_, 2);
                        lean_inc(v___x_2340_);
                        v___x_2344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2340_, v_a_2342_, v_b_2336_);
                        v___x_2345_ = 1usize;
                        v___x_2346_ = lean_usize_add(v_i_2334_, v___x_2345_);
                        v_i_2334_ = v___x_2346_;
                        v_b_2336_ = v___x_2344_;
                        v___y_2337_ = v_a_2343_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_b_2336_);
                        lean_dec_ref(v_f_2332_);
                        v_a_2348_ = lean_ctor_get(v___x_2341_, 0);
                        v_a_2349_ = lean_ctor_get(v___x_2341_, 1);
                        v_isSharedCheck_2356_ = (!lean_is_exclusive(v___x_2341_)) as u8;
                        if v_isSharedCheck_2356_ == 0 {
                            v___x_2351_ = v___x_2341_;
                            v_isShared_2352_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2349_);
                            lean_inc(v_a_2348_);
                            lean_dec(v___x_2341_);
                            v___x_2351_ = lean_box(0);
                            v_isShared_2352_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_2332_);
                    v___x_2357_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2357_, 0, v_b_2336_);
                    lean_ctor_set(v___x_2357_, 1, v___y_2337_);
                    return v___x_2357_;
                }
            }
            1 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2348_);
                    lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_a_2349_);
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
    mut v_f_2358_: *mut LeanObject,
    mut v_as_2359_: *mut LeanObject,
    mut v_i_2360_: *mut LeanObject,
    mut v_stop_2361_: *mut LeanObject,
    mut v_b_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2365_: usize = 0;
    let mut v_stop_boxed_2366_: usize = 0;
    let mut v_res_2367_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2365_ = lean_unbox_usize(v_i_2360_);
    lean_dec(v_i_2360_);
    v_stop_boxed_2366_ = lean_unbox_usize(v_stop_2361_);
    lean_dec(v_stop_2361_);
    v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2358_, v_as_2359_, v_i_boxed_2365_, v_stop_boxed_2366_, v_b_2362_, v___y_2363_);
    lean_dec_ref(v_as_2359_);
    return v_res_2367_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(
    mut v_env_2368_: *mut LeanObject,
    mut v_attr_2369_: *mut LeanObject,
    mut v_f_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_entries_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    v_entries_2373_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_2369_, v_env_2368_);
    v___x_2374_ = lean_box(1);
    v___x_2375_ = lean_unsigned_to_nat(0);
    v___x_2376_ = lean_array_get_size(v_entries_2373_);
    v___x_2377_ = lean_nat_dec_lt(v___x_2375_, v___x_2376_);
    if v___x_2377_ == 0 {
        let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_entries_2373_);
        lean_dec_ref(v_f_2370_);
        v___x_2378_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2378_, 0, v___x_2374_);
        lean_ctor_set(v___x_2378_, 1, v___y_2371_);
        return v___x_2378_;
    } else {
        let mut v___x_2379_: u8 = 0;
        v___x_2379_ = lean_nat_dec_le(v___x_2376_, v___x_2376_);
        if v___x_2379_ == 0 {
            if v___x_2377_ == 0 {
                let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_entries_2373_);
                lean_dec_ref(v_f_2370_);
                v___x_2380_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2380_, 0, v___x_2374_);
                lean_ctor_set(v___x_2380_, 1, v___y_2371_);
                return v___x_2380_;
            } else {
                let mut v___x_2381_: usize = 0;
                let mut v___x_2382_: usize = 0;
                let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
                v___x_2381_ = 0usize;
                v___x_2382_ = lean_usize_of_nat(v___x_2376_);
                v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2370_, v_entries_2373_, v___x_2381_, v___x_2382_, v___x_2374_, v___y_2371_);
                lean_dec_ref(v_entries_2373_);
                return v___x_2383_;
            }
        } else {
            let mut v___x_2384_: usize = 0;
            let mut v___x_2385_: usize = 0;
            let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
            v___x_2384_ = 0usize;
            v___x_2385_ = lean_usize_of_nat(v___x_2376_);
            v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_2370_, v_entries_2373_, v___x_2384_, v___x_2385_, v___x_2374_, v___y_2371_);
            lean_dec_ref(v_entries_2373_);
            return v___x_2386_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(
    mut v_env_2387_: *mut LeanObject,
    mut v_attr_2388_: *mut LeanObject,
    mut v_f_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2392_: *mut LeanObject = core::ptr::null_mut();
    v_res_2392_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_2387_, v_attr_2388_, v_f_2389_, v___y_2390_);
    lean_dec_ref(v_attr_2388_);
    return v_res_2392_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(
    mut v_env_2393_: *mut LeanObject,
    mut v_opts_2394_: *mut LeanObject,
    mut v_as_2395_: *mut LeanObject,
    mut v_sz_2396_: usize,
    mut v_i_2397_: usize,
    mut v_b_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_a_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: usize = 0;
    let mut v___x_2422_: usize = 0;
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = lean_usize_dec_lt(v_i_2397_, v_sz_2396_);
                if v___x_2399_ == 0 {
                    lean_dec_ref(v_env_2393_);
                    v___x_2400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2400_, 0, v_b_2398_);
                    return v___x_2400_;
                } else {
                    v___x_2401_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
                    v_a_2402_ = lean_array_uget_borrowed(v_as_2395_, v_i_2397_);
                    lean_inc(v_a_2402_);
                    lean_inc_ref(v_env_2393_);
                    v___x_2403_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2393_,
                            v_opts_2394_,
                            v___x_2401_,
                            v_a_2402_,
                        );
                    if lean_obj_tag(v___x_2403_) == 0 {
                        lean_dec_ref(v_b_2398_);
                        lean_dec_ref(v_env_2393_);
                        v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2411_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2406_ = v___x_2403_;
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2404_);
                            lean_dec(v___x_2403_);
                            v___x_2406_ = lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2412_ = lean_ctor_get(v___x_2403_, 0);
                        lean_inc(v_a_2412_);
                        lean_dec_ref_known(v___x_2403_, 1);
                        v_name_2413_ = lean_ctor_get(v_a_2412_, 0);
                        v_config_2414_ = lean_ctor_get(v_a_2412_, 1);
                        v_isSharedCheck_2425_ = (!lean_is_exclusive(v_a_2412_)) as u8;
                        if v_isSharedCheck_2425_ == 0 {
                            v___x_2416_ = v_a_2412_;
                            v_isShared_2417_ = v_isSharedCheck_2425_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_config_2414_);
                            lean_inc(v_name_2413_);
                            lean_dec(v_a_2412_);
                            v___x_2416_ = lean_box(0);
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
                    v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
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
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_name_2413_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_config_2414_);
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
    mut v_env_2426_: *mut LeanObject,
    mut v_opts_2427_: *mut LeanObject,
    mut v_as_2428_: *mut LeanObject,
    mut v_sz_2429_: *mut LeanObject,
    mut v_i_2430_: *mut LeanObject,
    mut v_b_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2432_: usize = 0;
    let mut v_i_boxed_2433_: usize = 0;
    let mut v_res_2434_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2432_ = lean_unbox_usize(v_sz_2429_);
    lean_dec(v_sz_2429_);
    v_i_boxed_2433_ = lean_unbox_usize(v_i_2430_);
    lean_dec(v_i_2430_);
    v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_2426_, v_opts_2427_, v_as_2428_, v_sz_boxed_2432_, v_i_boxed_2433_, v_b_2431_);
    lean_dec_ref(v_as_2428_);
    lean_dec_ref(v_opts_2427_);
    return v_res_2434_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(
    mut v___x_2438_: *mut LeanObject,
    mut v_as_2439_: *mut LeanObject,
    mut v_i_2440_: usize,
    mut v_stop_2441_: usize,
    mut v_b_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: usize = 0;
    let mut v___x_2449_: usize = 0;
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v_root_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2451_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
                if v___x_2451_ == 0 {
                    v___x_2452_ = lean_array_uget_borrowed(v_as_2439_, v_i_2440_);
                    v_name_2453_ = lean_ctor_get(v___x_2452_, 1);
                    v_kind_2454_ = lean_ctor_get(v___x_2452_, 2);
                    v_config_2455_ = lean_ctor_get(v___x_2452_, 3);
                    v___x_2456_ = l_Lake_LeanExe_keyword;
                    v___x_2457_ = lean_name_eq(v_kind_2454_, v___x_2456_);
                    if v___x_2457_ == 0 {
                        v_a_2446_ = v_b_2442_;
                        v_a_2447_ = v___y_2443_;
                        state = 1;
                        continue;
                    } else {
                        v_root_2458_ = lean_ctor_get(v_config_2455_, 2);
                        v___x_2459_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_b_2442_, v_root_2458_);
                        if lean_obj_tag(v___x_2459_) == 1 {
                            lean_dec(v_b_2442_);
                            v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
                            lean_inc(v_val_2460_);
                            lean_dec_ref_known(v___x_2459_, 1);
                            v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__0;
                            v___x_2462_ = lean_string_append(v___x_2438_, v___x_2461_);
                            lean_inc(v_name_2453_);
                            v___x_2463_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_name_2453_,
                                    v___x_2457_,
                                );
                            v___x_2464_ = lean_string_append(v___x_2462_, v___x_2463_);
                            lean_dec_ref(v___x_2463_);
                            v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__1;
                            v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
                            lean_inc(v_root_2458_);
                            v___x_2467_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_root_2458_,
                                    v___x_2457_,
                                );
                            v___x_2468_ = lean_string_append(v___x_2466_, v___x_2467_);
                            lean_dec_ref(v___x_2467_);
                            v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___closed__2;
                            v___x_2470_ = lean_string_append(v___x_2468_, v___x_2469_);
                            v___x_2471_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_val_2460_,
                                    v___x_2457_,
                                );
                            v___x_2472_ = lean_string_append(v___x_2470_, v___x_2471_);
                            lean_dec_ref(v___x_2471_);
                            v___x_2473_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                            v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
                            v___x_2475_ = 3;
                            v___x_2476_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_2476_, 0, v___x_2474_);
                            lean_ctor_set_uint8(
                                v___x_2476_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_2475_,
                            );
                            v___x_2477_ = lean_array_get_size(v___y_2443_);
                            v___x_2478_ = lean_array_push(v___y_2443_, v___x_2476_);
                            v___x_2479_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2479_, 0, v___x_2477_);
                            lean_ctor_set(v___x_2479_, 1, v___x_2478_);
                            return v___x_2479_;
                        } else {
                            lean_dec(v___x_2459_);
                            lean_inc(v_name_2453_);
                            lean_inc(v_root_2458_);
                            v___x_2480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_2458_, v_name_2453_, v_b_2442_);
                            v_a_2446_ = v___x_2480_;
                            v_a_2447_ = v___y_2443_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2438_);
                    v___x_2481_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2481_, 0, v_b_2442_);
                    lean_ctor_set(v___x_2481_, 1, v___y_2443_);
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
    mut v___x_2482_: *mut LeanObject,
    mut v_as_2483_: *mut LeanObject,
    mut v_i_2484_: *mut LeanObject,
    mut v_stop_2485_: *mut LeanObject,
    mut v_b_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2489_: usize = 0;
    let mut v_stop_boxed_2490_: usize = 0;
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2489_ = lean_unbox_usize(v_i_2484_);
    lean_dec(v_i_2484_);
    v_stop_boxed_2490_ = lean_unbox_usize(v_stop_2485_);
    lean_dec(v_stop_2485_);
    v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_2482_, v_as_2483_, v_i_boxed_2489_, v_stop_boxed_2490_, v_b_2486_, v___y_2487_);
    lean_dec_ref(v_as_2483_);
    return v_res_2491_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v___x_2496_: *mut LeanObject,
    mut v_sz_2497_: usize,
    mut v_i_2498_: usize,
    mut v_bs_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: usize = 0;
    let mut v___x_2512_: usize = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_unused_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2502_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
                if v___x_2502_ == 0 {
                    lean_dec_ref(v___x_2496_);
                    lean_dec_ref(v_a_2494_);
                    v___x_2503_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2503_, 0, v_bs_2499_);
                    lean_ctor_set(v___x_2503_, 1, v___y_2500_);
                    return v___x_2503_;
                } else {
                    v_toTreeMap_2504_ = lean_ctor_get(v_a_2494_, 0);
                    v_v_2505_ = lean_array_uget(v_bs_2499_, v_i_2498_);
                    v___x_2506_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2507_ = lean_array_uset(v_bs_2499_, v_i_2498_, v___x_2506_);
                    v___x_2515_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2504_, v_v_2505_);
                    if lean_obj_tag(v___x_2515_) == 1 {
                        lean_dec(v_v_2505_);
                        v_val_2516_ = lean_ctor_get(v___x_2515_, 0);
                        lean_inc(v_val_2516_);
                        lean_dec_ref_known(v___x_2515_, 1);
                        v_name_2517_ = lean_ctor_get(v_val_2516_, 1);
                        lean_inc(v_name_2517_);
                        lean_dec(v_val_2516_);
                        v_a_2509_ = v_name_2517_;
                        v_a_2510_ = v___y_2500_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2515_);
                        v___x_2518_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_2505_, v_a_2495_);
                        if v___x_2518_ == 0 {
                            lean_dec_ref(v_bs_x27_2507_);
                            v_isSharedCheck_2535_ = (!lean_is_exclusive(v_a_2494_)) as u8;
                            if v_isSharedCheck_2535_ == 0 {
                                v_unused_2536_ = lean_ctor_get(v_a_2494_, 1);
                                lean_dec(v_unused_2536_);
                                v_unused_2537_ = lean_ctor_get(v_a_2494_, 0);
                                lean_dec(v_unused_2537_);
                                v___x_2520_ = v_a_2494_;
                                v_isShared_2521_ = v_isSharedCheck_2535_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2494_);
                                v___x_2520_ = lean_box(0);
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
                lean_dec_ref(v___x_2524_);
                v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1;
                v___x_2527_ = lean_string_append(v___x_2525_, v___x_2526_);
                v___x_2528_ = 3;
                v___x_2529_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2529_, 0, v___x_2527_);
                lean_ctor_set_uint8(
                    v___x_2529_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2528_,
                );
                v___x_2530_ = lean_array_get_size(v___y_2500_);
                v___x_2531_ = lean_array_push(v___y_2500_, v___x_2529_);
                if v_isShared_2521_ == 0 {
                    lean_ctor_set_tag(v___x_2520_, 1);
                    lean_ctor_set(v___x_2520_, 1, v___x_2531_);
                    lean_ctor_set(v___x_2520_, 0, v___x_2530_);
                    v___x_2533_ = v___x_2520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2530_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2531_);
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
    mut v_a_2538_: *mut LeanObject,
    mut v_a_2539_: *mut LeanObject,
    mut v___x_2540_: *mut LeanObject,
    mut v_sz_2541_: *mut LeanObject,
    mut v_i_2542_: *mut LeanObject,
    mut v_bs_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2546_: usize = 0;
    let mut v_i_boxed_2547_: usize = 0;
    let mut v_res_2548_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2546_ = lean_unbox_usize(v_sz_2541_);
    lean_dec(v_sz_2541_);
    v_i_boxed_2547_ = lean_unbox_usize(v_i_2542_);
    lean_dec(v_i_2542_);
    v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_2538_, v_a_2539_, v___x_2540_, v_sz_boxed_2546_, v_i_boxed_2547_, v_bs_2543_, v___y_2544_);
    lean_dec(v_a_2539_);
    return v_res_2548_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v___x_2552_: *mut LeanObject,
    mut v_sz_2553_: usize,
    mut v_i_2554_: usize,
    mut v_bs_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: usize = 0;
    let mut v___x_2568_: usize = 0;
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_unused_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2558_ = lean_usize_dec_lt(v_i_2554_, v_sz_2553_);
                if v___x_2558_ == 0 {
                    lean_dec_ref(v___x_2552_);
                    lean_dec_ref(v_a_2550_);
                    v___x_2559_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2559_, 0, v_bs_2555_);
                    lean_ctor_set(v___x_2559_, 1, v___y_2556_);
                    return v___x_2559_;
                } else {
                    v_toTreeMap_2560_ = lean_ctor_get(v_a_2550_, 0);
                    v_v_2561_ = lean_array_uget(v_bs_2555_, v_i_2554_);
                    v___x_2562_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2563_ = lean_array_uset(v_bs_2555_, v_i_2554_, v___x_2562_);
                    v___x_2571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_2560_, v_v_2561_);
                    if lean_obj_tag(v___x_2571_) == 1 {
                        lean_dec(v_v_2561_);
                        v_val_2572_ = lean_ctor_get(v___x_2571_, 0);
                        lean_inc(v_val_2572_);
                        lean_dec_ref_known(v___x_2571_, 1);
                        v_name_2573_ = lean_ctor_get(v_val_2572_, 1);
                        lean_inc(v_name_2573_);
                        lean_dec(v_val_2572_);
                        v_a_2565_ = v_name_2573_;
                        v_a_2566_ = v___y_2556_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2571_);
                        v___x_2574_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_2561_, v_a_2551_);
                        if v___x_2574_ == 0 {
                            lean_dec_ref(v_bs_x27_2563_);
                            v_isSharedCheck_2591_ = (!lean_is_exclusive(v_a_2550_)) as u8;
                            if v_isSharedCheck_2591_ == 0 {
                                v_unused_2592_ = lean_ctor_get(v_a_2550_, 1);
                                lean_dec(v_unused_2592_);
                                v_unused_2593_ = lean_ctor_get(v_a_2550_, 0);
                                lean_dec(v_unused_2593_);
                                v___x_2576_ = v_a_2550_;
                                v_isShared_2577_ = v_isSharedCheck_2591_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2550_);
                                v___x_2576_ = lean_box(0);
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
                lean_dec_ref(v___x_2580_);
                v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___closed__0;
                v___x_2583_ = lean_string_append(v___x_2581_, v___x_2582_);
                v___x_2584_ = 3;
                v___x_2585_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2585_, 0, v___x_2583_);
                lean_ctor_set_uint8(
                    v___x_2585_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2584_,
                );
                v___x_2586_ = lean_array_get_size(v___y_2556_);
                v___x_2587_ = lean_array_push(v___y_2556_, v___x_2585_);
                if v_isShared_2577_ == 0 {
                    lean_ctor_set_tag(v___x_2576_, 1);
                    lean_ctor_set(v___x_2576_, 1, v___x_2587_);
                    lean_ctor_set(v___x_2576_, 0, v___x_2586_);
                    v___x_2589_ = v___x_2576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2586_);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2587_);
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
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
    mut v___x_2596_: *mut LeanObject,
    mut v_sz_2597_: *mut LeanObject,
    mut v_i_2598_: *mut LeanObject,
    mut v_bs_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2602_: usize = 0;
    let mut v_i_boxed_2603_: usize = 0;
    let mut v_res_2604_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2602_ = lean_unbox_usize(v_sz_2597_);
    lean_dec(v_sz_2597_);
    v_i_boxed_2603_ = lean_unbox_usize(v_i_2598_);
    lean_dec(v_i_2598_);
    v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_2594_, v_a_2595_, v___x_2596_, v_sz_boxed_2602_, v_i_boxed_2603_, v_bs_2599_, v___y_2600_);
    lean_dec(v_a_2595_);
    return v_res_2604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(
    mut v_a_2606_: *mut LeanObject,
    mut v___x_2607_: *mut LeanObject,
    mut v_sz_2608_: usize,
    mut v_i_2609_: usize,
    mut v_bs_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2613_ = lean_usize_dec_lt(v_i_2609_, v_sz_2608_);
                if v___x_2613_ == 0 {
                    lean_dec_ref(v___x_2607_);
                    v___x_2614_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2614_, 0, v_bs_2610_);
                    lean_ctor_set(v___x_2614_, 1, v___y_2611_);
                    return v___x_2614_;
                } else {
                    v_v_2615_ = lean_array_uget_borrowed(v_bs_2610_, v_i_2609_);
                    v___x_2616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_2606_, v_v_2615_);
                    if lean_obj_tag(v___x_2616_) == 1 {
                        v_val_2617_ = lean_ctor_get(v___x_2616_, 0);
                        lean_inc(v_val_2617_);
                        lean_dec_ref_known(v___x_2616_, 1);
                        v___x_2618_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2619_ = lean_array_uset(v_bs_2610_, v_i_2609_, v___x_2618_);
                        v___x_2620_ = 1usize;
                        v___x_2621_ = lean_usize_add(v_i_2609_, v___x_2620_);
                        v___x_2622_ = lean_array_uset(v_bs_x27_2619_, v_i_2609_, v_val_2617_);
                        v_i_2609_ = v___x_2621_;
                        v_bs_2610_ = v___x_2622_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_v_2615_);
                        lean_dec(v___x_2616_);
                        lean_dec_ref(v_bs_2610_);
                        v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0;
                        v___x_2625_ = lean_string_append(v___x_2607_, v___x_2624_);
                        v___x_2626_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_v_2615_,
                                v___x_2613_,
                            );
                        v___x_2627_ = lean_string_append(v___x_2625_, v___x_2626_);
                        lean_dec_ref(v___x_2626_);
                        v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1;
                        v___x_2629_ = lean_string_append(v___x_2627_, v___x_2628_);
                        v___x_2630_ = 3;
                        v___x_2631_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2631_, 0, v___x_2629_);
                        lean_ctor_set_uint8(
                            v___x_2631_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2630_,
                        );
                        v___x_2632_ = lean_array_get_size(v___y_2611_);
                        v___x_2633_ = lean_array_push(v___y_2611_, v___x_2631_);
                        v___x_2634_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2634_, 0, v___x_2632_);
                        lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                        return v___x_2634_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(
    mut v_a_2635_: *mut LeanObject,
    mut v___x_2636_: *mut LeanObject,
    mut v_sz_2637_: *mut LeanObject,
    mut v_i_2638_: *mut LeanObject,
    mut v_bs_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2642_: usize = 0;
    let mut v_i_boxed_2643_: usize = 0;
    let mut v_res_2644_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2642_ = lean_unbox_usize(v_sz_2637_);
    lean_dec(v_sz_2637_);
    v_i_boxed_2643_ = lean_unbox_usize(v_i_2638_);
    lean_dec(v_i_2638_);
    v_res_2644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_2635_, v___x_2636_, v_sz_boxed_2642_, v_i_boxed_2643_, v_bs_2639_, v___y_2640_);
    lean_dec(v_a_2635_);
    return v_res_2644_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(
    mut v_env_2645_: *mut LeanObject,
    mut v_opts_2646_: *mut LeanObject,
    mut v_sz_2647_: usize,
    mut v_i_2648_: usize,
    mut v_bs_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_a_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: usize = 0;
    let mut v___x_2667_: usize = 0;
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2650_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
                if v___x_2650_ == 0 {
                    lean_dec_ref(v_env_2645_);
                    v___x_2651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2651_, 0, v_bs_2649_);
                    return v___x_2651_;
                } else {
                    v___x_2652_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
                    v_v_2653_ = lean_array_uget_borrowed(v_bs_2649_, v_i_2648_);
                    lean_inc(v_v_2653_);
                    lean_inc_ref(v_env_2645_);
                    v___x_2654_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2645_,
                            v_opts_2646_,
                            v___x_2652_,
                            v_v_2653_,
                        );
                    if lean_obj_tag(v___x_2654_) == 0 {
                        lean_dec_ref(v_bs_2649_);
                        lean_dec_ref(v_env_2645_);
                        v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
                        v_isSharedCheck_2662_ = (!lean_is_exclusive(v___x_2654_)) as u8;
                        if v_isSharedCheck_2662_ == 0 {
                            v___x_2657_ = v___x_2654_;
                            v_isShared_2658_ = v_isSharedCheck_2662_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2655_);
                            lean_dec(v___x_2654_);
                            v___x_2657_ = lean_box(0);
                            v_isShared_2658_ = v_isSharedCheck_2662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2663_ = lean_ctor_get(v___x_2654_, 0);
                        lean_inc(v_a_2663_);
                        lean_dec_ref_known(v___x_2654_, 1);
                        v___x_2664_ = lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
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
    mut v_env_2670_: *mut LeanObject,
    mut v_opts_2671_: *mut LeanObject,
    mut v_sz_2672_: *mut LeanObject,
    mut v_i_2673_: *mut LeanObject,
    mut v_bs_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2675_: usize = 0;
    let mut v_i_boxed_2676_: usize = 0;
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2675_ = lean_unbox_usize(v_sz_2672_);
    lean_dec(v_sz_2672_);
    v_i_boxed_2676_ = lean_unbox_usize(v_i_2673_);
    lean_dec(v_i_2673_);
    v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_2670_, v_opts_2671_, v_sz_boxed_2675_, v_i_boxed_2676_, v_bs_2674_);
    lean_dec_ref(v_opts_2671_);
    return v_res_2677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(
    mut v_env_2678_: *mut LeanObject,
    mut v_opts_2679_: *mut LeanObject,
    mut v_as_2680_: *mut LeanObject,
    mut v_sz_2681_: usize,
    mut v_i_2682_: usize,
    mut v_b_2683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_a_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: usize = 0;
    let mut v_reuseFailAlloc_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
                if v___x_2684_ == 0 {
                    lean_dec_ref(v_env_2678_);
                    v___x_2685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2685_, 0, v_b_2683_);
                    return v___x_2685_;
                } else {
                    v___x_2686_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
                    v_a_2687_ = lean_array_uget_borrowed(v_as_2680_, v_i_2682_);
                    lean_inc(v_a_2687_);
                    lean_inc_ref(v_env_2678_);
                    v___x_2688_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2678_,
                            v_opts_2679_,
                            v___x_2686_,
                            v_a_2687_,
                        );
                    if lean_obj_tag(v___x_2688_) == 0 {
                        lean_dec_ref(v_b_2683_);
                        lean_dec_ref(v_env_2678_);
                        v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
                        v_isSharedCheck_2696_ = (!lean_is_exclusive(v___x_2688_)) as u8;
                        if v_isSharedCheck_2696_ == 0 {
                            v___x_2691_ = v___x_2688_;
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2689_);
                            lean_dec(v___x_2688_);
                            v___x_2691_ = lean_box(0);
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2697_ = lean_ctor_get(v___x_2688_, 0);
                        lean_inc(v_a_2697_);
                        lean_dec_ref_known(v___x_2688_, 1);
                        v_name_2698_ = lean_ctor_get(v_a_2697_, 0);
                        v_config_2699_ = lean_ctor_get(v_a_2697_, 1);
                        v_isSharedCheck_2710_ = (!lean_is_exclusive(v_a_2697_)) as u8;
                        if v_isSharedCheck_2710_ == 0 {
                            v___x_2701_ = v_a_2697_;
                            v_isShared_2702_ = v_isSharedCheck_2710_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_config_2699_);
                            lean_inc(v_name_2698_);
                            lean_dec(v_a_2697_);
                            v___x_2701_ = lean_box(0);
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
                    v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
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
                    v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_name_2698_);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_config_2699_);
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
    mut v_env_2711_: *mut LeanObject,
    mut v_opts_2712_: *mut LeanObject,
    mut v_as_2713_: *mut LeanObject,
    mut v_sz_2714_: *mut LeanObject,
    mut v_i_2715_: *mut LeanObject,
    mut v_b_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2717_: usize = 0;
    let mut v_i_boxed_2718_: usize = 0;
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2717_ = lean_unbox_usize(v_sz_2714_);
    lean_dec(v_sz_2714_);
    v_i_boxed_2718_ = lean_unbox_usize(v_i_2715_);
    lean_dec(v_i_2715_);
    v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_2711_, v_opts_2712_, v_as_2713_, v_sz_boxed_2717_, v_i_boxed_2718_, v_b_2716_);
    lean_dec_ref(v_as_2713_);
    lean_dec_ref(v_opts_2712_);
    return v_res_2719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(
    mut v_env_2720_: *mut LeanObject,
    mut v_opts_2721_: *mut LeanObject,
    mut v_as_2722_: *mut LeanObject,
    mut v_sz_2723_: usize,
    mut v_i_2724_: usize,
    mut v_b_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: usize = 0;
    let mut v___x_2749_: usize = 0;
    let mut v_reuseFailAlloc_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2726_ = lean_usize_dec_lt(v_i_2724_, v_sz_2723_);
                if v___x_2726_ == 0 {
                    lean_dec_ref(v_env_2720_);
                    v___x_2727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2727_, 0, v_b_2725_);
                    return v___x_2727_;
                } else {
                    v___x_2728_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
                    v_a_2729_ = lean_array_uget_borrowed(v_as_2722_, v_i_2724_);
                    lean_inc(v_a_2729_);
                    lean_inc_ref(v_env_2720_);
                    v___x_2730_ =
                        l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(
                            v_env_2720_,
                            v_opts_2721_,
                            v___x_2728_,
                            v_a_2729_,
                        );
                    if lean_obj_tag(v___x_2730_) == 0 {
                        lean_dec_ref(v_b_2725_);
                        lean_dec_ref(v_env_2720_);
                        v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
                        v_isSharedCheck_2738_ = (!lean_is_exclusive(v___x_2730_)) as u8;
                        if v_isSharedCheck_2738_ == 0 {
                            v___x_2733_ = v___x_2730_;
                            v_isShared_2734_ = v_isSharedCheck_2738_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2731_);
                            lean_dec(v___x_2730_);
                            v___x_2733_ = lean_box(0);
                            v_isShared_2734_ = v_isSharedCheck_2738_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2739_ = lean_ctor_get(v___x_2730_, 0);
                        lean_inc(v_a_2739_);
                        lean_dec_ref_known(v___x_2730_, 1);
                        v_name_2740_ = lean_ctor_get(v_a_2739_, 0);
                        v_config_2741_ = lean_ctor_get(v_a_2739_, 1);
                        v_isSharedCheck_2752_ = (!lean_is_exclusive(v_a_2739_)) as u8;
                        if v_isSharedCheck_2752_ == 0 {
                            v___x_2743_ = v_a_2739_;
                            v_isShared_2744_ = v_isSharedCheck_2752_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_config_2741_);
                            lean_inc(v_name_2740_);
                            lean_dec(v_a_2739_);
                            v___x_2743_ = lean_box(0);
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
                    v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
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
                    v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_name_2740_);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_config_2741_);
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
    mut v_env_2753_: *mut LeanObject,
    mut v_opts_2754_: *mut LeanObject,
    mut v_as_2755_: *mut LeanObject,
    mut v_sz_2756_: *mut LeanObject,
    mut v_i_2757_: *mut LeanObject,
    mut v_b_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2759_: usize = 0;
    let mut v_i_boxed_2760_: usize = 0;
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2759_ = lean_unbox_usize(v_sz_2756_);
    lean_dec(v_sz_2756_);
    v_i_boxed_2760_ = lean_unbox_usize(v_i_2757_);
    lean_dec(v_i_2757_);
    v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_2753_, v_opts_2754_, v_as_2755_, v_sz_boxed_2759_, v_i_boxed_2760_, v_b_2758_);
    lean_dec_ref(v_as_2755_);
    lean_dec_ref(v_opts_2754_);
    return v_res_2761_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(
    mut v_t_2762_: *mut LeanObject,
    mut v_k_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2762_) == 0 {
                    v_k_2764_ = lean_ctor_get(v_t_2762_, 1);
                    v_v_2765_ = lean_ctor_get(v_t_2762_, 2);
                    v_l_2766_ = lean_ctor_get(v_t_2762_, 3);
                    v_r_2767_ = lean_ctor_get(v_t_2762_, 4);
                    v___x_2768_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2763_, v_k_2764_);
                    match v___x_2768_ {
                        0 => {
                            v_t_2762_ = v_l_2766_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2765_);
                            v___x_2770_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2770_, 0, v_v_2765_);
                            return v___x_2770_;
                        }
                        _ => {
                            v_t_2762_ = v_r_2767_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2772_ = lean_box(0);
                    return v___x_2772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(
    mut v_t_2773_: *mut LeanObject,
    mut v_k_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2775_: *mut LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_2773_, v_k_2774_);
    lean_dec(v_k_2774_);
    lean_dec(v_t_2773_);
    return v_res_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(
    mut v_k_2776_: *mut LeanObject,
    mut v_v_2777_: *mut LeanObject,
    mut v_t_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2787_: u8 = 0;
    let mut v_impl_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v_size_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_unused_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_unused_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2889_: u8 = 0;
    let mut v_unused_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v_k_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_unused_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_unused_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v_size_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v_unused_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut v_unused_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_unused_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v_k_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_unused_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_unused_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2778_) == 0 {
                    v_size_2779_ = lean_ctor_get(v_t_2778_, 0);
                    v_k_2780_ = lean_ctor_get(v_t_2778_, 1);
                    v_v_2781_ = lean_ctor_get(v_t_2778_, 2);
                    v_l_2782_ = lean_ctor_get(v_t_2778_, 3);
                    v_r_2783_ = lean_ctor_get(v_t_2778_, 4);
                    v_isSharedCheck_3063_ = (!lean_is_exclusive(v_t_2778_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_2785_ = v_t_2778_;
                        v_isShared_2786_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2783_);
                        lean_inc(v_l_2782_);
                        lean_inc(v_v_2781_);
                        lean_inc(v_k_2780_);
                        lean_inc(v_size_2779_);
                        lean_dec(v_t_2778_);
                        v___x_2785_ = lean_box(0);
                        v_isShared_2786_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3064_ = lean_unsigned_to_nat(1);
                    v___x_3065_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3065_, 0, v___x_3064_);
                    lean_ctor_set(v___x_3065_, 1, v_k_2776_);
                    lean_ctor_set(v___x_3065_, 2, v_v_2777_);
                    lean_ctor_set(v___x_3065_, 3, v_t_2778_);
                    lean_ctor_set(v___x_3065_, 4, v_t_2778_);
                    return v___x_3065_;
                }
            }
            1 => {
                v___x_2787_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2776_, v_k_2780_);
                match v___x_2787_ {
                    0 => {
                        lean_dec(v_size_2779_);
                        v_impl_2788_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_2776_, v_v_2777_, v_l_2782_);
                        v___x_2789_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_2783_) == 0 {
                            v_size_2790_ = lean_ctor_get(v_r_2783_, 0);
                            v_size_2791_ = lean_ctor_get(v_impl_2788_, 0);
                            lean_inc(v_size_2791_);
                            v_k_2792_ = lean_ctor_get(v_impl_2788_, 1);
                            lean_inc(v_k_2792_);
                            v_v_2793_ = lean_ctor_get(v_impl_2788_, 2);
                            lean_inc(v_v_2793_);
                            v_l_2794_ = lean_ctor_get(v_impl_2788_, 3);
                            lean_inc(v_l_2794_);
                            v_r_2795_ = lean_ctor_get(v_impl_2788_, 4);
                            lean_inc(v_r_2795_);
                            v___x_2796_ = lean_unsigned_to_nat(3);
                            v___x_2797_ = lean_nat_mul(v___x_2796_, v_size_2790_);
                            v___x_2798_ = lean_nat_dec_lt(v___x_2797_, v_size_2791_);
                            lean_dec(v___x_2797_);
                            if v___x_2798_ == 0 {
                                lean_dec(v_r_2795_);
                                lean_dec(v_l_2794_);
                                lean_dec(v_v_2793_);
                                lean_dec(v_k_2792_);
                                v___x_2799_ = lean_nat_add(v___x_2789_, v_size_2791_);
                                lean_dec(v_size_2791_);
                                v___x_2800_ = lean_nat_add(v___x_2799_, v_size_2790_);
                                lean_dec(v___x_2799_);
                                if v_isShared_2786_ == 0 {
                                    lean_ctor_set(v___x_2785_, 3, v_impl_2788_);
                                    lean_ctor_set(v___x_2785_, 0, v___x_2800_);
                                    v___x_2802_ = v___x_2785_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
                                    lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_k_2780_);
                                    lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_v_2781_);
                                    lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_impl_2788_);
                                    lean_ctor_set(v_reuseFailAlloc_2803_, 4, v_r_2783_);
                                    v___x_2802_ = v_reuseFailAlloc_2803_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2869_ = (!lean_is_exclusive(v_impl_2788_)) as u8;
                                if v_isSharedCheck_2869_ == 0 {
                                    v_unused_2870_ = lean_ctor_get(v_impl_2788_, 4);
                                    lean_dec(v_unused_2870_);
                                    v_unused_2871_ = lean_ctor_get(v_impl_2788_, 3);
                                    lean_dec(v_unused_2871_);
                                    v_unused_2872_ = lean_ctor_get(v_impl_2788_, 2);
                                    lean_dec(v_unused_2872_);
                                    v_unused_2873_ = lean_ctor_get(v_impl_2788_, 1);
                                    lean_dec(v_unused_2873_);
                                    v_unused_2874_ = lean_ctor_get(v_impl_2788_, 0);
                                    lean_dec(v_unused_2874_);
                                    v___x_2805_ = v_impl_2788_;
                                    v_isShared_2806_ = v_isSharedCheck_2869_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2788_);
                                    v___x_2805_ = lean_box(0);
                                    v_isShared_2806_ = v_isSharedCheck_2869_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2875_ = lean_ctor_get(v_impl_2788_, 3);
                            lean_inc(v_l_2875_);
                            if lean_obj_tag(v_l_2875_) == 0 {
                                v_r_2876_ = lean_ctor_get(v_impl_2788_, 4);
                                v_k_2877_ = lean_ctor_get(v_impl_2788_, 1);
                                v_v_2878_ = lean_ctor_get(v_impl_2788_, 2);
                                v_isSharedCheck_2889_ = (!lean_is_exclusive(v_impl_2788_)) as u8;
                                if v_isSharedCheck_2889_ == 0 {
                                    v_unused_2890_ = lean_ctor_get(v_impl_2788_, 3);
                                    lean_dec(v_unused_2890_);
                                    v_unused_2891_ = lean_ctor_get(v_impl_2788_, 0);
                                    lean_dec(v_unused_2891_);
                                    v___x_2880_ = v_impl_2788_;
                                    v_isShared_2881_ = v_isSharedCheck_2889_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_2876_);
                                    lean_inc(v_v_2878_);
                                    lean_inc(v_k_2877_);
                                    lean_dec(v_impl_2788_);
                                    v___x_2880_ = lean_box(0);
                                    v_isShared_2881_ = v_isSharedCheck_2889_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2892_ = lean_ctor_get(v_impl_2788_, 4);
                                lean_inc(v_r_2892_);
                                if lean_obj_tag(v_r_2892_) == 0 {
                                    v_k_2893_ = lean_ctor_get(v_impl_2788_, 1);
                                    v_v_2894_ = lean_ctor_get(v_impl_2788_, 2);
                                    v_isSharedCheck_2917_ =
                                        (!lean_is_exclusive(v_impl_2788_)) as u8;
                                    if v_isSharedCheck_2917_ == 0 {
                                        v_unused_2918_ = lean_ctor_get(v_impl_2788_, 4);
                                        lean_dec(v_unused_2918_);
                                        v_unused_2919_ = lean_ctor_get(v_impl_2788_, 3);
                                        lean_dec(v_unused_2919_);
                                        v_unused_2920_ = lean_ctor_get(v_impl_2788_, 0);
                                        lean_dec(v_unused_2920_);
                                        v___x_2896_ = v_impl_2788_;
                                        v_isShared_2897_ = v_isSharedCheck_2917_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2894_);
                                        lean_inc(v_k_2893_);
                                        lean_dec(v_impl_2788_);
                                        v___x_2896_ = lean_box(0);
                                        v_isShared_2897_ = v_isSharedCheck_2917_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2921_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2786_ == 0 {
                                        lean_ctor_set(v___x_2785_, 4, v_r_2892_);
                                        lean_ctor_set(v___x_2785_, 3, v_impl_2788_);
                                        lean_ctor_set(v___x_2785_, 0, v___x_2921_);
                                        v___x_2923_ = v___x_2785_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
                                        lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_k_2780_);
                                        lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_v_2781_);
                                        lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_impl_2788_);
                                        lean_ctor_set(v_reuseFailAlloc_2924_, 4, v_r_2892_);
                                        v___x_2923_ = v_reuseFailAlloc_2924_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_2781_);
                        lean_dec(v_k_2780_);
                        if v_isShared_2786_ == 0 {
                            lean_ctor_set(v___x_2785_, 2, v_v_2777_);
                            lean_ctor_set(v___x_2785_, 1, v_k_2776_);
                            v___x_2926_ = v___x_2785_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_size_2779_);
                            lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2776_);
                            lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2777_);
                            lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_l_2782_);
                            lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_r_2783_);
                            v___x_2926_ = v_reuseFailAlloc_2927_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_2779_);
                        v_impl_2928_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_2776_, v_v_2777_, v_r_2783_);
                        v___x_2929_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_2782_) == 0 {
                            v_size_2930_ = lean_ctor_get(v_l_2782_, 0);
                            v_size_2931_ = lean_ctor_get(v_impl_2928_, 0);
                            lean_inc(v_size_2931_);
                            v_k_2932_ = lean_ctor_get(v_impl_2928_, 1);
                            lean_inc(v_k_2932_);
                            v_v_2933_ = lean_ctor_get(v_impl_2928_, 2);
                            lean_inc(v_v_2933_);
                            v_l_2934_ = lean_ctor_get(v_impl_2928_, 3);
                            lean_inc(v_l_2934_);
                            v_r_2935_ = lean_ctor_get(v_impl_2928_, 4);
                            lean_inc(v_r_2935_);
                            v___x_2936_ = lean_unsigned_to_nat(3);
                            v___x_2937_ = lean_nat_mul(v___x_2936_, v_size_2930_);
                            v___x_2938_ = lean_nat_dec_lt(v___x_2937_, v_size_2931_);
                            lean_dec(v___x_2937_);
                            if v___x_2938_ == 0 {
                                lean_dec(v_r_2935_);
                                lean_dec(v_l_2934_);
                                lean_dec(v_v_2933_);
                                lean_dec(v_k_2932_);
                                v___x_2939_ = lean_nat_add(v___x_2929_, v_size_2930_);
                                v___x_2940_ = lean_nat_add(v___x_2939_, v_size_2931_);
                                lean_dec(v_size_2931_);
                                lean_dec(v___x_2939_);
                                if v_isShared_2786_ == 0 {
                                    lean_ctor_set(v___x_2785_, 4, v_impl_2928_);
                                    lean_ctor_set(v___x_2785_, 0, v___x_2940_);
                                    v___x_2942_ = v___x_2785_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
                                    lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_k_2780_);
                                    lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_v_2781_);
                                    lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_l_2782_);
                                    lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_impl_2928_);
                                    v___x_2942_ = v_reuseFailAlloc_2943_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3007_ = (!lean_is_exclusive(v_impl_2928_)) as u8;
                                if v_isSharedCheck_3007_ == 0 {
                                    v_unused_3008_ = lean_ctor_get(v_impl_2928_, 4);
                                    lean_dec(v_unused_3008_);
                                    v_unused_3009_ = lean_ctor_get(v_impl_2928_, 3);
                                    lean_dec(v_unused_3009_);
                                    v_unused_3010_ = lean_ctor_get(v_impl_2928_, 2);
                                    lean_dec(v_unused_3010_);
                                    v_unused_3011_ = lean_ctor_get(v_impl_2928_, 1);
                                    lean_dec(v_unused_3011_);
                                    v_unused_3012_ = lean_ctor_get(v_impl_2928_, 0);
                                    lean_dec(v_unused_3012_);
                                    v___x_2945_ = v_impl_2928_;
                                    v_isShared_2946_ = v_isSharedCheck_3007_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2928_);
                                    v___x_2945_ = lean_box(0);
                                    v_isShared_2946_ = v_isSharedCheck_3007_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3013_ = lean_ctor_get(v_impl_2928_, 3);
                            lean_inc(v_l_3013_);
                            if lean_obj_tag(v_l_3013_) == 0 {
                                v_r_3014_ = lean_ctor_get(v_impl_2928_, 4);
                                v_k_3015_ = lean_ctor_get(v_impl_2928_, 1);
                                v_v_3016_ = lean_ctor_get(v_impl_2928_, 2);
                                v_isSharedCheck_3039_ = (!lean_is_exclusive(v_impl_2928_)) as u8;
                                if v_isSharedCheck_3039_ == 0 {
                                    v_unused_3040_ = lean_ctor_get(v_impl_2928_, 3);
                                    lean_dec(v_unused_3040_);
                                    v_unused_3041_ = lean_ctor_get(v_impl_2928_, 0);
                                    lean_dec(v_unused_3041_);
                                    v___x_3018_ = v_impl_2928_;
                                    v_isShared_3019_ = v_isSharedCheck_3039_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_3014_);
                                    lean_inc(v_v_3016_);
                                    lean_inc(v_k_3015_);
                                    lean_dec(v_impl_2928_);
                                    v___x_3018_ = lean_box(0);
                                    v_isShared_3019_ = v_isSharedCheck_3039_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3042_ = lean_ctor_get(v_impl_2928_, 4);
                                lean_inc(v_r_3042_);
                                if lean_obj_tag(v_r_3042_) == 0 {
                                    v_k_3043_ = lean_ctor_get(v_impl_2928_, 1);
                                    v_v_3044_ = lean_ctor_get(v_impl_2928_, 2);
                                    v_isSharedCheck_3055_ =
                                        (!lean_is_exclusive(v_impl_2928_)) as u8;
                                    if v_isSharedCheck_3055_ == 0 {
                                        v_unused_3056_ = lean_ctor_get(v_impl_2928_, 4);
                                        lean_dec(v_unused_3056_);
                                        v_unused_3057_ = lean_ctor_get(v_impl_2928_, 3);
                                        lean_dec(v_unused_3057_);
                                        v_unused_3058_ = lean_ctor_get(v_impl_2928_, 0);
                                        lean_dec(v_unused_3058_);
                                        v___x_3046_ = v_impl_2928_;
                                        v_isShared_3047_ = v_isSharedCheck_3055_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3044_);
                                        lean_inc(v_k_3043_);
                                        lean_dec(v_impl_2928_);
                                        v___x_3046_ = lean_box(0);
                                        v_isShared_3047_ = v_isSharedCheck_3055_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3059_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2786_ == 0 {
                                        lean_ctor_set(v___x_2785_, 4, v_impl_2928_);
                                        lean_ctor_set(v___x_2785_, 3, v_r_3042_);
                                        lean_ctor_set(v___x_2785_, 0, v___x_3059_);
                                        v___x_3061_ = v___x_2785_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
                                        lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_k_2780_);
                                        lean_ctor_set(v_reuseFailAlloc_3062_, 2, v_v_2781_);
                                        lean_ctor_set(v_reuseFailAlloc_3062_, 3, v_r_3042_);
                                        lean_ctor_set(v_reuseFailAlloc_3062_, 4, v_impl_2928_);
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
                v_size_2807_ = lean_ctor_get(v_l_2794_, 0);
                v_size_2808_ = lean_ctor_get(v_r_2795_, 0);
                v_k_2809_ = lean_ctor_get(v_r_2795_, 1);
                v_v_2810_ = lean_ctor_get(v_r_2795_, 2);
                v_l_2811_ = lean_ctor_get(v_r_2795_, 3);
                v_r_2812_ = lean_ctor_get(v_r_2795_, 4);
                v___x_2813_ = lean_unsigned_to_nat(2);
                v___x_2814_ = lean_nat_mul(v___x_2813_, v_size_2807_);
                v___x_2815_ = lean_nat_dec_lt(v_size_2808_, v___x_2814_);
                lean_dec(v___x_2814_);
                if v___x_2815_ == 0 {
                    lean_inc(v_r_2812_);
                    lean_inc(v_l_2811_);
                    lean_inc(v_v_2810_);
                    lean_inc(v_k_2809_);
                    v_isSharedCheck_2844_ = (!lean_is_exclusive(v_r_2795_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v_unused_2845_ = lean_ctor_get(v_r_2795_, 4);
                        lean_dec(v_unused_2845_);
                        v_unused_2846_ = lean_ctor_get(v_r_2795_, 3);
                        lean_dec(v_unused_2846_);
                        v_unused_2847_ = lean_ctor_get(v_r_2795_, 2);
                        lean_dec(v_unused_2847_);
                        v_unused_2848_ = lean_ctor_get(v_r_2795_, 1);
                        lean_dec(v_unused_2848_);
                        v_unused_2849_ = lean_ctor_get(v_r_2795_, 0);
                        lean_dec(v_unused_2849_);
                        v___x_2817_ = v_r_2795_;
                        v_isShared_2818_ = v_isSharedCheck_2844_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_2795_);
                        v___x_2817_ = lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2844_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2785_);
                    v___x_2850_ = lean_nat_add(v___x_2789_, v_size_2791_);
                    lean_dec(v_size_2791_);
                    v___x_2851_ = lean_nat_add(v___x_2850_, v_size_2790_);
                    lean_dec(v___x_2850_);
                    v___x_2852_ = lean_nat_add(v___x_2789_, v_size_2790_);
                    v___x_2853_ = lean_nat_add(v___x_2852_, v_size_2808_);
                    lean_dec(v___x_2852_);
                    lean_inc_ref(v_r_2783_);
                    if v_isShared_2806_ == 0 {
                        lean_ctor_set(v___x_2805_, 4, v_r_2783_);
                        lean_ctor_set(v___x_2805_, 3, v_r_2795_);
                        lean_ctor_set(v___x_2805_, 2, v_v_2781_);
                        lean_ctor_set(v___x_2805_, 1, v_k_2780_);
                        lean_ctor_set(v___x_2805_, 0, v___x_2853_);
                        v___x_2855_ = v___x_2805_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2853_);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_k_2780_);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_v_2781_);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_r_2795_);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_r_2783_);
                        v___x_2855_ = v_reuseFailAlloc_2868_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2819_ = lean_nat_add(v___x_2789_, v_size_2791_);
                lean_dec(v_size_2791_);
                v___x_2820_ = lean_nat_add(v___x_2819_, v_size_2790_);
                lean_dec(v___x_2819_);
                v___x_2832_ = lean_nat_add(v___x_2789_, v_size_2807_);
                if lean_obj_tag(v_l_2811_) == 0 {
                    v_size_2842_ = lean_ctor_get(v_l_2811_, 0);
                    lean_inc(v_size_2842_);
                    v___y_2834_ = v_size_2842_;
                    state = 8;
                    continue;
                } else {
                    v___x_2843_ = lean_unsigned_to_nat(0);
                    v___y_2834_ = v___x_2843_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2825_ = lean_nat_add(v___y_2822_, v___y_2824_);
                lean_dec(v___y_2824_);
                lean_dec(v___y_2822_);
                if v_isShared_2818_ == 0 {
                    lean_ctor_set(v___x_2817_, 4, v_r_2783_);
                    lean_ctor_set(v___x_2817_, 3, v_r_2812_);
                    lean_ctor_set(v___x_2817_, 2, v_v_2781_);
                    lean_ctor_set(v___x_2817_, 1, v_k_2780_);
                    lean_ctor_set(v___x_2817_, 0, v___x_2825_);
                    v___x_2827_ = v___x_2817_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2825_);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_r_2812_);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_r_2783_);
                    v___x_2827_ = v_reuseFailAlloc_2831_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2806_ == 0 {
                    lean_ctor_set(v___x_2805_, 4, v___x_2827_);
                    lean_ctor_set(v___x_2805_, 3, v___y_2823_);
                    lean_ctor_set(v___x_2805_, 2, v_v_2810_);
                    lean_ctor_set(v___x_2805_, 1, v_k_2809_);
                    lean_ctor_set(v___x_2805_, 0, v___x_2820_);
                    v___x_2829_ = v___x_2805_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2820_);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_k_2809_);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_v_2810_);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 3, v___y_2823_);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 4, v___x_2827_);
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
                lean_dec(v___y_2834_);
                lean_dec(v___x_2832_);
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v_l_2811_);
                    lean_ctor_set(v___x_2785_, 3, v_l_2794_);
                    lean_ctor_set(v___x_2785_, 2, v_v_2793_);
                    lean_ctor_set(v___x_2785_, 1, v_k_2792_);
                    lean_ctor_set(v___x_2785_, 0, v___x_2835_);
                    v___x_2837_ = v___x_2785_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_l_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_l_2811_);
                    v___x_2837_ = v_reuseFailAlloc_2841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2838_ = lean_nat_add(v___x_2789_, v_size_2790_);
                if lean_obj_tag(v_r_2812_) == 0 {
                    v_size_2839_ = lean_ctor_get(v_r_2812_, 0);
                    lean_inc(v_size_2839_);
                    v___y_2822_ = v___x_2838_;
                    v___y_2823_ = v___x_2837_;
                    v___y_2824_ = v_size_2839_;
                    state = 5;
                    continue;
                } else {
                    v___x_2840_ = lean_unsigned_to_nat(0);
                    v___y_2822_ = v___x_2838_;
                    v___y_2823_ = v___x_2837_;
                    v___y_2824_ = v___x_2840_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2862_ = (!lean_is_exclusive(v_r_2783_)) as u8;
                if v_isSharedCheck_2862_ == 0 {
                    v_unused_2863_ = lean_ctor_get(v_r_2783_, 4);
                    lean_dec(v_unused_2863_);
                    v_unused_2864_ = lean_ctor_get(v_r_2783_, 3);
                    lean_dec(v_unused_2864_);
                    v_unused_2865_ = lean_ctor_get(v_r_2783_, 2);
                    lean_dec(v_unused_2865_);
                    v_unused_2866_ = lean_ctor_get(v_r_2783_, 1);
                    lean_dec(v_unused_2866_);
                    v_unused_2867_ = lean_ctor_get(v_r_2783_, 0);
                    lean_dec(v_unused_2867_);
                    v___x_2857_ = v_r_2783_;
                    v_isShared_2858_ = v_isSharedCheck_2862_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_2783_);
                    v___x_2857_ = lean_box(0);
                    v_isShared_2858_ = v_isSharedCheck_2862_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2858_ == 0 {
                    lean_ctor_set(v___x_2857_, 4, v___x_2855_);
                    lean_ctor_set(v___x_2857_, 3, v_l_2794_);
                    lean_ctor_set(v___x_2857_, 2, v_v_2793_);
                    lean_ctor_set(v___x_2857_, 1, v_k_2792_);
                    lean_ctor_set(v___x_2857_, 0, v___x_2851_);
                    v___x_2860_ = v___x_2857_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2851_);
                    lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_l_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2861_, 4, v___x_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2861_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2860_;
            }
            13 => {
                v___x_2882_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_2876_);
                if v_isShared_2881_ == 0 {
                    lean_ctor_set(v___x_2880_, 3, v_r_2876_);
                    lean_ctor_set(v___x_2880_, 2, v_v_2781_);
                    lean_ctor_set(v___x_2880_, 1, v_k_2780_);
                    lean_ctor_set(v___x_2880_, 0, v___x_2789_);
                    v___x_2884_ = v___x_2880_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_r_2876_);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 4, v_r_2876_);
                    v___x_2884_ = v_reuseFailAlloc_2888_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v___x_2884_);
                    lean_ctor_set(v___x_2785_, 3, v_l_2875_);
                    lean_ctor_set(v___x_2785_, 2, v_v_2878_);
                    lean_ctor_set(v___x_2785_, 1, v_k_2877_);
                    lean_ctor_set(v___x_2785_, 0, v___x_2882_);
                    v___x_2886_ = v___x_2785_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2882_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_l_2875_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 4, v___x_2884_);
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2886_;
            }
            16 => {
                v_k_2898_ = lean_ctor_get(v_r_2892_, 1);
                v_v_2899_ = lean_ctor_get(v_r_2892_, 2);
                v_isSharedCheck_2913_ = (!lean_is_exclusive(v_r_2892_)) as u8;
                if v_isSharedCheck_2913_ == 0 {
                    v_unused_2914_ = lean_ctor_get(v_r_2892_, 4);
                    lean_dec(v_unused_2914_);
                    v_unused_2915_ = lean_ctor_get(v_r_2892_, 3);
                    lean_dec(v_unused_2915_);
                    v_unused_2916_ = lean_ctor_get(v_r_2892_, 0);
                    lean_dec(v_unused_2916_);
                    v___x_2901_ = v_r_2892_;
                    v_isShared_2902_ = v_isSharedCheck_2913_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_2899_);
                    lean_inc(v_k_2898_);
                    lean_dec(v_r_2892_);
                    v___x_2901_ = lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2913_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2903_ = lean_unsigned_to_nat(3);
                if v_isShared_2902_ == 0 {
                    lean_ctor_set(v___x_2901_, 4, v_l_2875_);
                    lean_ctor_set(v___x_2901_, 3, v_l_2875_);
                    lean_ctor_set(v___x_2901_, 2, v_v_2894_);
                    lean_ctor_set(v___x_2901_, 1, v_k_2893_);
                    lean_ctor_set(v___x_2901_, 0, v___x_2789_);
                    v___x_2905_ = v___x_2901_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2893_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2894_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_l_2875_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_l_2875_);
                    v___x_2905_ = v_reuseFailAlloc_2912_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2897_ == 0 {
                    lean_ctor_set(v___x_2896_, 4, v_l_2875_);
                    lean_ctor_set(v___x_2896_, 2, v_v_2781_);
                    lean_ctor_set(v___x_2896_, 1, v_k_2780_);
                    lean_ctor_set(v___x_2896_, 0, v___x_2789_);
                    v___x_2907_ = v___x_2896_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 3, v_l_2875_);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 4, v_l_2875_);
                    v___x_2907_ = v_reuseFailAlloc_2911_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v___x_2907_);
                    lean_ctor_set(v___x_2785_, 3, v___x_2905_);
                    lean_ctor_set(v___x_2785_, 2, v_v_2899_);
                    lean_ctor_set(v___x_2785_, 1, v_k_2898_);
                    lean_ctor_set(v___x_2785_, 0, v___x_2903_);
                    v___x_2909_ = v___x_2785_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2903_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_k_2898_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_v_2899_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 3, v___x_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 4, v___x_2907_);
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
                v_size_2947_ = lean_ctor_get(v_l_2934_, 0);
                v_k_2948_ = lean_ctor_get(v_l_2934_, 1);
                v_v_2949_ = lean_ctor_get(v_l_2934_, 2);
                v_l_2950_ = lean_ctor_get(v_l_2934_, 3);
                v_r_2951_ = lean_ctor_get(v_l_2934_, 4);
                v_size_2952_ = lean_ctor_get(v_r_2935_, 0);
                v___x_2953_ = lean_unsigned_to_nat(2);
                v___x_2954_ = lean_nat_mul(v___x_2953_, v_size_2952_);
                v___x_2955_ = lean_nat_dec_lt(v_size_2947_, v___x_2954_);
                lean_dec(v___x_2954_);
                if v___x_2955_ == 0 {
                    lean_inc(v_r_2951_);
                    lean_inc(v_l_2950_);
                    lean_inc(v_v_2949_);
                    lean_inc(v_k_2948_);
                    v_isSharedCheck_2983_ = (!lean_is_exclusive(v_l_2934_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v_unused_2984_ = lean_ctor_get(v_l_2934_, 4);
                        lean_dec(v_unused_2984_);
                        v_unused_2985_ = lean_ctor_get(v_l_2934_, 3);
                        lean_dec(v_unused_2985_);
                        v_unused_2986_ = lean_ctor_get(v_l_2934_, 2);
                        lean_dec(v_unused_2986_);
                        v_unused_2987_ = lean_ctor_get(v_l_2934_, 1);
                        lean_dec(v_unused_2987_);
                        v_unused_2988_ = lean_ctor_get(v_l_2934_, 0);
                        lean_dec(v_unused_2988_);
                        v___x_2957_ = v_l_2934_;
                        v_isShared_2958_ = v_isSharedCheck_2983_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_2934_);
                        v___x_2957_ = lean_box(0);
                        v_isShared_2958_ = v_isSharedCheck_2983_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2785_);
                    v___x_2989_ = lean_nat_add(v___x_2929_, v_size_2930_);
                    v___x_2990_ = lean_nat_add(v___x_2989_, v_size_2931_);
                    lean_dec(v_size_2931_);
                    v___x_2991_ = lean_nat_add(v___x_2989_, v_size_2947_);
                    lean_dec(v___x_2989_);
                    lean_inc_ref(v_l_2782_);
                    if v_isShared_2946_ == 0 {
                        lean_ctor_set(v___x_2945_, 4, v_l_2934_);
                        lean_ctor_set(v___x_2945_, 3, v_l_2782_);
                        lean_ctor_set(v___x_2945_, 2, v_v_2781_);
                        lean_ctor_set(v___x_2945_, 1, v_k_2780_);
                        lean_ctor_set(v___x_2945_, 0, v___x_2991_);
                        v___x_2993_ = v___x_2945_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2991_);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_k_2780_);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_v_2781_);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_l_2782_);
                        lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_l_2934_);
                        v___x_2993_ = v_reuseFailAlloc_3006_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2959_ = lean_nat_add(v___x_2929_, v_size_2930_);
                v___x_2960_ = lean_nat_add(v___x_2959_, v_size_2931_);
                lean_dec(v_size_2931_);
                if lean_obj_tag(v_l_2950_) == 0 {
                    v_size_2981_ = lean_ctor_get(v_l_2950_, 0);
                    lean_inc(v_size_2981_);
                    v___y_2973_ = v_size_2981_;
                    state = 29;
                    continue;
                } else {
                    v___x_2982_ = lean_unsigned_to_nat(0);
                    v___y_2973_ = v___x_2982_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2965_ = lean_nat_add(v___y_2962_, v___y_2964_);
                lean_dec(v___y_2964_);
                lean_dec(v___y_2962_);
                if v_isShared_2958_ == 0 {
                    lean_ctor_set(v___x_2957_, 4, v_r_2935_);
                    lean_ctor_set(v___x_2957_, 3, v_r_2951_);
                    lean_ctor_set(v___x_2957_, 2, v_v_2933_);
                    lean_ctor_set(v___x_2957_, 1, v_k_2932_);
                    lean_ctor_set(v___x_2957_, 0, v___x_2965_);
                    v___x_2967_ = v___x_2957_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2965_);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_k_2932_);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_v_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_r_2951_);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_r_2935_);
                    v___x_2967_ = v_reuseFailAlloc_2971_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2946_ == 0 {
                    lean_ctor_set(v___x_2945_, 4, v___x_2967_);
                    lean_ctor_set(v___x_2945_, 3, v___y_2963_);
                    lean_ctor_set(v___x_2945_, 2, v_v_2949_);
                    lean_ctor_set(v___x_2945_, 1, v_k_2948_);
                    lean_ctor_set(v___x_2945_, 0, v___x_2960_);
                    v___x_2969_ = v___x_2945_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2960_);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_k_2948_);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_v_2949_);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 3, v___y_2963_);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 4, v___x_2967_);
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
                lean_dec(v___y_2973_);
                lean_dec(v___x_2959_);
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v_l_2950_);
                    lean_ctor_set(v___x_2785_, 0, v___x_2974_);
                    v___x_2976_ = v___x_2785_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2974_);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_l_2782_);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_l_2950_);
                    v___x_2976_ = v_reuseFailAlloc_2980_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2977_ = lean_nat_add(v___x_2929_, v_size_2952_);
                if lean_obj_tag(v_r_2951_) == 0 {
                    v_size_2978_ = lean_ctor_get(v_r_2951_, 0);
                    lean_inc(v_size_2978_);
                    v___y_2962_ = v___x_2977_;
                    v___y_2963_ = v___x_2976_;
                    v___y_2964_ = v_size_2978_;
                    state = 26;
                    continue;
                } else {
                    v___x_2979_ = lean_unsigned_to_nat(0);
                    v___y_2962_ = v___x_2977_;
                    v___y_2963_ = v___x_2976_;
                    v___y_2964_ = v___x_2979_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3000_ = (!lean_is_exclusive(v_l_2782_)) as u8;
                if v_isSharedCheck_3000_ == 0 {
                    v_unused_3001_ = lean_ctor_get(v_l_2782_, 4);
                    lean_dec(v_unused_3001_);
                    v_unused_3002_ = lean_ctor_get(v_l_2782_, 3);
                    lean_dec(v_unused_3002_);
                    v_unused_3003_ = lean_ctor_get(v_l_2782_, 2);
                    lean_dec(v_unused_3003_);
                    v_unused_3004_ = lean_ctor_get(v_l_2782_, 1);
                    lean_dec(v_unused_3004_);
                    v_unused_3005_ = lean_ctor_get(v_l_2782_, 0);
                    lean_dec(v_unused_3005_);
                    v___x_2995_ = v_l_2782_;
                    v_isShared_2996_ = v_isSharedCheck_3000_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_2782_);
                    v___x_2995_ = lean_box(0);
                    v_isShared_2996_ = v_isSharedCheck_3000_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2996_ == 0 {
                    lean_ctor_set(v___x_2995_, 4, v_r_2935_);
                    lean_ctor_set(v___x_2995_, 3, v___x_2993_);
                    lean_ctor_set(v___x_2995_, 2, v_v_2933_);
                    lean_ctor_set(v___x_2995_, 1, v_k_2932_);
                    lean_ctor_set(v___x_2995_, 0, v___x_2990_);
                    v___x_2998_ = v___x_2995_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2990_);
                    lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_k_2932_);
                    lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_v_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2999_, 3, v___x_2993_);
                    lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_r_2935_);
                    v___x_2998_ = v_reuseFailAlloc_2999_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2998_;
            }
            34 => {
                v_k_3020_ = lean_ctor_get(v_l_3013_, 1);
                v_v_3021_ = lean_ctor_get(v_l_3013_, 2);
                v_isSharedCheck_3035_ = (!lean_is_exclusive(v_l_3013_)) as u8;
                if v_isSharedCheck_3035_ == 0 {
                    v_unused_3036_ = lean_ctor_get(v_l_3013_, 4);
                    lean_dec(v_unused_3036_);
                    v_unused_3037_ = lean_ctor_get(v_l_3013_, 3);
                    lean_dec(v_unused_3037_);
                    v_unused_3038_ = lean_ctor_get(v_l_3013_, 0);
                    lean_dec(v_unused_3038_);
                    v___x_3023_ = v_l_3013_;
                    v_isShared_3024_ = v_isSharedCheck_3035_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_3021_);
                    lean_inc(v_k_3020_);
                    lean_dec(v_l_3013_);
                    v___x_3023_ = lean_box(0);
                    v_isShared_3024_ = v_isSharedCheck_3035_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3025_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3014_, 2);
                if v_isShared_3024_ == 0 {
                    lean_ctor_set(v___x_3023_, 4, v_r_3014_);
                    lean_ctor_set(v___x_3023_, 3, v_r_3014_);
                    lean_ctor_set(v___x_3023_, 2, v_v_2781_);
                    lean_ctor_set(v___x_3023_, 1, v_k_2780_);
                    lean_ctor_set(v___x_3023_, 0, v___x_2929_);
                    v___x_3027_ = v___x_3023_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_2929_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_r_3014_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 4, v_r_3014_);
                    v___x_3027_ = v_reuseFailAlloc_3034_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_3014_);
                if v_isShared_3019_ == 0 {
                    lean_ctor_set(v___x_3018_, 3, v_r_3014_);
                    lean_ctor_set(v___x_3018_, 0, v___x_2929_);
                    v___x_3029_ = v___x_3018_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_2929_);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_k_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_v_3016_);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_r_3014_);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 4, v_r_3014_);
                    v___x_3029_ = v_reuseFailAlloc_3033_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v___x_3029_);
                    lean_ctor_set(v___x_2785_, 3, v___x_3027_);
                    lean_ctor_set(v___x_2785_, 2, v_v_3021_);
                    lean_ctor_set(v___x_2785_, 1, v_k_3020_);
                    lean_ctor_set(v___x_2785_, 0, v___x_3025_);
                    v___x_3031_ = v___x_2785_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_k_3020_);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_v_3021_);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 3, v___x_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 4, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3032_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3031_;
            }
            39 => {
                v___x_3048_ = lean_unsigned_to_nat(3);
                if v_isShared_3047_ == 0 {
                    lean_ctor_set(v___x_3046_, 4, v_l_3013_);
                    lean_ctor_set(v___x_3046_, 2, v_v_2781_);
                    lean_ctor_set(v___x_3046_, 1, v_k_2780_);
                    lean_ctor_set(v___x_3046_, 0, v___x_2929_);
                    v___x_3050_ = v___x_3046_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_2929_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_k_2780_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_v_2781_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_l_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_l_3013_);
                    v___x_3050_ = v_reuseFailAlloc_3054_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2786_ == 0 {
                    lean_ctor_set(v___x_2785_, 4, v_r_3042_);
                    lean_ctor_set(v___x_2785_, 3, v___x_3050_);
                    lean_ctor_set(v___x_2785_, 2, v_v_3044_);
                    lean_ctor_set(v___x_2785_, 1, v_k_3043_);
                    lean_ctor_set(v___x_2785_, 0, v___x_3048_);
                    v___x_3052_ = v___x_2785_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_k_3043_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_v_3044_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 3, v___x_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_r_3042_);
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
    mut v___x_3069_: *mut LeanObject,
    mut v_as_3070_: *mut LeanObject,
    mut v_i_3071_: usize,
    mut v_stop_3072_: usize,
    mut v_b_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: usize = 0;
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_usize_dec_eq(v_i_3071_, v_stop_3072_);
                if v___x_3076_ == 0 {
                    v___x_3077_ = lean_array_uget_borrowed(v_as_3070_, v_i_3071_);
                    v_name_3078_ = lean_ctor_get(v___x_3077_, 1);
                    v_kind_3079_ = lean_ctor_get(v___x_3077_, 2);
                    v___x_3080_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_b_3073_, v_name_3078_);
                    if lean_obj_tag(v___x_3080_) == 1 {
                        lean_dec(v_b_3073_);
                        v_val_3081_ = lean_ctor_get(v___x_3080_, 0);
                        lean_inc(v_val_3081_);
                        lean_dec_ref_known(v___x_3080_, 1);
                        v_kind_3082_ = lean_ctor_get(v_val_3081_, 2);
                        lean_inc(v_kind_3082_);
                        lean_dec(v_val_3081_);
                        v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0;
                        v___x_3084_ = lean_string_append(v___x_3069_, v___x_3083_);
                        v___x_3085_ = 1;
                        lean_inc(v_name_3078_);
                        v___x_3086_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_3078_,
                                v___x_3085_,
                            );
                        v___x_3087_ = lean_string_append(v___x_3084_, v___x_3086_);
                        lean_dec_ref(v___x_3086_);
                        v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1;
                        v___x_3089_ = lean_string_append(v___x_3087_, v___x_3088_);
                        v___x_3090_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_3082_,
                                v___x_3085_,
                            );
                        v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
                        lean_dec_ref(v___x_3090_);
                        v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2;
                        v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
                        lean_inc(v_kind_3079_);
                        v___x_3094_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_3079_,
                                v___x_3085_,
                            );
                        v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
                        lean_dec_ref(v___x_3094_);
                        v___x_3096_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1;
                        v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
                        v___x_3098_ = 3;
                        v___x_3099_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3099_, 0, v___x_3097_);
                        lean_ctor_set_uint8(
                            v___x_3099_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3098_,
                        );
                        v___x_3100_ = lean_array_get_size(v___y_3074_);
                        v___x_3101_ = lean_array_push(v___y_3074_, v___x_3099_);
                        v___x_3102_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3102_, 0, v___x_3100_);
                        lean_ctor_set(v___x_3102_, 1, v___x_3101_);
                        return v___x_3102_;
                    } else {
                        lean_dec(v___x_3080_);
                        lean_inc(v___x_3077_);
                        lean_inc(v_name_3078_);
                        v___x_3103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_name_3078_, v___x_3077_, v_b_3073_);
                        v___x_3104_ = 1usize;
                        v___x_3105_ = lean_usize_add(v_i_3071_, v___x_3104_);
                        v_i_3071_ = v___x_3105_;
                        v_b_3073_ = v___x_3103_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3069_);
                    v___x_3107_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3107_, 0, v_b_3073_);
                    lean_ctor_set(v___x_3107_, 1, v___y_3074_);
                    return v___x_3107_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(
    mut v___x_3108_: *mut LeanObject,
    mut v_as_3109_: *mut LeanObject,
    mut v_i_3110_: *mut LeanObject,
    mut v_stop_3111_: *mut LeanObject,
    mut v_b_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3115_: usize = 0;
    let mut v_stop_boxed_3116_: usize = 0;
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3115_ = lean_unbox_usize(v_i_3110_);
    lean_dec(v_i_3110_);
    v_stop_boxed_3116_ = lean_unbox_usize(v_stop_3111_);
    lean_dec(v_stop_3111_);
    v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3108_, v_as_3109_, v_i_boxed_3115_, v_stop_boxed_3116_, v_b_3112_, v___y_3113_);
    lean_dec_ref(v_as_3109_);
    return v_res_3117_;
}
pub unsafe fn l_Lake_LakefileConfig_loadFromEnv(
    mut v_env_3124_: *mut LeanObject,
    mut v_opts_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3149_: usize = 0;
    let mut v___x_3150_: usize = 0;
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3203_: usize = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3208_: usize = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3213_: usize = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3227_: usize = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v_lintDriver_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v___y_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3266_: usize = 0;
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3276_: usize = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3282_: usize = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3291_: usize = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3297_: usize = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: u8 = 0;
    let mut v_testDriver_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_testDriver_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_a_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_a_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3346_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v_a_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_a_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_a_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v___y_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: usize = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3409_: u8 = 0;
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: usize = 0;
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut v_a_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut v_a_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u8 = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_env_3124_);
                v___x_3136_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(
                    v_env_3124_,
                    v_opts_3125_,
                );
                v___x_3137_ =
                    l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                        v___x_3136_,
                    );
                if lean_obj_tag(v___x_3137_) == 0 {
                    v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
                    lean_inc(v_a_3138_);
                    lean_dec_ref_known(v___x_3137_, 1);
                    v___x_3139_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
                    lean_inc_ref(v_opts_3125_);
                    lean_inc_ref_n(v_env_3124_, 2);
                    v___f_3140_ = lean_alloc_closure(
                        l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_3140_, 0, v_env_3124_);
                    lean_closure_set(v___f_3140_, 1, v_opts_3125_);
                    lean_closure_set(v___f_3140_, 2, v___x_3139_);
                    v___x_3141_ = l_Lake_targetAttr;
                    v___x_3142_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_3124_, v___x_3141_, v___f_3140_);
                    v___x_3143_ =
                        l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                            v___x_3142_,
                        );
                    if lean_obj_tag(v___x_3143_) == 0 {
                        v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
                        lean_inc(v_a_3144_);
                        lean_dec_ref_known(v___x_3143_, 1);
                        v_baseName_3145_ = lean_ctor_get(v_a_3138_, 0);
                        v_keyName_3146_ = lean_ctor_get(v_a_3138_, 1);
                        v_config_3147_ = lean_ctor_get(v_a_3138_, 3);
                        v_toArray_3148_ = lean_ctor_get(v_a_3144_, 1);
                        v_sz_3149_ = lean_array_size(v_toArray_3148_);
                        v___x_3150_ = 0usize;
                        lean_inc_ref(v_toArray_3148_);
                        lean_inc(v_keyName_3146_);
                        v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__2(v_keyName_3146_, v_sz_3149_, v___x_3150_, v_toArray_3148_, v_a_3126_);
                        if lean_obj_tag(v___x_3151_) == 0 {
                            v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
                            v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
                            v_isSharedCheck_3420_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                            if v_isSharedCheck_3420_ == 0 {
                                v___x_3155_ = v___x_3151_;
                                v_isShared_3156_ = v_isSharedCheck_3420_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3153_);
                                lean_inc(v_a_3152_);
                                lean_dec(v___x_3151_);
                                v___x_3155_ = lean_box(0);
                                v_isShared_3156_ = v_isSharedCheck_3420_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3144_);
                            lean_dec(v_a_3138_);
                            lean_dec_ref(v_opts_3125_);
                            lean_dec_ref(v_env_3124_);
                            v_a_3421_ = lean_ctor_get(v___x_3151_, 0);
                            v_a_3422_ = lean_ctor_get(v___x_3151_, 1);
                            v_isSharedCheck_3429_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                            if v_isSharedCheck_3429_ == 0 {
                                v___x_3424_ = v___x_3151_;
                                v_isShared_3425_ = v_isSharedCheck_3429_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_a_3422_);
                                lean_inc(v_a_3421_);
                                lean_dec(v___x_3151_);
                                v___x_3424_ = lean_box(0);
                                v_isShared_3425_ = v_isSharedCheck_3429_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3138_);
                        lean_dec_ref(v_opts_3125_);
                        lean_dec_ref(v_env_3124_);
                        v_a_3430_ = lean_ctor_get(v___x_3143_, 0);
                        lean_inc(v_a_3430_);
                        lean_dec_ref_known(v___x_3143_, 1);
                        v___x_3431_ = lean_io_error_to_string(v_a_3430_);
                        v___x_3432_ = 3;
                        v___x_3433_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3433_, 0, v___x_3431_);
                        lean_ctor_set_uint8(
                            v___x_3433_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3432_,
                        );
                        v___x_3434_ = lean_array_get_size(v_a_3126_);
                        v___x_3435_ = lean_array_push(v_a_3126_, v___x_3433_);
                        v___x_3436_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3436_, 0, v___x_3434_);
                        lean_ctor_set(v___x_3436_, 1, v___x_3435_);
                        return v___x_3436_;
                    }
                } else {
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3437_ = lean_ctor_get(v___x_3137_, 0);
                    lean_inc(v_a_3437_);
                    lean_dec_ref_known(v___x_3137_, 1);
                    v___x_3438_ = lean_io_error_to_string(v_a_3437_);
                    v___x_3439_ = 3;
                    v___x_3440_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3440_, 0, v___x_3438_);
                    lean_ctor_set_uint8(
                        v___x_3440_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3439_,
                    );
                    v___x_3441_ = lean_array_get_size(v_a_3126_);
                    v___x_3442_ = lean_array_push(v_a_3126_, v___x_3440_);
                    v___x_3443_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3443_, 0, v___x_3441_);
                    lean_ctor_set(v___x_3443_, 1, v___x_3442_);
                    return v___x_3443_;
                }
            }
            1 => {
                v___x_3131_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3131_, 0, v_a_3129_);
                lean_ctor_set(v___x_3131_, 1, v_a_3130_);
                return v___x_3131_;
            }
            2 => {
                v___x_3135_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3135_, 0, v_a_3133_);
                lean_ctor_set(v___x_3135_, 1, v_a_3134_);
                return v___x_3135_;
            }
            3 => {
                v___x_3183_ = l_Lake_instTypeNameScriptFn_unsafe__1;
                v___x_3184_ = 0;
                lean_inc(v_baseName_3145_);
                v___x_3185_ = l_Lean_Name_toString(v_baseName_3145_, v___x_3184_);
                v___x_3186_ = lean_box((v___x_3184_) as usize);
                lean_inc_ref(v___x_3185_);
                lean_inc_ref(v_opts_3125_);
                lean_inc_ref(v_env_3124_);
                v___f_3187_ = lean_alloc_closure(
                    l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed as *mut core::ffi::c_void,
                    8,
                    5,
                );
                lean_closure_set(v___f_3187_, 0, v___x_3186_);
                lean_closure_set(v___f_3187_, 1, v_env_3124_);
                lean_closure_set(v___f_3187_, 2, v_opts_3125_);
                lean_closure_set(v___f_3187_, 3, v___x_3183_);
                lean_closure_set(v___f_3187_, 4, v___x_3185_);
                v___x_3188_ = lean_box(1);
                v___x_3189_ = lean_unsigned_to_nat(0);
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
                            lean_inc_ref(v___x_3185_);
                            v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3416_, v___x_3188_, v_a_3153_);
                            v___y_3402_ = v___x_3417_;
                            state = 28;
                            continue;
                        }
                    } else {
                        v___x_3418_ = lean_usize_of_nat(v___x_3391_);
                        lean_inc_ref(v___x_3185_);
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
                if lean_obj_tag(v___x_3168_) == 0 {
                    v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
                    lean_inc(v_a_3169_);
                    lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3170_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v___x_3170_, 0, v_a_3138_);
                    lean_ctor_set(v___x_3170_, 1, v___y_3161_);
                    lean_ctor_set(v___x_3170_, 2, v_a_3169_);
                    lean_ctor_set(v___x_3170_, 3, v_a_3152_);
                    lean_ctor_set(v___x_3170_, 4, v___y_3158_);
                    lean_ctor_set(v___x_3170_, 5, v___y_3165_);
                    lean_ctor_set(v___x_3170_, 6, v___y_3159_);
                    lean_ctor_set(v___x_3170_, 7, v___y_3164_);
                    lean_ctor_set(v___x_3170_, 8, v___y_3163_);
                    lean_ctor_set(v___x_3170_, 9, v___y_3162_);
                    lean_ctor_set(v___x_3170_, 10, v___y_3166_);
                    if v_isShared_3156_ == 0 {
                        lean_ctor_set(v___x_3155_, 1, v___y_3160_);
                        lean_ctor_set(v___x_3155_, 0, v___x_3170_);
                        v___x_3172_ = v___x_3155_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
                        lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___y_3160_);
                        v___x_3172_ = v_reuseFailAlloc_3173_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3166_);
                    lean_dec_ref(v___y_3165_);
                    lean_dec_ref(v___y_3164_);
                    lean_dec_ref(v___y_3163_);
                    lean_dec_ref(v___y_3162_);
                    lean_dec_ref(v___y_3161_);
                    lean_dec(v___y_3159_);
                    lean_dec(v___y_3158_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3138_);
                    v_a_3174_ = lean_ctor_get(v___x_3168_, 0);
                    lean_inc(v_a_3174_);
                    lean_dec_ref_known(v___x_3168_, 1);
                    v___x_3175_ = lean_io_error_to_string(v_a_3174_);
                    v___x_3176_ = 3;
                    v___x_3177_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3177_, 0, v___x_3175_);
                    lean_ctor_set_uint8(
                        v___x_3177_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3176_,
                    );
                    v___x_3178_ = lean_array_get_size(v___y_3160_);
                    v___x_3179_ = lean_array_push(v___y_3160_, v___x_3177_);
                    if v_isShared_3156_ == 0 {
                        lean_ctor_set_tag(v___x_3155_, 1);
                        lean_ctor_set(v___x_3155_, 1, v___x_3179_);
                        lean_ctor_set(v___x_3155_, 0, v___x_3178_);
                        v___x_3181_ = v___x_3155_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
                        lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
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
                lean_inc_ref_n(v_env_3124_, 2);
                v___x_3202_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3201_, v_env_3124_);
                v_sz_3203_ = lean_array_size(v___x_3202_);
                v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_3124_, v_opts_3125_, v___x_3202_, v_sz_3203_, v___x_3150_, v___x_3200_);
                lean_dec_ref(v___x_3202_);
                if lean_obj_tag(v___x_3204_) == 0 {
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
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
                    v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
                    lean_inc(v_a_3205_);
                    lean_dec_ref_known(v___x_3204_, 1);
                    v___x_3206_ = l_Lake_packageFacetAttr;
                    lean_inc_ref_n(v_env_3124_, 2);
                    v___x_3207_ =
                        l_Lake_OrderedTagAttribute_getAllEntries(v___x_3206_, v_env_3124_);
                    v_sz_3208_ = lean_array_size(v___x_3207_);
                    v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_3124_, v_opts_3125_, v___x_3207_, v_sz_3208_, v___x_3150_, v_a_3205_);
                    lean_dec_ref(v___x_3207_);
                    if lean_obj_tag(v___x_3209_) == 0 {
                        lean_dec_ref(v_opts_3125_);
                        lean_dec_ref(v_env_3124_);
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
                        v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
                        lean_inc(v_a_3210_);
                        lean_dec_ref_known(v___x_3209_, 1);
                        v___x_3211_ = l_Lake_libraryFacetAttr;
                        lean_inc_ref(v_env_3124_);
                        v___x_3212_ =
                            l_Lake_OrderedTagAttribute_getAllEntries(v___x_3211_, v_env_3124_);
                        v_sz_3213_ = lean_array_size(v___x_3212_);
                        v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_3124_, v_opts_3125_, v___x_3212_, v_sz_3213_, v___x_3150_, v_a_3210_);
                        lean_dec_ref(v___x_3212_);
                        lean_dec_ref(v_opts_3125_);
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
                lean_inc_ref(v_env_3124_);
                v___x_3226_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3225_, v_env_3124_);
                v_sz_3227_ = lean_array_size(v___x_3226_);
                lean_inc_ref(v___x_3185_);
                v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_3144_, v___y_3218_, v___x_3185_, v_sz_3227_, v___x_3150_, v___x_3226_, v_a_3224_);
                if lean_obj_tag(v___x_3228_) == 0 {
                    v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
                    lean_inc(v_a_3229_);
                    v_a_3230_ = lean_ctor_get(v___x_3228_, 1);
                    lean_inc(v_a_3230_);
                    lean_dec_ref_known(v___x_3228_, 2);
                    v___x_3231_ = lean_array_get_size(v_a_3229_);
                    v___x_3232_ = lean_nat_dec_lt(v___y_3217_, v___x_3231_);
                    if v___x_3232_ == 0 {
                        v___x_3233_ = lean_nat_dec_lt(v___x_3189_, v___x_3231_);
                        if v___x_3233_ == 0 {
                            lean_dec(v_a_3229_);
                            lean_dec_ref(v___x_3185_);
                            v_lintDriver_3234_ = lean_ctor_get(v_config_3147_, 14);
                            lean_inc_ref(v_lintDriver_3234_);
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
                            v_lintDriver_3235_ = lean_ctor_get(v_config_3147_, 14);
                            v___x_3236_ = lean_string_utf8_byte_size(v_lintDriver_3235_);
                            v___x_3237_ = lean_nat_dec_eq(v___x_3236_, v___x_3189_);
                            if v___x_3237_ == 0 {
                                lean_dec(v_a_3229_);
                                lean_dec_ref(v_a_3223_);
                                lean_dec_ref(v___y_3222_);
                                lean_dec_ref(v___y_3221_);
                                lean_dec_ref(v___y_3220_);
                                lean_dec_ref(v___y_3219_);
                                lean_dec(v___y_3218_);
                                lean_dec(v___y_3216_);
                                lean_del_object(v___x_3155_);
                                lean_dec(v_a_3152_);
                                lean_dec(v_a_3138_);
                                lean_dec_ref(v_opts_3125_);
                                lean_dec_ref(v_env_3124_);
                                v___x_3238_ = l_Lake_LakefileConfig_loadFromEnv___closed__1;
                                v___x_3239_ = lean_string_append(v___x_3185_, v___x_3238_);
                                v___x_3240_ = 3;
                                v___x_3241_ = lean_alloc_ctor(0, 1, (1) as u32);
                                lean_ctor_set(v___x_3241_, 0, v___x_3239_);
                                lean_ctor_set_uint8(
                                    v___x_3241_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                    v___x_3240_,
                                );
                                v___x_3242_ = lean_array_get_size(v_a_3230_);
                                v___x_3243_ = lean_array_push(v_a_3230_, v___x_3241_);
                                v_a_3133_ = v___x_3242_;
                                v_a_3134_ = v___x_3243_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v___x_3185_);
                                v___x_3244_ = lean_array_fget(v_a_3229_, v___x_3189_);
                                lean_dec(v_a_3229_);
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
                        lean_dec(v_a_3229_);
                        lean_dec_ref(v_a_3223_);
                        lean_dec_ref(v___y_3222_);
                        lean_dec_ref(v___y_3221_);
                        lean_dec_ref(v___y_3220_);
                        lean_dec_ref(v___y_3219_);
                        lean_dec(v___y_3218_);
                        lean_dec(v___y_3216_);
                        lean_del_object(v___x_3155_);
                        lean_dec(v_a_3152_);
                        lean_dec(v_a_3138_);
                        lean_dec_ref(v_opts_3125_);
                        lean_dec_ref(v_env_3124_);
                        v___x_3246_ = l_Lake_LakefileConfig_loadFromEnv___closed__2;
                        v___x_3247_ = lean_string_append(v___x_3185_, v___x_3246_);
                        v___x_3248_ = 3;
                        v___x_3249_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3249_, 0, v___x_3247_);
                        lean_ctor_set_uint8(
                            v___x_3249_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                    lean_dec_ref(v_a_3223_);
                    lean_dec_ref(v___y_3222_);
                    lean_dec_ref(v___y_3221_);
                    lean_dec_ref(v___y_3220_);
                    lean_dec_ref(v___y_3219_);
                    lean_dec(v___y_3218_);
                    lean_dec(v___y_3216_);
                    lean_dec_ref(v___x_3185_);
                    lean_del_object(v___x_3155_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3138_);
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3252_ = lean_ctor_get(v___x_3228_, 0);
                    v_a_3253_ = lean_ctor_get(v___x_3228_, 1);
                    v_isSharedCheck_3260_ = (!lean_is_exclusive(v___x_3228_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3255_ = v___x_3228_;
                        v_isShared_3256_ = v_isSharedCheck_3260_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3253_);
                        lean_inc(v_a_3252_);
                        lean_dec(v___x_3228_);
                        v___x_3255_ = lean_box(0);
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
                    v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_a_3253_);
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
                lean_inc_ref(v_env_3124_);
                v___x_3265_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3264_, v_env_3124_);
                v_sz_3266_ = lean_array_size(v___x_3265_);
                lean_inc_ref(v___x_3185_);
                lean_inc(v_a_3144_);
                v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_3144_, v___x_3185_, v_sz_3266_, v___x_3150_, v___x_3265_, v_a_3263_);
                if lean_obj_tag(v___x_3267_) == 0 {
                    v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
                    lean_inc(v_a_3268_);
                    v_a_3269_ = lean_ctor_get(v___x_3267_, 1);
                    lean_inc(v_a_3269_);
                    lean_dec_ref_known(v___x_3267_, 2);
                    v___x_3270_ = l_Lake_scriptAttr;
                    lean_inc_ref(v_env_3124_);
                    v___x_3271_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_3124_, v___x_3270_, v___f_3187_, v_a_3269_);
                    if lean_obj_tag(v___x_3271_) == 0 {
                        v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
                        lean_inc(v_a_3272_);
                        v_a_3273_ = lean_ctor_get(v___x_3271_, 1);
                        lean_inc(v_a_3273_);
                        lean_dec_ref_known(v___x_3271_, 2);
                        v___x_3274_ = l_Lake_defaultScriptAttr;
                        lean_inc_ref(v_env_3124_);
                        v___x_3275_ =
                            l_Lake_OrderedTagAttribute_getAllEntries(v___x_3274_, v_env_3124_);
                        v_sz_3276_ = lean_array_size(v___x_3275_);
                        lean_inc_ref(v___x_3185_);
                        v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_3272_, v___x_3185_, v_sz_3276_, v___x_3150_, v___x_3275_, v_a_3273_);
                        if lean_obj_tag(v___x_3277_) == 0 {
                            v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
                            lean_inc(v_a_3278_);
                            v_a_3279_ = lean_ctor_get(v___x_3277_, 1);
                            lean_inc(v_a_3279_);
                            lean_dec_ref_known(v___x_3277_, 2);
                            v___x_3280_ = l_Lake_postUpdateAttr;
                            lean_inc_ref_n(v_env_3124_, 2);
                            v___x_3281_ =
                                l_Lake_OrderedTagAttribute_getAllEntries(v___x_3280_, v_env_3124_);
                            v_sz_3282_ = lean_array_size(v___x_3281_);
                            lean_inc(v_keyName_3146_);
                            v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_3124_, v_opts_3125_, v_keyName_3146_, v_sz_3282_, v___x_3150_, v___x_3281_, v_a_3279_);
                            if lean_obj_tag(v___x_3283_) == 0 {
                                v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
                                v_a_3285_ = lean_ctor_get(v___x_3283_, 1);
                                v_isSharedCheck_3341_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                                if v_isSharedCheck_3341_ == 0 {
                                    v___x_3287_ = v___x_3283_;
                                    v_isShared_3288_ = v_isSharedCheck_3341_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_3285_);
                                    lean_inc(v_a_3284_);
                                    lean_dec(v___x_3283_);
                                    v___x_3287_ = lean_box(0);
                                    v_isShared_3288_ = v_isSharedCheck_3341_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3278_);
                                lean_dec(v_a_3272_);
                                lean_dec(v_a_3268_);
                                lean_dec(v___y_3262_);
                                lean_dec_ref(v___x_3185_);
                                lean_del_object(v___x_3155_);
                                lean_dec(v_a_3152_);
                                lean_dec(v_a_3144_);
                                lean_dec(v_a_3138_);
                                lean_dec_ref(v_opts_3125_);
                                lean_dec_ref(v_env_3124_);
                                v_a_3342_ = lean_ctor_get(v___x_3283_, 0);
                                v_a_3343_ = lean_ctor_get(v___x_3283_, 1);
                                v_isSharedCheck_3350_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                                if v_isSharedCheck_3350_ == 0 {
                                    v___x_3345_ = v___x_3283_;
                                    v_isShared_3346_ = v_isSharedCheck_3350_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_3343_);
                                    lean_inc(v_a_3342_);
                                    lean_dec(v___x_3283_);
                                    v___x_3345_ = lean_box(0);
                                    v_isShared_3346_ = v_isSharedCheck_3350_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3272_);
                            lean_dec(v_a_3268_);
                            lean_dec(v___y_3262_);
                            lean_dec_ref(v___x_3185_);
                            lean_del_object(v___x_3155_);
                            lean_dec(v_a_3152_);
                            lean_dec(v_a_3144_);
                            lean_dec(v_a_3138_);
                            lean_dec_ref(v_opts_3125_);
                            lean_dec_ref(v_env_3124_);
                            v_a_3351_ = lean_ctor_get(v___x_3277_, 0);
                            v_a_3352_ = lean_ctor_get(v___x_3277_, 1);
                            v_isSharedCheck_3359_ = (!lean_is_exclusive(v___x_3277_)) as u8;
                            if v_isSharedCheck_3359_ == 0 {
                                v___x_3354_ = v___x_3277_;
                                v_isShared_3355_ = v_isSharedCheck_3359_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_3352_);
                                lean_inc(v_a_3351_);
                                lean_dec(v___x_3277_);
                                v___x_3354_ = lean_box(0);
                                v_isShared_3355_ = v_isSharedCheck_3359_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3268_);
                        lean_dec(v___y_3262_);
                        lean_dec_ref(v___x_3185_);
                        lean_del_object(v___x_3155_);
                        lean_dec(v_a_3152_);
                        lean_dec(v_a_3144_);
                        lean_dec(v_a_3138_);
                        lean_dec_ref(v_opts_3125_);
                        lean_dec_ref(v_env_3124_);
                        v_a_3360_ = lean_ctor_get(v___x_3271_, 0);
                        v_a_3361_ = lean_ctor_get(v___x_3271_, 1);
                        v_isSharedCheck_3368_ = (!lean_is_exclusive(v___x_3271_)) as u8;
                        if v_isSharedCheck_3368_ == 0 {
                            v___x_3363_ = v___x_3271_;
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3361_);
                            lean_inc(v_a_3360_);
                            lean_dec(v___x_3271_);
                            v___x_3363_ = lean_box(0);
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3262_);
                    lean_dec_ref(v___f_3187_);
                    lean_dec_ref(v___x_3185_);
                    lean_del_object(v___x_3155_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3144_);
                    lean_dec(v_a_3138_);
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3369_ = lean_ctor_get(v___x_3267_, 0);
                    v_a_3370_ = lean_ctor_get(v___x_3267_, 1);
                    v_isSharedCheck_3377_ = (!lean_is_exclusive(v___x_3267_)) as u8;
                    if v_isSharedCheck_3377_ == 0 {
                        v___x_3372_ = v___x_3267_;
                        v_isShared_3373_ = v_isSharedCheck_3377_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_3370_);
                        lean_inc(v_a_3369_);
                        lean_dec(v___x_3267_);
                        v___x_3372_ = lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3377_;
                        state = 22;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3289_ = l_Lake_packageDepAttr;
                lean_inc_ref_n(v_env_3124_, 2);
                v___x_3290_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_3289_, v_env_3124_);
                v_sz_3291_ = lean_array_size(v___x_3290_);
                v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_3124_, v_opts_3125_, v_sz_3291_, v___x_3150_, v___x_3290_);
                v___x_3293_ =
                    l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(
                        v___x_3292_,
                    );
                if lean_obj_tag(v___x_3293_) == 0 {
                    lean_del_object(v___x_3287_);
                    v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
                    lean_inc(v_a_3294_);
                    lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3295_ = l_Lake_testDriverAttr;
                    lean_inc_ref(v_env_3124_);
                    v___x_3296_ =
                        l_Lake_OrderedTagAttribute_getAllEntries(v___x_3295_, v_env_3124_);
                    v_sz_3297_ = lean_array_size(v___x_3296_);
                    lean_inc_ref(v___x_3185_);
                    lean_inc(v_a_3144_);
                    v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_3144_, v_a_3272_, v___x_3185_, v_sz_3297_, v___x_3150_, v___x_3296_, v_a_3285_);
                    if lean_obj_tag(v___x_3298_) == 0 {
                        v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
                        lean_inc(v_a_3299_);
                        v_a_3300_ = lean_ctor_get(v___x_3298_, 1);
                        lean_inc(v_a_3300_);
                        lean_dec_ref_known(v___x_3298_, 2);
                        v___x_3301_ = lean_unsigned_to_nat(1);
                        v___x_3302_ = lean_array_get_size(v_a_3299_);
                        v___x_3303_ = lean_nat_dec_lt(v___x_3301_, v___x_3302_);
                        if v___x_3303_ == 0 {
                            v___x_3304_ = lean_nat_dec_lt(v___x_3189_, v___x_3302_);
                            if v___x_3304_ == 0 {
                                lean_dec(v_a_3299_);
                                v_testDriver_3305_ = lean_ctor_get(v_config_3147_, 12);
                                lean_inc_ref(v_testDriver_3305_);
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
                                v_testDriver_3306_ = lean_ctor_get(v_config_3147_, 12);
                                v___x_3307_ = lean_string_utf8_byte_size(v_testDriver_3306_);
                                v___x_3308_ = lean_nat_dec_eq(v___x_3307_, v___x_3189_);
                                if v___x_3308_ == 0 {
                                    lean_dec(v_a_3299_);
                                    lean_dec(v_a_3294_);
                                    lean_dec(v_a_3284_);
                                    lean_dec(v_a_3278_);
                                    lean_dec(v_a_3272_);
                                    lean_dec(v_a_3268_);
                                    lean_dec(v___y_3262_);
                                    lean_del_object(v___x_3155_);
                                    lean_dec(v_a_3152_);
                                    lean_dec(v_a_3144_);
                                    lean_dec(v_a_3138_);
                                    lean_dec_ref(v_opts_3125_);
                                    lean_dec_ref(v_env_3124_);
                                    v___x_3309_ = l_Lake_LakefileConfig_loadFromEnv___closed__3;
                                    v___x_3310_ = lean_string_append(v___x_3185_, v___x_3309_);
                                    v___x_3311_ = 3;
                                    v___x_3312_ = lean_alloc_ctor(0, 1, (1) as u32);
                                    lean_ctor_set(v___x_3312_, 0, v___x_3310_);
                                    lean_ctor_set_uint8(
                                        v___x_3312_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                                    lean_dec(v_a_3299_);
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
                            lean_dec(v_a_3299_);
                            lean_dec(v_a_3294_);
                            lean_dec(v_a_3284_);
                            lean_dec(v_a_3278_);
                            lean_dec(v_a_3272_);
                            lean_dec(v_a_3268_);
                            lean_dec(v___y_3262_);
                            lean_del_object(v___x_3155_);
                            lean_dec(v_a_3152_);
                            lean_dec(v_a_3144_);
                            lean_dec(v_a_3138_);
                            lean_dec_ref(v_opts_3125_);
                            lean_dec_ref(v_env_3124_);
                            v___x_3317_ = l_Lake_LakefileConfig_loadFromEnv___closed__4;
                            v___x_3318_ = lean_string_append(v___x_3185_, v___x_3317_);
                            v___x_3319_ = 3;
                            v___x_3320_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_3320_, 0, v___x_3318_);
                            lean_ctor_set_uint8(
                                v___x_3320_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                        lean_dec(v_a_3294_);
                        lean_dec(v_a_3284_);
                        lean_dec(v_a_3278_);
                        lean_dec(v_a_3272_);
                        lean_dec(v_a_3268_);
                        lean_dec(v___y_3262_);
                        lean_dec_ref(v___x_3185_);
                        lean_del_object(v___x_3155_);
                        lean_dec(v_a_3152_);
                        lean_dec(v_a_3144_);
                        lean_dec(v_a_3138_);
                        lean_dec_ref(v_opts_3125_);
                        lean_dec_ref(v_env_3124_);
                        v_a_3323_ = lean_ctor_get(v___x_3298_, 0);
                        v_a_3324_ = lean_ctor_get(v___x_3298_, 1);
                        v_isSharedCheck_3331_ = (!lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3331_ == 0 {
                            v___x_3326_ = v___x_3298_;
                            v_isShared_3327_ = v_isSharedCheck_3331_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3324_);
                            lean_inc(v_a_3323_);
                            lean_dec(v___x_3298_);
                            v___x_3326_ = lean_box(0);
                            v_isShared_3327_ = v_isSharedCheck_3331_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3284_);
                    lean_dec(v_a_3278_);
                    lean_dec(v_a_3272_);
                    lean_dec(v_a_3268_);
                    lean_dec(v___y_3262_);
                    lean_dec_ref(v___x_3185_);
                    lean_del_object(v___x_3155_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3144_);
                    lean_dec(v_a_3138_);
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3332_ = lean_ctor_get(v___x_3293_, 0);
                    lean_inc(v_a_3332_);
                    lean_dec_ref_known(v___x_3293_, 1);
                    v___x_3333_ = lean_io_error_to_string(v_a_3332_);
                    v___x_3334_ = 3;
                    v___x_3335_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3335_, 0, v___x_3333_);
                    lean_ctor_set_uint8(
                        v___x_3335_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3334_,
                    );
                    v___x_3336_ = lean_array_get_size(v_a_3285_);
                    v___x_3337_ = lean_array_push(v_a_3285_, v___x_3335_);
                    if v_isShared_3288_ == 0 {
                        lean_ctor_set_tag(v___x_3287_, 1);
                        lean_ctor_set(v___x_3287_, 1, v___x_3337_);
                        lean_ctor_set(v___x_3287_, 0, v___x_3336_);
                        v___x_3339_ = v___x_3287_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3336_);
                        lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3337_);
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
                    v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
                    lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_a_3324_);
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
                    v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3342_);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
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
                    v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3351_);
                    lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_a_3352_);
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
                    v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3360_);
                    lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_a_3361_);
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
                    v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3369_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_a_3370_);
                    v___x_3375_ = v_reuseFailAlloc_3376_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3375_;
            }
            24 => {
                if lean_obj_tag(v___y_3380_) == 0 {
                    v_a_3381_ = lean_ctor_get(v___y_3380_, 1);
                    lean_inc(v_a_3381_);
                    lean_dec_ref_known(v___y_3380_, 2);
                    v___y_3262_ = v___y_3379_;
                    v_a_3263_ = v_a_3381_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v___y_3379_);
                    lean_dec_ref(v___f_3187_);
                    lean_dec_ref(v___x_3185_);
                    lean_del_object(v___x_3155_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3144_);
                    lean_dec(v_a_3138_);
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3382_ = lean_ctor_get(v___y_3380_, 0);
                    v_a_3383_ = lean_ctor_get(v___y_3380_, 1);
                    v_isSharedCheck_3390_ = (!lean_is_exclusive(v___y_3380_)) as u8;
                    if v_isSharedCheck_3390_ == 0 {
                        v___x_3385_ = v___y_3380_;
                        v_isShared_3386_ = v_isSharedCheck_3390_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_3383_);
                        lean_inc(v_a_3382_);
                        lean_dec(v___y_3380_);
                        v___x_3385_ = lean_box(0);
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
                    v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3382_);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
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
                            lean_inc_ref(v___x_3185_);
                            v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3397_, v___x_3188_, v_a_3394_);
                            v___y_3379_ = v_a_3393_;
                            v___y_3380_ = v___x_3398_;
                            state = 24;
                            continue;
                        }
                    } else {
                        v___x_3399_ = lean_usize_of_nat(v___x_3391_);
                        lean_inc_ref(v___x_3185_);
                        v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_3185_, v_a_3152_, v___x_3150_, v___x_3399_, v___x_3188_, v_a_3394_);
                        v___y_3379_ = v_a_3393_;
                        v___y_3380_ = v___x_3400_;
                        state = 24;
                        continue;
                    }
                }
            }
            28 => {
                if lean_obj_tag(v___y_3402_) == 0 {
                    v_a_3403_ = lean_ctor_get(v___y_3402_, 0);
                    lean_inc(v_a_3403_);
                    v_a_3404_ = lean_ctor_get(v___y_3402_, 1);
                    lean_inc(v_a_3404_);
                    lean_dec_ref_known(v___y_3402_, 2);
                    v_a_3393_ = v_a_3403_;
                    v_a_3394_ = v_a_3404_;
                    state = 27;
                    continue;
                } else {
                    lean_dec_ref(v___f_3187_);
                    lean_dec_ref(v___x_3185_);
                    lean_del_object(v___x_3155_);
                    lean_dec(v_a_3152_);
                    lean_dec(v_a_3144_);
                    lean_dec(v_a_3138_);
                    lean_dec_ref(v_opts_3125_);
                    lean_dec_ref(v_env_3124_);
                    v_a_3405_ = lean_ctor_get(v___y_3402_, 0);
                    v_a_3406_ = lean_ctor_get(v___y_3402_, 1);
                    v_isSharedCheck_3413_ = (!lean_is_exclusive(v___y_3402_)) as u8;
                    if v_isSharedCheck_3413_ == 0 {
                        v___x_3408_ = v___y_3402_;
                        v_isShared_3409_ = v_isSharedCheck_3413_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3406_);
                        lean_inc(v_a_3405_);
                        lean_dec(v___y_3402_);
                        v___x_3408_ = lean_box(0);
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
                    v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_a_3406_);
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
                    v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3421_);
                    lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_a_3422_);
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
    mut v_env_3444_: *mut LeanObject,
    mut v_opts_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lake_LakefileConfig_loadFromEnv(v_env_3444_, v_opts_3445_, v_a_3446_);
    return v_res_3448_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(
    mut v_00_u03b2_3449_: *mut LeanObject,
    mut v_env_3450_: *mut LeanObject,
    mut v_attr_3451_: *mut LeanObject,
    mut v_f_3452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_env_3450_, v_attr_3451_, v_f_3452_);
    return v___x_3453_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(
    mut v_00_u03b2_3454_: *mut LeanObject,
    mut v_env_3455_: *mut LeanObject,
    mut v_attr_3456_: *mut LeanObject,
    mut v_f_3457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3458_: *mut LeanObject = core::ptr::null_mut();
    v_res_3458_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_3454_, v_env_3455_, v_attr_3456_, v_f_3457_);
    lean_dec_ref(v_attr_3456_);
    return v_res_3458_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(
    mut v_00_u03b2_3459_: *mut LeanObject,
    mut v_inst_3460_: *mut LeanObject,
    mut v_t_3461_: *mut LeanObject,
    mut v_k_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_t_3461_, v_k_3462_);
    return v___x_3463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(
    mut v_00_u03b2_3464_: *mut LeanObject,
    mut v_inst_3465_: *mut LeanObject,
    mut v_t_3466_: *mut LeanObject,
    mut v_k_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__3(
            v_00_u03b2_3464_,
            v_inst_3465_,
            v_t_3466_,
            v_k_3467_,
        );
    lean_dec(v_k_3467_);
    lean_dec(v_t_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4(
    mut v_00_u03b2_3469_: *mut LeanObject,
    mut v_k_3470_: *mut LeanObject,
    mut v_v_3471_: *mut LeanObject,
    mut v_t_3472_: *mut LeanObject,
    mut v_hl_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__4___redArg(v_k_3470_, v_v_3471_, v_t_3472_);
    return v___x_3474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(
    mut v_00_u03b4_3475_: *mut LeanObject,
    mut v_t_3476_: *mut LeanObject,
    mut v_k_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    v___x_3478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_3476_, v_k_3477_);
    return v___x_3478_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(
    mut v_00_u03b4_3479_: *mut LeanObject,
    mut v_t_3480_: *mut LeanObject,
    mut v_k_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3482_: *mut LeanObject = core::ptr::null_mut();
    v_res_3482_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(
            v_00_u03b4_3479_,
            v_t_3480_,
            v_k_3481_,
        );
    lean_dec(v_k_3481_);
    lean_dec(v_t_3480_);
    return v_res_3482_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(
    mut v_00_u03b2_3483_: *mut LeanObject,
    mut v_env_3484_: *mut LeanObject,
    mut v_attr_3485_: *mut LeanObject,
    mut v_f_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_3484_, v_attr_3485_, v_f_3486_, v___y_3487_);
    return v___x_3489_;
}
pub unsafe fn l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(
    mut v_00_u03b2_3490_: *mut LeanObject,
    mut v_env_3491_: *mut LeanObject,
    mut v_attr_3492_: *mut LeanObject,
    mut v_f_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3496_: *mut LeanObject = core::ptr::null_mut();
    v_res_3496_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_3490_, v_env_3491_, v_attr_3492_, v_f_3493_, v___y_3494_);
    lean_dec_ref(v_attr_3492_);
    return v_res_3496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(
    mut v___x_3497_: *mut LeanObject,
    mut v___x_3498_: *mut LeanObject,
    mut v_as_3499_: *mut LeanObject,
    mut v_i_3500_: usize,
    mut v_stop_3501_: usize,
    mut v_b_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_3497_, v_as_3499_, v_i_3500_, v_stop_3501_, v_b_3502_, v___y_3503_);
    return v___x_3505_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(
    mut v___x_3506_: *mut LeanObject,
    mut v___x_3507_: *mut LeanObject,
    mut v_as_3508_: *mut LeanObject,
    mut v_i_3509_: *mut LeanObject,
    mut v_stop_3510_: *mut LeanObject,
    mut v_b_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3514_: usize = 0;
    let mut v_stop_boxed_3515_: usize = 0;
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3514_ = lean_unbox_usize(v_i_3509_);
    lean_dec(v_i_3509_);
    v_stop_boxed_3515_ = lean_unbox_usize(v_stop_3510_);
    lean_dec(v_stop_3510_);
    v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_3506_, v___x_3507_, v_as_3508_, v_i_boxed_3514_, v_stop_boxed_3515_, v_b_3511_, v___y_3512_);
    lean_dec_ref(v_as_3508_);
    lean_dec(v___x_3507_);
    return v_res_3516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(
    mut v_00_u03b2_3517_: *mut LeanObject,
    mut v_f_3518_: *mut LeanObject,
    mut v_as_3519_: *mut LeanObject,
    mut v_i_3520_: usize,
    mut v_stop_3521_: usize,
    mut v_b_3522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___redArg(v_f_3518_, v_as_3519_, v_i_3520_, v_stop_3521_, v_b_3522_);
    return v___x_3523_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1___boxed(
    mut v_00_u03b2_3524_: *mut LeanObject,
    mut v_f_3525_: *mut LeanObject,
    mut v_as_3526_: *mut LeanObject,
    mut v_i_3527_: *mut LeanObject,
    mut v_stop_3528_: *mut LeanObject,
    mut v_b_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3530_: usize = 0;
    let mut v_stop_boxed_3531_: usize = 0;
    let mut v_res_3532_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3530_ = lean_unbox_usize(v_i_3527_);
    lean_dec(v_i_3527_);
    v_stop_boxed_3531_ = lean_unbox_usize(v_stop_3528_);
    lean_dec(v_stop_3528_);
    v_res_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__1_spec__1(v_00_u03b2_3524_, v_f_3525_, v_as_3526_, v_i_boxed_3530_, v_stop_boxed_3531_, v_b_3529_);
    lean_dec_ref(v_as_3526_);
    return v_res_3532_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(
    mut v_00_u03b2_3533_: *mut LeanObject,
    mut v_f_3534_: *mut LeanObject,
    mut v_as_3535_: *mut LeanObject,
    mut v_i_3536_: usize,
    mut v_stop_3537_: usize,
    mut v_b_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_3534_, v_as_3535_, v_i_3536_, v_stop_3537_, v_b_3538_, v___y_3539_);
    return v___x_3541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(
    mut v_00_u03b2_3542_: *mut LeanObject,
    mut v_f_3543_: *mut LeanObject,
    mut v_as_3544_: *mut LeanObject,
    mut v_i_3545_: *mut LeanObject,
    mut v_stop_3546_: *mut LeanObject,
    mut v_b_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3550_: usize = 0;
    let mut v_stop_boxed_3551_: usize = 0;
    let mut v_res_3552_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3550_ = lean_unbox_usize(v_i_3545_);
    lean_dec(v_i_3545_);
    v_stop_boxed_3551_ = lean_unbox_usize(v_stop_3546_);
    lean_dec(v_stop_3546_);
    v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_3542_, v_f_3543_, v_as_3544_, v_i_boxed_3550_, v_stop_boxed_3551_, v_b_3547_, v___y_3548_);
    lean_dec_ref(v_as_3544_);
    return v_res_3552_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Lean_Eval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LakefileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_AttributesCore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Lean_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Load_Lean_Eval(builtin);
}

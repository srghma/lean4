// Lean compiler output
// Module: Lake.CLI.Build
// Imports: Lake.CLI.Error Lake.Config.Workspace Lake.Build.Infos Lake.Build.Job.Monad Lake.Build.Job.Register Lake.Util.IO Init.Data.Iterators.Consumers
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toName, l_String_Slice_toString};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1};
use crate::r#gen::Init::System::IO::l_System_FilePath_isDir;
use crate::r#gen::Lake::Build::Facets::l_Lake_Module_leanArtsFacet;
use crate::r#gen::Lake::Build::Info::l_Lake_BuildInfo_key;
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Monad::{
    initialize_Lake_Build_Job_Monad, l_Lake_Job_collectArray___redArg,
    l_Lake_Job_mixArray___redArg, runtime_initialize_Lake_Build_Job_Monad,
};
use crate::r#gen::Lake::Build::Job::Register::{
    initialize_Lake_Build_Job_Register, l_Lake_Job_renew___redArg,
    runtime_initialize_Lake_Build_Job_Register,
};
use crate::r#gen::Lake::Build::Key::l_Lake_BuildKey_toSimpleString;
use crate::r#gen::Lake::CLI::Error::{
    initialize_Lake_CLI_Error, runtime_initialize_Lake_CLI_Error,
};
use crate::r#gen::Lake::Config::FacetConfig::l_Lake_FacetConfigMap_get_x3f;
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_LeanExe_keyword, l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::LeanExe::l_Lake_Package_findTargetModule_x3f;
use crate::r#gen::Lake::Config::OutFormat::l_Lake_formatQuery___boxed;
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, l_Lake_Workspace_findLeanExe_x3f,
    l_Lake_Workspace_findModuleBySrc_x3f, l_Lake_Workspace_findModuleFacetConfig_x3f,
    l_Lake_Workspace_findPackageFacetConfig_x3f, l_Lake_Workspace_findTargetDecl_x3f,
    l_Lake_Workspace_findTargetModule_x3f, runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_resolvePath, runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lake::Util::Name::l_Lake_stringToLegalOrSimpleName;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint32, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_buildSpecs___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [60, 99, 111, 108, 108, 101, 99, 116, 105, 111, 110, 62, 0],
};
static mut l_Lake_buildSpecs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_buildSpecs___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1_value:
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
    m_fun: l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 102, 97, 117, 108, 116, 0],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__0_value
        ) as *mut LeanObject,
        9666231177748665885 as *mut LeanObject,
    ],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 97, 99, 107, 97, 103, 101, 0],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0_value)
        as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [43, 0],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [64, 0],
};
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0_value)
        as *mut LeanObject;
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_parseTargetSpec___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_parseTargetSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_parseTargetSpec___closed__0_value) as *mut LeanObject;
pub static l_Lake_parseTargetSpecs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_parseTargetSpecs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_parseTargetSpecs___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_mkBuildSpec___redArg(
    mut v_info_1487_: *mut LeanObject,
    mut v_inst_1488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    v___x_1489_ = 1;
    v___x_1490_ = lean_alloc_closure(l_Lake_formatQuery___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1490_, 0, lean_box(0));
    lean_closure_set(v___x_1490_, 1, v_inst_1488_);
    v___x_1491_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_1491_, 0, v_info_1487_);
    lean_ctor_set(v___x_1491_, 1, v___x_1490_);
    lean_ctor_set_uint8(
        v___x_1491_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1489_,
    );
    return v___x_1491_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_mkBuildSpec(
    mut v_00_u03b1_1492_: *mut LeanObject,
    mut v_info_1493_: *mut LeanObject,
    mut v_inst_1494_: *mut LeanObject,
    mut v_h_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = 1;
    v___x_1497_ = lean_alloc_closure(l_Lake_formatQuery___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1497_, 0, lean_box(0));
    lean_closure_set(v___x_1497_, 1, v_inst_1494_);
    v___x_1498_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_1498_, 0, v_info_1493_);
    lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    lean_ctor_set_uint8(
        v___x_1498_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1496_,
    );
    return v___x_1498_;
}
pub unsafe fn l_Lake_mkConfigBuildSpec___redArg(
    mut v_info_1499_: *mut LeanObject,
    mut v_config_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildable_1501_: u8 = 0;
    let mut v_format_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    v_buildable_1501_ = lean_ctor_get_uint8(
        v_config_1500_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
    );
    v_format_1502_ = lean_ctor_get(v_config_1500_, 3);
    lean_inc_ref(v_format_1502_);
    v___x_1503_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_1503_, 0, v_info_1499_);
    lean_ctor_set(v___x_1503_, 1, v_format_1502_);
    lean_ctor_set_uint8(
        v___x_1503_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_buildable_1501_,
    );
    return v___x_1503_;
}
pub unsafe fn l_Lake_mkConfigBuildSpec___redArg___boxed(
    mut v_info_1504_: *mut LeanObject,
    mut v_config_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1506_: *mut LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lake_mkConfigBuildSpec___redArg(v_info_1504_, v_config_1505_);
    lean_dec_ref(v_config_1505_);
    return v_res_1506_;
}
pub unsafe fn l_Lake_mkConfigBuildSpec(
    mut v_facet_1507_: *mut LeanObject,
    mut v_info_1508_: *mut LeanObject,
    mut v_config_1509_: *mut LeanObject,
    mut v_h_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildable_1511_: u8 = 0;
    let mut v_format_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v_buildable_1511_ = lean_ctor_get_uint8(
        v_config_1509_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
    );
    v_format_1512_ = lean_ctor_get(v_config_1509_, 3);
    lean_inc_ref(v_format_1512_);
    v___x_1513_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_1513_, 0, v_info_1508_);
    lean_ctor_set(v___x_1513_, 1, v_format_1512_);
    lean_ctor_set_uint8(
        v___x_1513_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_buildable_1511_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lake_mkConfigBuildSpec___boxed(
    mut v_facet_1514_: *mut LeanObject,
    mut v_info_1515_: *mut LeanObject,
    mut v_config_1516_: *mut LeanObject,
    mut v_h_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Lake_mkConfigBuildSpec(v_facet_1514_, v_info_1515_, v_config_1516_, v_h_1517_);
    lean_dec_ref(v_config_1516_);
    lean_dec(v_facet_1514_);
    return v_res_1518_;
}
pub unsafe fn l_Lake_BuildSpec_fetch(
    mut v_self_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_a_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v_registeredJobs_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: u8 = 0;
    let mut v_job_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut v_unused_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1527_ = lean_ctor_get(v_self_1519_, 0);
                lean_inc_ref_n(v_info_1527_, 2);
                lean_dec_ref(v_self_1519_);
                lean_inc_ref(v_a_1524_);
                lean_inc(v_a_1523_);
                lean_inc(v_a_1522_);
                lean_inc(v_a_1521_);
                v___x_1528_ = lean_apply_7(
                    v_a_1520_,
                    v_info_1527_,
                    v_a_1521_,
                    v_a_1522_,
                    v_a_1523_,
                    v_a_1524_,
                    v_a_1525_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1528_) == 0 {
                    v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
                    lean_inc(v_a_1529_);
                    v_a_1530_ = lean_ctor_get(v___x_1528_, 1);
                    lean_inc(v_a_1530_);
                    v_task_1531_ = lean_ctor_get(v_a_1529_, 0);
                    v_kind_1532_ = lean_ctor_get(v_a_1529_, 1);
                    v_caption_1533_ = lean_ctor_get(v_a_1529_, 2);
                    v_isSharedCheck_1561_ = (!lean_is_exclusive(v_a_1529_)) as u8;
                    if v_isSharedCheck_1561_ == 0 {
                        v___x_1535_ = v_a_1529_;
                        v_isShared_1536_ = v_isSharedCheck_1561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_caption_1533_);
                        lean_inc(v_kind_1532_);
                        lean_inc(v_task_1531_);
                        lean_dec(v_a_1529_);
                        v___x_1535_ = lean_box(0);
                        v_isShared_1536_ = v_isSharedCheck_1561_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_info_1527_);
                    return v___x_1528_;
                }
            }
            1 => {
                v___x_1537_ = lean_string_utf8_byte_size(v_caption_1533_);
                lean_dec_ref(v_caption_1533_);
                v___x_1538_ = lean_unsigned_to_nat(0);
                v___x_1539_ = lean_nat_dec_eq(v___x_1537_, v___x_1538_);
                if v___x_1539_ == 0 {
                    lean_del_object(v___x_1535_);
                    lean_dec(v_kind_1532_);
                    lean_dec_ref(v_task_1531_);
                    lean_dec(v_a_1530_);
                    lean_dec_ref(v_info_1527_);
                    return v___x_1528_;
                } else {
                    v_isSharedCheck_1558_ = (!lean_is_exclusive(v___x_1528_)) as u8;
                    if v_isSharedCheck_1558_ == 0 {
                        v_unused_1559_ = lean_ctor_get(v___x_1528_, 1);
                        lean_dec(v_unused_1559_);
                        v_unused_1560_ = lean_ctor_get(v___x_1528_, 0);
                        lean_dec(v_unused_1560_);
                        v___x_1541_ = v___x_1528_;
                        v_isShared_1542_ = v_isSharedCheck_1558_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_1528_);
                        v___x_1541_ = lean_box(0);
                        v_isShared_1542_ = v_isSharedCheck_1558_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_registeredJobs_1543_ = lean_ctor_get(v_a_1524_, 3);
                v___x_1544_ = lean_st_ref_take(v_registeredJobs_1543_);
                v___x_1545_ = l_Lake_BuildInfo_key(v_info_1527_);
                v___x_1546_ = l_Lake_BuildKey_toSimpleString(v___x_1545_);
                v___x_1547_ = 0;
                if v_isShared_1536_ == 0 {
                    lean_ctor_set(v___x_1535_, 2, v___x_1546_);
                    v_job_1549_ = v___x_1535_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_task_1531_);
                    lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_kind_1532_);
                    lean_ctor_set(v_reuseFailAlloc_1557_, 2, v___x_1546_);
                    v_job_1549_ = v_reuseFailAlloc_1557_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_1549_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1547_,
                );
                lean_inc_ref(v_job_1549_);
                v___x_1550_ = l_Lake_Job_toOpaque___redArg(v_job_1549_);
                v___x_1551_ = lean_array_push(v___x_1544_, v___x_1550_);
                v___x_1552_ = lean_st_ref_set(v_registeredJobs_1543_, v___x_1551_);
                v___x_1553_ = l_Lake_Job_renew___redArg(v_job_1549_);
                if v_isShared_1542_ == 0 {
                    lean_ctor_set(v___x_1541_, 0, v___x_1553_);
                    v___x_1555_ = v___x_1541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
                    lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_a_1530_);
                    v___x_1555_ = v_reuseFailAlloc_1556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildSpec_fetch___boxed(
    mut v_self_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
    mut v_a_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1570_: *mut LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Lake_BuildSpec_fetch(
        v_self_1562_,
        v_a_1563_,
        v_a_1564_,
        v_a_1565_,
        v_a_1566_,
        v_a_1567_,
        v_a_1568_,
    );
    lean_dec_ref(v_a_1567_);
    lean_dec(v_a_1566_);
    lean_dec(v_a_1565_);
    lean_dec(v_a_1564_);
    return v_res_1570_;
}
pub unsafe fn l_Lake_BuildSpec_build(
    mut v_self_1571_: *mut LeanObject,
    mut v_a_1572_: *mut LeanObject,
    mut v_a_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
    mut v_a_1575_: *mut LeanObject,
    mut v_a_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v_registeredJobs_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: u8 = 0;
    let mut v_job_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut v_unused_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1584_ = lean_ctor_get(v_self_1571_, 0);
                lean_inc_ref_n(v_info_1584_, 2);
                lean_dec_ref(v_self_1571_);
                lean_inc_ref(v_a_1576_);
                lean_inc(v_a_1575_);
                lean_inc(v_a_1574_);
                lean_inc(v_a_1573_);
                v___x_1585_ = lean_apply_7(
                    v_a_1572_,
                    v_info_1584_,
                    v_a_1573_,
                    v_a_1574_,
                    v_a_1575_,
                    v_a_1576_,
                    v_a_1577_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1585_) == 0 {
                    v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
                    lean_inc(v_a_1586_);
                    v_a_1587_ = lean_ctor_get(v___x_1585_, 1);
                    lean_inc(v_a_1587_);
                    lean_dec_ref_known(v___x_1585_, 2);
                    v_task_1588_ = lean_ctor_get(v_a_1586_, 0);
                    v_kind_1589_ = lean_ctor_get(v_a_1586_, 1);
                    v_caption_1590_ = lean_ctor_get(v_a_1586_, 2);
                    v___x_1591_ = lean_string_utf8_byte_size(v_caption_1590_);
                    v___x_1592_ = lean_unsigned_to_nat(0);
                    v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
                    if v___x_1593_ == 0 {
                        lean_dec_ref(v_info_1584_);
                        v_a_1580_ = v_a_1586_;
                        v_a_1581_ = v_a_1587_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_kind_1589_);
                        lean_inc_ref(v_task_1588_);
                        v_isSharedCheck_1609_ = (!lean_is_exclusive(v_a_1586_)) as u8;
                        if v_isSharedCheck_1609_ == 0 {
                            v_unused_1610_ = lean_ctor_get(v_a_1586_, 2);
                            lean_dec(v_unused_1610_);
                            v_unused_1611_ = lean_ctor_get(v_a_1586_, 1);
                            lean_dec(v_unused_1611_);
                            v_unused_1612_ = lean_ctor_get(v_a_1586_, 0);
                            lean_dec(v_unused_1612_);
                            v___x_1595_ = v_a_1586_;
                            v_isShared_1596_ = v_isSharedCheck_1609_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_a_1586_);
                            v___x_1595_ = lean_box(0);
                            v_isShared_1596_ = v_isSharedCheck_1609_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_info_1584_);
                    return v___x_1585_;
                }
            }
            1 => {
                v___x_1582_ = l_Lake_Job_toOpaque___redArg(v_a_1580_);
                v___x_1583_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1583_, 0, v___x_1582_);
                lean_ctor_set(v___x_1583_, 1, v_a_1581_);
                return v___x_1583_;
            }
            2 => {
                v_registeredJobs_1597_ = lean_ctor_get(v_a_1576_, 3);
                v___x_1598_ = lean_st_ref_take(v_registeredJobs_1597_);
                v___x_1599_ = l_Lake_BuildInfo_key(v_info_1584_);
                v___x_1600_ = l_Lake_BuildKey_toSimpleString(v___x_1599_);
                v___x_1601_ = 0;
                if v_isShared_1596_ == 0 {
                    lean_ctor_set(v___x_1595_, 2, v___x_1600_);
                    v_job_1603_ = v___x_1595_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_task_1588_);
                    lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_kind_1589_);
                    lean_ctor_set(v_reuseFailAlloc_1608_, 2, v___x_1600_);
                    v_job_1603_ = v_reuseFailAlloc_1608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_1603_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1601_,
                );
                lean_inc_ref(v_job_1603_);
                v___x_1604_ = l_Lake_Job_toOpaque___redArg(v_job_1603_);
                v___x_1605_ = lean_array_push(v___x_1598_, v___x_1604_);
                v___x_1606_ = lean_st_ref_set(v_registeredJobs_1597_, v___x_1605_);
                v___x_1607_ = l_Lake_Job_renew___redArg(v_job_1603_);
                v_a_1580_ = v___x_1607_;
                v_a_1581_ = v_a_1587_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildSpec_build___boxed(
    mut v_self_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
    mut v_a_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1621_: *mut LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Lake_BuildSpec_build(
        v_self_1613_,
        v_a_1614_,
        v_a_1615_,
        v_a_1616_,
        v_a_1617_,
        v_a_1618_,
        v_a_1619_,
    );
    lean_dec_ref(v_a_1618_);
    lean_dec(v_a_1617_);
    lean_dec(v_a_1616_);
    lean_dec(v_a_1615_);
    return v_res_1621_;
}
pub unsafe fn l_Lake_BuildSpec_query___lam__0(
    mut v_format_1622_: *mut LeanObject,
    mut v_fmt_1623_: u8,
    mut v_x_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1624_) == 0 {
                    v_a_1625_ = lean_ctor_get(v_x_1624_, 0);
                    v_a_1626_ = lean_ctor_get(v_x_1624_, 1);
                    v_isSharedCheck_1635_ = (!lean_is_exclusive(v_x_1624_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1628_ = v_x_1624_;
                        v_isShared_1629_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1626_);
                        lean_inc(v_a_1625_);
                        lean_dec(v_x_1624_);
                        v___x_1628_ = lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_format_1622_);
                    v_a_1636_ = lean_ctor_get(v_x_1624_, 0);
                    v_a_1637_ = lean_ctor_get(v_x_1624_, 1);
                    v_isSharedCheck_1644_ = (!lean_is_exclusive(v_x_1624_)) as u8;
                    if v_isSharedCheck_1644_ == 0 {
                        v___x_1639_ = v_x_1624_;
                        v_isShared_1640_ = v_isSharedCheck_1644_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1637_);
                        lean_inc(v_a_1636_);
                        lean_dec(v_x_1624_);
                        v___x_1639_ = lean_box(0);
                        v_isShared_1640_ = v_isSharedCheck_1644_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1630_ = lean_box((v_fmt_1623_) as usize);
                v___x_1631_ = lean_apply_2(v_format_1622_, v___x_1630_, v_a_1625_);
                if v_isShared_1629_ == 0 {
                    lean_ctor_set(v___x_1628_, 0, v___x_1631_);
                    v___x_1633_ = v___x_1628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_a_1626_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1633_;
            }
            3 => {
                if v_isShared_1640_ == 0 {
                    v___x_1642_ = v___x_1639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1636_);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1637_);
                    v___x_1642_ = v_reuseFailAlloc_1643_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildSpec_query___lam__0___boxed(
    mut v_format_1645_: *mut LeanObject,
    mut v_fmt_1646_: *mut LeanObject,
    mut v_x_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1648_: u8 = 0;
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1648_ = (lean_unbox(v_fmt_1646_) as u8);
    v_res_1649_ = l_Lake_BuildSpec_query___lam__0(v_format_1645_, v_fmt_boxed_1648_, v_x_1647_);
    return v_res_1649_;
}
pub unsafe fn l_Lake_BuildSpec_query(
    mut v_self_1650_: *mut LeanObject,
    mut v_fmt_1651_: u8,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
    mut v_a_1655_: *mut LeanObject,
    mut v_a_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_format_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v_task_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optional_1670_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registeredJobs_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v_a_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1659_ = lean_ctor_get(v_self_1650_, 0);
                lean_inc_ref_n(v_info_1659_, 2);
                v_format_1660_ = lean_ctor_get(v_self_1650_, 1);
                lean_inc_ref(v_format_1660_);
                lean_dec_ref(v_self_1650_);
                v___x_1661_ = l_Lake_BuildInfo_key(v_info_1659_);
                lean_inc_ref(v_a_1656_);
                lean_inc(v_a_1655_);
                lean_inc(v_a_1654_);
                lean_inc(v_a_1653_);
                v___x_1662_ = lean_apply_7(
                    v_a_1652_,
                    v_info_1659_,
                    v_a_1653_,
                    v_a_1654_,
                    v_a_1655_,
                    v_a_1656_,
                    v_a_1657_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1662_) == 0 {
                    v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
                    v_a_1664_ = lean_ctor_get(v___x_1662_, 1);
                    v_isSharedCheck_1703_ = (!lean_is_exclusive(v___x_1662_)) as u8;
                    if v_isSharedCheck_1703_ == 0 {
                        v___x_1666_ = v___x_1662_;
                        v_isShared_1667_ = v_isSharedCheck_1703_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1664_);
                        lean_inc(v_a_1663_);
                        lean_dec(v___x_1662_);
                        v___x_1666_ = lean_box(0);
                        v_isShared_1667_ = v_isSharedCheck_1703_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1661_);
                    lean_dec_ref(v_format_1660_);
                    v_a_1704_ = lean_ctor_get(v___x_1662_, 0);
                    v_a_1705_ = lean_ctor_get(v___x_1662_, 1);
                    v_isSharedCheck_1712_ = (!lean_is_exclusive(v___x_1662_)) as u8;
                    if v_isSharedCheck_1712_ == 0 {
                        v___x_1707_ = v___x_1662_;
                        v_isShared_1708_ = v_isSharedCheck_1712_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1705_);
                        lean_inc(v_a_1704_);
                        lean_dec(v___x_1662_);
                        v___x_1707_ = lean_box(0);
                        v_isShared_1708_ = v_isSharedCheck_1712_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_task_1668_ = lean_ctor_get(v_a_1663_, 0);
                v_caption_1669_ = lean_ctor_get(v_a_1663_, 2);
                v_optional_1670_ = lean_ctor_get_uint8(
                    v_a_1663_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1701_ = (!lean_is_exclusive(v_a_1663_)) as u8;
                if v_isSharedCheck_1701_ == 0 {
                    v_unused_1702_ = lean_ctor_get(v_a_1663_, 1);
                    lean_dec(v_unused_1702_);
                    v___x_1672_ = v_a_1663_;
                    v_isShared_1673_ = v_isSharedCheck_1701_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_caption_1669_);
                    lean_inc(v_task_1668_);
                    lean_dec(v_a_1663_);
                    v___x_1672_ = lean_box(0);
                    v_isShared_1673_ = v_isSharedCheck_1701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1674_ = lean_box(0);
                v___x_1675_ = lean_box((v_fmt_1651_) as usize);
                v___f_1676_ = lean_alloc_closure(
                    l_Lake_BuildSpec_query___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1676_, 0, v_format_1660_);
                lean_closure_set(v___f_1676_, 1, v___x_1675_);
                v___x_1677_ = lean_unsigned_to_nat(0);
                v___x_1678_ = 0;
                v___x_1679_ = lean_task_map(v___f_1676_, v_task_1668_, v___x_1677_, v___x_1678_);
                v___x_1680_ = lean_string_utf8_byte_size(v_caption_1669_);
                v___x_1681_ = lean_nat_dec_eq(v___x_1680_, v___x_1677_);
                if v___x_1681_ == 0 {
                    lean_dec_ref(v___x_1661_);
                    if v_isShared_1673_ == 0 {
                        lean_ctor_set(v___x_1672_, 1, v___x_1674_);
                        lean_ctor_set(v___x_1672_, 0, v___x_1679_);
                        v___x_1683_ = v___x_1672_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1679_);
                        lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1674_);
                        lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_caption_1669_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1687_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_optional_1670_,
                        );
                        v___x_1683_ = v_reuseFailAlloc_1687_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_caption_1669_);
                    v_registeredJobs_1688_ = lean_ctor_get(v_a_1656_, 3);
                    v___x_1689_ = lean_st_ref_take(v_registeredJobs_1688_);
                    v___x_1690_ = l_Lake_BuildKey_toSimpleString(v___x_1661_);
                    if v_isShared_1673_ == 0 {
                        lean_ctor_set(v___x_1672_, 2, v___x_1690_);
                        lean_ctor_set(v___x_1672_, 1, v___x_1674_);
                        lean_ctor_set(v___x_1672_, 0, v___x_1679_);
                        v_job_1692_ = v___x_1672_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1679_);
                        lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1674_);
                        lean_ctor_set(v_reuseFailAlloc_1700_, 2, v___x_1690_);
                        v_job_1692_ = v_reuseFailAlloc_1700_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1664_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1685_;
            }
            5 => {
                lean_ctor_set_uint8(
                    v_job_1692_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1678_,
                );
                lean_inc_ref(v_job_1692_);
                v___x_1693_ = l_Lake_Job_toOpaque___redArg(v_job_1692_);
                v___x_1694_ = lean_array_push(v___x_1689_, v___x_1693_);
                v___x_1695_ = lean_st_ref_set(v_registeredJobs_1688_, v___x_1694_);
                v___x_1696_ = l_Lake_Job_renew___redArg(v_job_1692_);
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 0, v___x_1696_);
                    v___x_1698_ = v___x_1666_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_a_1664_);
                    v___x_1698_ = v_reuseFailAlloc_1699_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1698_;
            }
            7 => {
                if v_isShared_1708_ == 0 {
                    v___x_1710_ = v___x_1707_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1704_);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1705_);
                    v___x_1710_ = v_reuseFailAlloc_1711_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildSpec_query___boxed(
    mut v_self_1713_: *mut LeanObject,
    mut v_fmt_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_a_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1722_: u8 = 0;
    let mut v_res_1723_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1722_ = (lean_unbox(v_fmt_1714_) as u8);
    v_res_1723_ = l_Lake_BuildSpec_query(
        v_self_1713_,
        v_fmt_boxed_1722_,
        v_a_1715_,
        v_a_1716_,
        v_a_1717_,
        v_a_1718_,
        v_a_1719_,
        v_a_1720_,
    );
    lean_dec_ref(v_a_1719_);
    lean_dec(v_a_1718_);
    lean_dec(v_a_1717_);
    lean_dec(v_a_1716_);
    return v_res_1723_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(
    mut v_sz_1724_: usize,
    mut v_i_1725_: usize,
    mut v_bs_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: usize = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v_registeredJobs_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v_job_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_unused_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1734_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
                if v___x_1734_ == 0 {
                    lean_dec_ref(v___y_1727_);
                    v___x_1735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1735_, 0, v_bs_1726_);
                    lean_ctor_set(v___x_1735_, 1, v___y_1732_);
                    return v___x_1735_;
                } else {
                    v_v_1736_ = lean_array_uget_borrowed(v_bs_1726_, v_i_1725_);
                    v_info_1737_ = lean_ctor_get(v_v_1736_, 0);
                    lean_inc_ref_n(v_info_1737_, 2);
                    lean_inc_ref(v___y_1727_);
                    lean_inc_ref(v___y_1731_);
                    lean_inc(v___y_1730_);
                    lean_inc(v___y_1729_);
                    lean_inc(v___y_1728_);
                    v___x_1738_ = lean_apply_7(
                        v___y_1727_,
                        v_info_1737_,
                        v___y_1728_,
                        v___y_1729_,
                        v___y_1730_,
                        v___y_1731_,
                        v___y_1732_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1738_) == 0 {
                        v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
                        lean_inc(v_a_1739_);
                        v_a_1740_ = lean_ctor_get(v___x_1738_, 1);
                        lean_inc(v_a_1740_);
                        lean_dec_ref_known(v___x_1738_, 2);
                        v_task_1741_ = lean_ctor_get(v_a_1739_, 0);
                        v_kind_1742_ = lean_ctor_get(v_a_1739_, 1);
                        v_caption_1743_ = lean_ctor_get(v_a_1739_, 2);
                        v___x_1744_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1745_ = lean_array_uset(v_bs_1726_, v_i_1725_, v___x_1744_);
                        v___x_1754_ = lean_string_utf8_byte_size(v_caption_1743_);
                        v___x_1755_ = lean_nat_dec_eq(v___x_1754_, v___x_1744_);
                        if v___x_1755_ == 0 {
                            lean_dec_ref(v_info_1737_);
                            v_a_1747_ = v_a_1739_;
                            v_a_1748_ = v_a_1740_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_kind_1742_);
                            lean_inc_ref(v_task_1741_);
                            v_isSharedCheck_1771_ = (!lean_is_exclusive(v_a_1739_)) as u8;
                            if v_isSharedCheck_1771_ == 0 {
                                v_unused_1772_ = lean_ctor_get(v_a_1739_, 2);
                                lean_dec(v_unused_1772_);
                                v_unused_1773_ = lean_ctor_get(v_a_1739_, 1);
                                lean_dec(v_unused_1773_);
                                v_unused_1774_ = lean_ctor_get(v_a_1739_, 0);
                                lean_dec(v_unused_1774_);
                                v___x_1757_ = v_a_1739_;
                                v_isShared_1758_ = v_isSharedCheck_1771_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_1739_);
                                v___x_1757_ = lean_box(0);
                                v_isShared_1758_ = v_isSharedCheck_1771_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_info_1737_);
                        lean_dec_ref(v___y_1727_);
                        lean_dec_ref(v_bs_1726_);
                        v_a_1775_ = lean_ctor_get(v___x_1738_, 0);
                        v_a_1776_ = lean_ctor_get(v___x_1738_, 1);
                        v_isSharedCheck_1783_ = (!lean_is_exclusive(v___x_1738_)) as u8;
                        if v_isSharedCheck_1783_ == 0 {
                            v___x_1778_ = v___x_1738_;
                            v_isShared_1779_ = v_isSharedCheck_1783_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1776_);
                            lean_inc(v_a_1775_);
                            lean_dec(v___x_1738_);
                            v___x_1778_ = lean_box(0);
                            v_isShared_1779_ = v_isSharedCheck_1783_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1749_ = l_Lake_Job_toOpaque___redArg(v_a_1747_);
                v___x_1750_ = 1usize;
                v___x_1751_ = lean_usize_add(v_i_1725_, v___x_1750_);
                v___x_1752_ = lean_array_uset(v_bs_x27_1745_, v_i_1725_, v___x_1749_);
                v_i_1725_ = v___x_1751_;
                v_bs_1726_ = v___x_1752_;
                v___y_1732_ = v_a_1748_;
                state = 0;
                continue;
            }
            2 => {
                v_registeredJobs_1759_ = lean_ctor_get(v___y_1731_, 3);
                v___x_1760_ = lean_st_ref_take(v_registeredJobs_1759_);
                v___x_1761_ = l_Lake_BuildInfo_key(v_info_1737_);
                v___x_1762_ = l_Lake_BuildKey_toSimpleString(v___x_1761_);
                v___x_1763_ = 0;
                if v_isShared_1758_ == 0 {
                    lean_ctor_set(v___x_1757_, 2, v___x_1762_);
                    v_job_1765_ = v___x_1757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_task_1741_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_kind_1742_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 2, v___x_1762_);
                    v_job_1765_ = v_reuseFailAlloc_1770_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_1765_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1763_,
                );
                lean_inc_ref(v_job_1765_);
                v___x_1766_ = l_Lake_Job_toOpaque___redArg(v_job_1765_);
                v___x_1767_ = lean_array_push(v___x_1760_, v___x_1766_);
                v___x_1768_ = lean_st_ref_set(v_registeredJobs_1759_, v___x_1767_);
                v___x_1769_ = l_Lake_Job_renew___redArg(v_job_1765_);
                v_a_1747_ = v___x_1769_;
                v_a_1748_ = v_a_1740_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1779_ == 0 {
                    v___x_1781_ = v___x_1778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1775_);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_a_1776_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0___boxed(
    mut v_sz_1784_: *mut LeanObject,
    mut v_i_1785_: *mut LeanObject,
    mut v_bs_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1794_: usize = 0;
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1794_ = lean_unbox_usize(v_sz_1784_);
    lean_dec(v_sz_1784_);
    v_i_boxed_1795_ = lean_unbox_usize(v_i_1785_);
    lean_dec(v_i_1785_);
    v_res_1796_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(
            v_sz_boxed_1794_,
            v_i_boxed_1795_,
            v_bs_1786_,
            v___y_1787_,
            v___y_1788_,
            v___y_1789_,
            v___y_1790_,
            v___y_1791_,
            v___y_1792_,
        );
    lean_dec_ref(v___y_1791_);
    lean_dec(v___y_1790_);
    lean_dec(v___y_1789_);
    lean_dec(v___y_1788_);
    return v_res_1796_;
}
pub unsafe fn l_Lake_buildSpecs(
    mut v_specs_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
    mut v_a_1802_: *mut LeanObject,
    mut v_a_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1806_: usize = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v_a_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1806_ = lean_array_size(v_specs_1798_);
                v___x_1807_ = 0usize;
                v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_buildSpecs_spec__0(v_sz_1806_, v___x_1807_, v_specs_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
                if lean_obj_tag(v___x_1808_) == 0 {
                    v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
                    v_a_1810_ = lean_ctor_get(v___x_1808_, 1);
                    v_isSharedCheck_1819_ = (!lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1812_ = v___x_1808_;
                        v_isShared_1813_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1810_);
                        lean_inc(v_a_1809_);
                        lean_dec(v___x_1808_);
                        v___x_1812_ = lean_box(0);
                        v_isShared_1813_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1820_ = lean_ctor_get(v___x_1808_, 0);
                    v_a_1821_ = lean_ctor_get(v___x_1808_, 1);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___x_1808_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1821_);
                        lean_inc(v_a_1820_);
                        lean_dec(v___x_1808_);
                        v___x_1823_ = lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1814_ = l_Lake_buildSpecs___closed__0;
                v___x_1815_ = l_Lake_Job_mixArray___redArg(v_a_1809_, v___x_1814_);
                lean_dec(v_a_1809_);
                if v_isShared_1813_ == 0 {
                    lean_ctor_set(v___x_1812_, 0, v___x_1815_);
                    v___x_1817_ = v___x_1812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1810_);
                    v___x_1817_ = v_reuseFailAlloc_1818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1817_;
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    v___x_1826_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1820_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_a_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_buildSpecs___boxed(
    mut v_specs_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1837_: *mut LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lake_buildSpecs(
        v_specs_1829_,
        v_a_1830_,
        v_a_1831_,
        v_a_1832_,
        v_a_1833_,
        v_a_1834_,
        v_a_1835_,
    );
    lean_dec_ref(v_a_1834_);
    lean_dec(v_a_1833_);
    lean_dec(v_a_1832_);
    lean_dec(v_a_1831_);
    return v_res_1837_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(
    mut v_format_1838_: *mut LeanObject,
    mut v_fmt_1839_: u8,
    mut v_x_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_a_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1840_) == 0 {
                    v_a_1841_ = lean_ctor_get(v_x_1840_, 0);
                    v_a_1842_ = lean_ctor_get(v_x_1840_, 1);
                    v_isSharedCheck_1851_ = (!lean_is_exclusive(v_x_1840_)) as u8;
                    if v_isSharedCheck_1851_ == 0 {
                        v___x_1844_ = v_x_1840_;
                        v_isShared_1845_ = v_isSharedCheck_1851_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1842_);
                        lean_inc(v_a_1841_);
                        lean_dec(v_x_1840_);
                        v___x_1844_ = lean_box(0);
                        v_isShared_1845_ = v_isSharedCheck_1851_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_format_1838_);
                    v_a_1852_ = lean_ctor_get(v_x_1840_, 0);
                    v_a_1853_ = lean_ctor_get(v_x_1840_, 1);
                    v_isSharedCheck_1860_ = (!lean_is_exclusive(v_x_1840_)) as u8;
                    if v_isSharedCheck_1860_ == 0 {
                        v___x_1855_ = v_x_1840_;
                        v_isShared_1856_ = v_isSharedCheck_1860_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1853_);
                        lean_inc(v_a_1852_);
                        lean_dec(v_x_1840_);
                        v___x_1855_ = lean_box(0);
                        v_isShared_1856_ = v_isSharedCheck_1860_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1846_ = lean_box((v_fmt_1839_) as usize);
                v___x_1847_ = lean_apply_2(v_format_1838_, v___x_1846_, v_a_1841_);
                if v_isShared_1845_ == 0 {
                    lean_ctor_set(v___x_1844_, 0, v___x_1847_);
                    v___x_1849_ = v___x_1844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_a_1842_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1849_;
            }
            3 => {
                if v_isShared_1856_ == 0 {
                    v___x_1858_ = v___x_1855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1852_);
                    lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1853_);
                    v___x_1858_ = v_reuseFailAlloc_1859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed(
    mut v_format_1861_: *mut LeanObject,
    mut v_fmt_1862_: *mut LeanObject,
    mut v_x_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1864_: u8 = 0;
    let mut v_res_1865_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1864_ = (lean_unbox(v_fmt_1862_) as u8);
    v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0(v_format_1861_, v_fmt_boxed_1864_, v_x_1863_);
    return v_res_1865_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(
    mut v_fmt_1866_: u8,
    mut v_sz_1867_: usize,
    mut v_i_1868_: usize,
    mut v_bs_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_format_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optional_1888_: u8 = 0;
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registeredJobs_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_unused_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_usize_dec_lt(v_i_1868_, v_sz_1867_);
                if v___x_1877_ == 0 {
                    lean_dec_ref(v___y_1870_);
                    v___x_1878_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1878_, 0, v_bs_1869_);
                    lean_ctor_set(v___x_1878_, 1, v___y_1875_);
                    return v___x_1878_;
                } else {
                    v_v_1879_ = lean_array_uget_borrowed(v_bs_1869_, v_i_1868_);
                    v_info_1880_ = lean_ctor_get(v_v_1879_, 0);
                    v_format_1881_ = lean_ctor_get(v_v_1879_, 1);
                    lean_inc_ref(v_format_1881_);
                    lean_inc_ref_n(v_info_1880_, 2);
                    v___x_1882_ = l_Lake_BuildInfo_key(v_info_1880_);
                    lean_inc_ref(v___y_1870_);
                    lean_inc_ref(v___y_1874_);
                    lean_inc(v___y_1873_);
                    lean_inc(v___y_1872_);
                    lean_inc(v___y_1871_);
                    v___x_1883_ = lean_apply_7(
                        v___y_1870_,
                        v_info_1880_,
                        v___y_1871_,
                        v___y_1872_,
                        v___y_1873_,
                        v___y_1874_,
                        v___y_1875_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1883_) == 0 {
                        v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                        lean_inc(v_a_1884_);
                        v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
                        lean_inc(v_a_1885_);
                        lean_dec_ref_known(v___x_1883_, 2);
                        v_task_1886_ = lean_ctor_get(v_a_1884_, 0);
                        v_caption_1887_ = lean_ctor_get(v_a_1884_, 2);
                        v_optional_1888_ = lean_ctor_get_uint8(
                            v_a_1884_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_isSharedCheck_1921_ = (!lean_is_exclusive(v_a_1884_)) as u8;
                        if v_isSharedCheck_1921_ == 0 {
                            v_unused_1922_ = lean_ctor_get(v_a_1884_, 1);
                            lean_dec(v_unused_1922_);
                            v___x_1890_ = v_a_1884_;
                            v_isShared_1891_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_caption_1887_);
                            lean_inc(v_task_1886_);
                            lean_dec(v_a_1884_);
                            v___x_1890_ = lean_box(0);
                            v_isShared_1891_ = v_isSharedCheck_1921_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1882_);
                        lean_dec_ref(v_format_1881_);
                        lean_dec_ref(v___y_1870_);
                        lean_dec_ref(v_bs_1869_);
                        v_a_1923_ = lean_ctor_get(v___x_1883_, 0);
                        v_a_1924_ = lean_ctor_get(v___x_1883_, 1);
                        v_isSharedCheck_1931_ = (!lean_is_exclusive(v___x_1883_)) as u8;
                        if v_isSharedCheck_1931_ == 0 {
                            v___x_1926_ = v___x_1883_;
                            v_isShared_1927_ = v_isSharedCheck_1931_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1924_);
                            lean_inc(v_a_1923_);
                            lean_dec(v___x_1883_);
                            v___x_1926_ = lean_box(0);
                            v_isShared_1927_ = v_isSharedCheck_1931_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1892_ = lean_unsigned_to_nat(0);
                v_bs_x27_1893_ = lean_array_uset(v_bs_1869_, v_i_1868_, v___x_1892_);
                v___x_1901_ = lean_box(0);
                v___x_1902_ = lean_box((v_fmt_1866_) as usize);
                v___f_1903_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1903_, 0, v_format_1881_);
                lean_closure_set(v___f_1903_, 1, v___x_1902_);
                v___x_1904_ = 0;
                v___x_1905_ = lean_task_map(v___f_1903_, v_task_1886_, v___x_1892_, v___x_1904_);
                v___x_1906_ = lean_string_utf8_byte_size(v_caption_1887_);
                v___x_1907_ = lean_nat_dec_eq(v___x_1906_, v___x_1892_);
                if v___x_1907_ == 0 {
                    lean_dec_ref(v___x_1882_);
                    if v_isShared_1891_ == 0 {
                        lean_ctor_set(v___x_1890_, 1, v___x_1901_);
                        lean_ctor_set(v___x_1890_, 0, v___x_1905_);
                        v___x_1909_ = v___x_1890_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1905_);
                        lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1901_);
                        lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_caption_1887_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1910_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_optional_1888_,
                        );
                        v___x_1909_ = v_reuseFailAlloc_1910_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_caption_1887_);
                    v_registeredJobs_1911_ = lean_ctor_get(v___y_1874_, 3);
                    v___x_1912_ = lean_st_ref_take(v_registeredJobs_1911_);
                    v___x_1913_ = l_Lake_BuildKey_toSimpleString(v___x_1882_);
                    if v_isShared_1891_ == 0 {
                        lean_ctor_set(v___x_1890_, 2, v___x_1913_);
                        lean_ctor_set(v___x_1890_, 1, v___x_1901_);
                        lean_ctor_set(v___x_1890_, 0, v___x_1905_);
                        v_job_1915_ = v___x_1890_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1905_);
                        lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1901_);
                        lean_ctor_set(v_reuseFailAlloc_1920_, 2, v___x_1913_);
                        v_job_1915_ = v_reuseFailAlloc_1920_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1897_ = 1usize;
                v___x_1898_ = lean_usize_add(v_i_1868_, v___x_1897_);
                v___x_1899_ = lean_array_uset(v_bs_x27_1893_, v_i_1868_, v_a_1895_);
                v_i_1868_ = v___x_1898_;
                v_bs_1869_ = v___x_1899_;
                v___y_1875_ = v_a_1896_;
                state = 0;
                continue;
            }
            3 => {
                v_a_1895_ = v___x_1909_;
                v_a_1896_ = v_a_1885_;
                state = 2;
                continue;
            }
            4 => {
                lean_ctor_set_uint8(
                    v_job_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1904_,
                );
                lean_inc_ref(v_job_1915_);
                v___x_1916_ = l_Lake_Job_toOpaque___redArg(v_job_1915_);
                v___x_1917_ = lean_array_push(v___x_1912_, v___x_1916_);
                v___x_1918_ = lean_st_ref_set(v_registeredJobs_1911_, v___x_1917_);
                v___x_1919_ = l_Lake_Job_renew___redArg(v_job_1915_);
                v_a_1895_ = v___x_1919_;
                v_a_1896_ = v_a_1885_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_1927_ == 0 {
                    v___x_1929_ = v___x_1926_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1923_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_a_1924_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0___boxed(
    mut v_fmt_1932_: *mut LeanObject,
    mut v_sz_1933_: *mut LeanObject,
    mut v_i_1934_: *mut LeanObject,
    mut v_bs_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1943_: u8 = 0;
    let mut v_sz_boxed_1944_: usize = 0;
    let mut v_i_boxed_1945_: usize = 0;
    let mut v_res_1946_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1943_ = (lean_unbox(v_fmt_1932_) as u8);
    v_sz_boxed_1944_ = lean_unbox_usize(v_sz_1933_);
    lean_dec(v_sz_1933_);
    v_i_boxed_1945_ = lean_unbox_usize(v_i_1934_);
    lean_dec(v_i_1934_);
    v_res_1946_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(
            v_fmt_boxed_1943_,
            v_sz_boxed_1944_,
            v_i_boxed_1945_,
            v_bs_1935_,
            v___y_1936_,
            v___y_1937_,
            v___y_1938_,
            v___y_1939_,
            v___y_1940_,
            v___y_1941_,
        );
    lean_dec_ref(v___y_1940_);
    lean_dec(v___y_1939_);
    lean_dec(v___y_1938_);
    lean_dec(v___y_1937_);
    return v_res_1946_;
}
pub unsafe fn l_Lake_querySpecs(
    mut v_specs_1947_: *mut LeanObject,
    mut v_fmt_1948_: u8,
    mut v_a_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1956_: usize = 0;
    let mut v___x_1957_: usize = 0;
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1969_: u8 = 0;
    let mut v_a_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1956_ = lean_array_size(v_specs_1947_);
                v___x_1957_ = 0usize;
                v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_querySpecs_spec__0(v_fmt_1948_, v_sz_1956_, v___x_1957_, v_specs_1947_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
                if lean_obj_tag(v___x_1958_) == 0 {
                    v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
                    v_a_1960_ = lean_ctor_get(v___x_1958_, 1);
                    v_isSharedCheck_1969_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_1969_ == 0 {
                        v___x_1962_ = v___x_1958_;
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1960_);
                        lean_inc(v_a_1959_);
                        lean_dec(v___x_1958_);
                        v___x_1962_ = lean_box(0);
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1970_ = lean_ctor_get(v___x_1958_, 0);
                    v_a_1971_ = lean_ctor_get(v___x_1958_, 1);
                    v_isSharedCheck_1978_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_1978_ == 0 {
                        v___x_1973_ = v___x_1958_;
                        v_isShared_1974_ = v_isSharedCheck_1978_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1971_);
                        lean_inc(v_a_1970_);
                        lean_dec(v___x_1958_);
                        v___x_1973_ = lean_box(0);
                        v_isShared_1974_ = v_isSharedCheck_1978_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1964_ = l_Lake_buildSpecs___closed__0;
                v___x_1965_ = l_Lake_Job_collectArray___redArg(v_a_1959_, v___x_1964_);
                lean_dec(v_a_1959_);
                if v_isShared_1963_ == 0 {
                    lean_ctor_set(v___x_1962_, 0, v___x_1965_);
                    v___x_1967_ = v___x_1962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
                    lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1960_);
                    v___x_1967_ = v_reuseFailAlloc_1968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1967_;
            }
            3 => {
                if v_isShared_1974_ == 0 {
                    v___x_1976_ = v___x_1973_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1970_);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_a_1971_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_querySpecs___boxed(
    mut v_specs_1979_: *mut LeanObject,
    mut v_fmt_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1988_: u8 = 0;
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1988_ = (lean_unbox(v_fmt_1980_) as u8);
    v_res_1989_ = l_Lake_querySpecs(
        v_specs_1979_,
        v_fmt_boxed_1988_,
        v_a_1981_,
        v_a_1982_,
        v_a_1983_,
        v_a_1984_,
        v_a_1985_,
        v_a_1986_,
    );
    lean_dec_ref(v_a_1985_);
    lean_dec(v_a_1984_);
    lean_dec(v_a_1983_);
    lean_dec(v_a_1982_);
    return v_res_1989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(
    mut v___x_1993_: *mut LeanObject,
    mut v_as_1994_: *mut LeanObject,
    mut v_sz_1995_: usize,
    mut v_i_1996_: usize,
    mut v_b_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1998_: u8 = 0;
    let mut v_a_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: usize = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1998_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
                if v___x_1998_ == 0 {
                    lean_inc_ref(v_b_1997_);
                    return v_b_1997_;
                } else {
                    v_a_1999_ = lean_array_uget_borrowed(v_as_1994_, v_i_1996_);
                    v_baseName_2000_ = lean_ctor_get(v_a_1999_, 1);
                    v___x_2001_ = lean_box(0);
                    v___x_2002_ = lean_name_eq(v_baseName_2000_, v___x_1993_);
                    if v___x_2002_ == 0 {
                        v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0;
                        v___x_2004_ = 1usize;
                        v___x_2005_ = lean_usize_add(v_i_1996_, v___x_2004_);
                        v_i_1996_ = v___x_2005_;
                        v_b_1997_ = v___x_2003_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_a_1999_);
                        v___x_2007_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2007_, 0, v_a_1999_);
                        v___x_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2008_, 0, v___x_2007_);
                        v___x_2009_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2009_, 0, v___x_2008_);
                        lean_ctor_set(v___x_2009_, 1, v___x_2001_);
                        return v___x_2009_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___boxed(
    mut v___x_2010_: *mut LeanObject,
    mut v_as_2011_: *mut LeanObject,
    mut v_sz_2012_: *mut LeanObject,
    mut v_i_2013_: *mut LeanObject,
    mut v_b_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2015_: usize = 0;
    let mut v_i_boxed_2016_: usize = 0;
    let mut v_res_2017_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2012_);
    lean_dec(v_sz_2012_);
    v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
    lean_dec(v_i_2013_);
    v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_2010_, v_as_2011_, v_sz_boxed_2015_, v_i_boxed_2016_, v_b_2014_);
    lean_dec_ref(v_b_2014_);
    lean_dec_ref(v_as_2011_);
    lean_dec(v___x_2010_);
    return v_res_2017_;
}
pub unsafe fn l_Lake_parsePackageSpec(
    mut v_ws_2018_: *mut LeanObject,
    mut v_spec_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v_packages_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2029_: usize = 0;
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_packages_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2023_ = lean_string_utf8_byte_size(v_spec_2019_);
                v___x_2024_ = lean_unsigned_to_nat(0);
                v___x_2025_ = lean_nat_dec_eq(v___x_2023_, v___x_2024_);
                if v___x_2025_ == 0 {
                    v_packages_2026_ = lean_ctor_get(v_ws_2018_, 4);
                    lean_inc_ref(v_spec_2019_);
                    v___x_2027_ = l_Lake_stringToLegalOrSimpleName(v_spec_2019_);
                    v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0;
                    v_sz_2029_ = lean_array_size(v_packages_2026_);
                    v___x_2030_ = 0usize;
                    v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v___x_2027_, v_packages_2026_, v_sz_2029_, v___x_2030_, v___x_2028_);
                    lean_dec(v___x_2027_);
                    v_fst_2032_ = lean_ctor_get(v___x_2031_, 0);
                    lean_inc(v_fst_2032_);
                    lean_dec_ref(v___x_2031_);
                    if lean_obj_tag(v_fst_2032_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2033_ = lean_ctor_get(v_fst_2032_, 0);
                        lean_inc(v_val_2033_);
                        lean_dec_ref_known(v_fst_2032_, 1);
                        if lean_obj_tag(v_val_2033_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_spec_2019_);
                            v_val_2034_ = lean_ctor_get(v_val_2033_, 0);
                            v_isSharedCheck_2041_ = (!lean_is_exclusive(v_val_2033_)) as u8;
                            if v_isSharedCheck_2041_ == 0 {
                                v___x_2036_ = v_val_2033_;
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_2034_);
                                lean_dec(v_val_2033_);
                                v___x_2036_ = lean_box(0);
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_spec_2019_);
                    v_packages_2042_ = lean_ctor_get(v_ws_2018_, 4);
                    v___x_2043_ = lean_array_fget_borrowed(v_packages_2042_, v___x_2024_);
                    lean_inc(v___x_2043_);
                    v___x_2044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2044_, 0, v___x_2043_);
                    return v___x_2044_;
                }
            }
            1 => {
                v___x_2021_ = lean_alloc_ctor(13, 1, (0) as u32);
                lean_ctor_set(v___x_2021_, 0, v_spec_2019_);
                v___x_2022_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2022_, 0, v___x_2021_);
                return v___x_2022_;
            }
            2 => {
                if v_isShared_2037_ == 0 {
                    v___x_2039_ = v___x_2036_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_val_2034_);
                    v___x_2039_ = v_reuseFailAlloc_2040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_parsePackageSpec___boxed(
    mut v_ws_2045_: *mut LeanObject,
    mut v_spec_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2047_: *mut LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lake_parsePackageSpec(v_ws_2045_, v_spec_2046_);
    lean_dec_ref(v_ws_2045_);
    return v_res_2047_;
}
pub unsafe fn _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ = lean_box(0);
    v___x_2050_ = l_Lean_Json_compress(v___x_2049_);
    return v___x_2050_;
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(
    mut v_fmt_2051_: u8,
) -> *mut LeanObject {
    if v_fmt_2051_ == 0 {
        let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
        v___x_2052_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__0;
        return v___x_2052_;
    } else {
        let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
        v___x_2053_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1_once), _init_l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___closed__1);
        return v___x_2053_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg___boxed(
    mut v_fmt_2054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_2055_: u8 = 0;
    let mut v_res_2056_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_2055_ = (lean_unbox(v_fmt_2054_) as u8);
    v_res_2056_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_boxed_2055_);
    return v_res_2056_;
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(
    mut v_fmt_2057_: u8,
    mut v_a_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v_fmt_2057_);
    return v___x_2059_;
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___boxed(
    mut v_fmt_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_2062_: u8 = 0;
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_2062_ = (lean_unbox(v_fmt_2060_) as u8);
    v_res_2063_ =
        l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0(
            v_fmt_boxed_2062_,
            v_a_2061_,
        );
    lean_dec_ref(v_a_2061_);
    return v_res_2063_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(
    mut v___y_2064_: u8,
    mut v___y_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2066_ = l_Lake_formatQuery___at___00__private_Lake_CLI_Build_0__Lake_resolveModuleTarget_spec__0___redArg(v___y_2064_);
    return v___x_2066_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0___boxed(
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_370__boxed_2069_: u8 = 0;
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v___y_370__boxed_2069_ = (lean_unbox(v___y_2067_) as u8);
    v_res_2070_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___lam__0(
        v___y_370__boxed_2069_,
        v___y_2068_,
    );
    lean_dec_ref(v___y_2068_);
    return v_res_2070_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
    mut v_ws_2073_: *mut LeanObject,
    mut v_mod_2074_: *mut LeanObject,
    mut v_facet_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v_name_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildable_2088_: u8 = 0;
    let mut v_format_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2076_ = l_Lean_Name_isAnonymous(v_facet_2075_);
                if v___x_2076_ == 0 {
                    v___x_2077_ = l_Lake_Module_keyword;
                    lean_inc(v_facet_2075_);
                    v___x_2078_ = l_Lean_Name_append(v___x_2077_, v_facet_2075_);
                    v___x_2079_ =
                        l_Lake_Workspace_findModuleFacetConfig_x3f(v___x_2078_, v_ws_2073_);
                    if lean_obj_tag(v___x_2079_) == 1 {
                        lean_dec(v_facet_2075_);
                        v_lib_2080_ = lean_ctor_get(v_mod_2074_, 0);
                        v_pkg_2081_ = lean_ctor_get(v_lib_2080_, 0);
                        v_val_2082_ = lean_ctor_get(v___x_2079_, 0);
                        v_isSharedCheck_2096_ = (!lean_is_exclusive(v___x_2079_)) as u8;
                        if v_isSharedCheck_2096_ == 0 {
                            v___x_2084_ = v___x_2079_;
                            v_isShared_2085_ = v_isSharedCheck_2096_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2082_);
                            lean_dec(v___x_2079_);
                            v___x_2084_ = lean_box(0);
                            v_isShared_2085_ = v_isSharedCheck_2096_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2079_);
                        lean_dec(v___x_2078_);
                        lean_dec_ref(v_mod_2074_);
                        v___x_2097_ =
                            l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__0;
                        v___x_2098_ = lean_alloc_ctor(14, 2, (0) as u32);
                        lean_ctor_set(v___x_2098_, 0, v___x_2097_);
                        lean_ctor_set(v___x_2098_, 1, v_facet_2075_);
                        v___x_2099_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2099_, 0, v___x_2098_);
                        return v___x_2099_;
                    }
                } else {
                    lean_dec(v_facet_2075_);
                    v_lib_2100_ = lean_ctor_get(v_mod_2074_, 0);
                    v_pkg_2101_ = lean_ctor_get(v_lib_2100_, 0);
                    v_name_2102_ = lean_ctor_get(v_mod_2074_, 1);
                    v_keyName_2103_ = lean_ctor_get(v_pkg_2101_, 2);
                    v___f_2104_ =
                        l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___closed__1;
                    v___x_2105_ = l_Lake_Module_leanArtsFacet;
                    lean_inc(v_name_2102_);
                    lean_inc(v_keyName_2103_);
                    v___x_2106_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2106_, 0, v_keyName_2103_);
                    lean_ctor_set(v___x_2106_, 1, v_name_2102_);
                    v___x_2107_ = l_Lake_Module_keyword;
                    v___x_2108_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_2108_, 0, v___x_2106_);
                    lean_ctor_set(v___x_2108_, 1, v___x_2107_);
                    lean_ctor_set(v___x_2108_, 2, v_mod_2074_);
                    lean_ctor_set(v___x_2108_, 3, v___x_2105_);
                    v___x_2109_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_2109_, 0, v___x_2108_);
                    lean_ctor_set(v___x_2109_, 1, v___f_2104_);
                    lean_ctor_set_uint8(
                        v___x_2109_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_2076_,
                    );
                    v___x_2110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2110_, 0, v___x_2109_);
                    return v___x_2110_;
                }
            }
            1 => {
                v_name_2086_ = lean_ctor_get(v_mod_2074_, 1);
                v_keyName_2087_ = lean_ctor_get(v_pkg_2081_, 2);
                v_buildable_2088_ = lean_ctor_get_uint8(
                    v_val_2082_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_format_2089_ = lean_ctor_get(v_val_2082_, 3);
                lean_inc_ref(v_format_2089_);
                lean_dec(v_val_2082_);
                lean_inc(v_name_2086_);
                lean_inc(v_keyName_2087_);
                v___x_2090_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2090_, 0, v_keyName_2087_);
                lean_ctor_set(v___x_2090_, 1, v_name_2086_);
                v___x_2091_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_2091_, 0, v___x_2090_);
                lean_ctor_set(v___x_2091_, 1, v___x_2077_);
                lean_ctor_set(v___x_2091_, 2, v_mod_2074_);
                lean_ctor_set(v___x_2091_, 3, v___x_2078_);
                v___x_2092_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2092_, 0, v___x_2091_);
                lean_ctor_set(v___x_2092_, 1, v_format_2089_);
                lean_ctor_set_uint8(
                    v___x_2092_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_buildable_2088_,
                );
                if v_isShared_2085_ == 0 {
                    lean_ctor_set(v___x_2084_, 0, v___x_2092_);
                    v___x_2094_ = v___x_2084_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget___boxed(
    mut v_ws_2111_: *mut LeanObject,
    mut v_mod_2112_: *mut LeanObject,
    mut v_facet_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2114_: *mut LeanObject = core::ptr::null_mut();
    v_res_2114_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
        v_ws_2111_,
        v_mod_2112_,
        v_facet_2113_,
    );
    lean_dec_ref(v_ws_2111_);
    return v_res_2114_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(
    mut v_pkg_2115_: *mut LeanObject,
    mut v_name_2116_: *mut LeanObject,
    mut v_facet_2117_: *mut LeanObject,
    mut v_config_2118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_format_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2131_: u8 = 0;
    let mut v_unused_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2119_ = l_Lean_Name_isAnonymous(v_facet_2117_);
                if v___x_2119_ == 0 {
                    lean_dec_ref(v_config_2118_);
                    lean_dec_ref(v_pkg_2115_);
                    v___x_2120_ = lean_alloc_ctor(20, 2, (0) as u32);
                    lean_ctor_set(v___x_2120_, 0, v_name_2116_);
                    lean_ctor_set(v___x_2120_, 1, v_facet_2117_);
                    v___x_2121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2121_, 0, v___x_2120_);
                    return v___x_2121_;
                } else {
                    lean_dec(v_facet_2117_);
                    v_format_2122_ = lean_ctor_get(v_config_2118_, 1);
                    v_isSharedCheck_2131_ = (!lean_is_exclusive(v_config_2118_)) as u8;
                    if v_isSharedCheck_2131_ == 0 {
                        v_unused_2132_ = lean_ctor_get(v_config_2118_, 0);
                        lean_dec(v_unused_2132_);
                        v___x_2124_ = v_config_2118_;
                        v_isShared_2125_ = v_isSharedCheck_2131_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_format_2122_);
                        lean_dec(v_config_2118_);
                        v___x_2124_ = lean_box(0);
                        v_isShared_2125_ = v_isSharedCheck_2131_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2125_ == 0 {
                    lean_ctor_set(v___x_2124_, 1, v_name_2116_);
                    lean_ctor_set(v___x_2124_, 0, v_pkg_2115_);
                    v___x_2127_ = v___x_2124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_pkg_2115_);
                    lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_name_2116_);
                    v___x_2127_ = v_reuseFailAlloc_2130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2128_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2128_, 0, v___x_2127_);
                lean_ctor_set(v___x_2128_, 1, v_format_2122_);
                lean_ctor_set_uint8(
                    v___x_2128_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2119_,
                );
                v___x_2129_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2129_, 0, v___x_2128_);
                return v___x_2129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(
    mut v_ws_2136_: *mut LeanObject,
    mut v_pkg_2137_: *mut LeanObject,
    mut v_target_2138_: *mut LeanObject,
    mut v_decl_2139_: *mut LeanObject,
    mut v_facet_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2147_: u8 = 0;
    let mut v___x_2148_: u8 = 0;
    let mut v___y_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v_keyName_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildable_2159_: u8 = 0;
    let mut v_format_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tgt_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_a_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut v_unused_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2141_ = lean_ctor_get(v_decl_2139_, 1);
                v_kind_2142_ = lean_ctor_get(v_decl_2139_, 2);
                v_config_2143_ = lean_ctor_get(v_decl_2139_, 3);
                v_isSharedCheck_2199_ = (!lean_is_exclusive(v_decl_2139_)) as u8;
                if v_isSharedCheck_2199_ == 0 {
                    v_unused_2200_ = lean_ctor_get(v_decl_2139_, 0);
                    lean_dec(v_unused_2200_);
                    v___x_2145_ = v_decl_2139_;
                    v_isShared_2146_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_config_2143_);
                    lean_inc(v_kind_2142_);
                    lean_inc(v_name_2141_);
                    lean_dec(v_decl_2139_);
                    v___x_2145_ = lean_box(0);
                    v_isShared_2146_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2147_ = l_Lean_Name_isAnonymous(v_kind_2142_);
                if v___x_2147_ == 0 {
                    lean_dec(v_target_2138_);
                    v___x_2148_ = 1;
                    v___x_2177_ = l_Lean_Name_isAnonymous(v_facet_2140_);
                    if v___x_2177_ == 0 {
                        v___y_2150_ = v_facet_2140_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_facet_2140_);
                        v___x_2178_ =
                            l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___closed__1;
                        v___y_2150_ = v___x_2178_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2145_);
                    lean_dec(v_kind_2142_);
                    lean_dec(v_name_2141_);
                    v___x_2179_ = l___private_Lake_CLI_Build_0__Lake_resolveCustomTarget(
                        v_pkg_2137_,
                        v_target_2138_,
                        v_facet_2140_,
                        v_config_2143_,
                    );
                    if lean_obj_tag(v___x_2179_) == 0 {
                        v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
                        v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2179_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2179_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2180_);
                            lean_dec(v___x_2179_);
                            v___x_2182_ = lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2188_ = lean_ctor_get(v___x_2179_, 0);
                        v_isSharedCheck_2198_ = (!lean_is_exclusive(v___x_2179_)) as u8;
                        if v_isSharedCheck_2198_ == 0 {
                            v___x_2190_ = v___x_2179_;
                            v_isShared_2191_ = v_isSharedCheck_2198_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2188_);
                            lean_dec(v___x_2179_);
                            v___x_2190_ = lean_box(0);
                            v_isShared_2191_ = v_isSharedCheck_2198_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_facetConfigs_2151_ = lean_ctor_get(v_ws_2136_, 6);
                lean_inc(v___y_2150_);
                lean_inc(v_kind_2142_);
                v___x_2152_ = l_Lean_Name_append(v_kind_2142_, v___y_2150_);
                v___x_2153_ = l_Lake_FacetConfigMap_get_x3f(v___x_2152_, v_facetConfigs_2151_);
                if lean_obj_tag(v___x_2153_) == 1 {
                    lean_dec(v___y_2150_);
                    v_val_2154_ = lean_ctor_get(v___x_2153_, 0);
                    v_isSharedCheck_2173_ = (!lean_is_exclusive(v___x_2153_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2156_ = v___x_2153_;
                        v_isShared_2157_ = v_isSharedCheck_2173_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2154_);
                        lean_dec(v___x_2153_);
                        v___x_2156_ = lean_box(0);
                        v_isShared_2157_ = v_isSharedCheck_2173_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2153_);
                    lean_dec(v___x_2152_);
                    lean_del_object(v___x_2145_);
                    lean_dec(v_config_2143_);
                    lean_dec(v_name_2141_);
                    lean_dec_ref(v_pkg_2137_);
                    v___x_2174_ = l_Lean_Name_toString(v_kind_2142_, v___x_2148_);
                    v___x_2175_ = lean_alloc_ctor(14, 2, (0) as u32);
                    lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                    lean_ctor_set(v___x_2175_, 1, v___y_2150_);
                    v___x_2176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2176_, 0, v___x_2175_);
                    return v___x_2176_;
                }
            }
            3 => {
                v_keyName_2158_ = lean_ctor_get(v_pkg_2137_, 2);
                lean_inc(v_keyName_2158_);
                v_buildable_2159_ = lean_ctor_get_uint8(
                    v_val_2154_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_format_2160_ = lean_ctor_get(v_val_2154_, 3);
                lean_inc_ref(v_format_2160_);
                lean_dec(v_val_2154_);
                lean_inc(v_name_2141_);
                v_tgt_2161_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v_tgt_2161_, 0, v_pkg_2137_);
                lean_ctor_set(v_tgt_2161_, 1, v_name_2141_);
                lean_ctor_set(v_tgt_2161_, 2, v_config_2143_);
                v___x_2162_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_2162_, 0, v_keyName_2158_);
                lean_ctor_set(v___x_2162_, 1, v_name_2141_);
                if v_isShared_2146_ == 0 {
                    lean_ctor_set_tag(v___x_2145_, 1);
                    lean_ctor_set(v___x_2145_, 3, v___x_2152_);
                    lean_ctor_set(v___x_2145_, 2, v_tgt_2161_);
                    lean_ctor_set(v___x_2145_, 1, v_kind_2142_);
                    lean_ctor_set(v___x_2145_, 0, v___x_2162_);
                    v_info_2164_ = v___x_2145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2162_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_kind_2142_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_tgt_2161_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 3, v___x_2152_);
                    v_info_2164_ = v_reuseFailAlloc_2172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2165_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2165_, 0, v_info_2164_);
                lean_ctor_set(v___x_2165_, 1, v_format_2160_);
                lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_buildable_2159_,
                );
                v___x_2166_ = lean_unsigned_to_nat(1);
                v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
                v___x_2168_ = lean_array_push(v___x_2167_, v___x_2165_);
                if v_isShared_2157_ == 0 {
                    lean_ctor_set(v___x_2156_, 0, v___x_2168_);
                    v___x_2170_ = v___x_2156_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2170_;
            }
            6 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2185_;
            }
            8 => {
                v___x_2192_ = lean_unsigned_to_nat(1);
                v___x_2193_ = lean_mk_empty_array_with_capacity(v___x_2192_);
                v___x_2194_ = lean_array_push(v___x_2193_, v_a_2188_);
                if v_isShared_2191_ == 0 {
                    lean_ctor_set(v___x_2190_, 0, v___x_2194_);
                    v___x_2196_ = v___x_2190_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget___boxed(
    mut v_ws_2201_: *mut LeanObject,
    mut v_pkg_2202_: *mut LeanObject,
    mut v_target_2203_: *mut LeanObject,
    mut v_decl_2204_: *mut LeanObject,
    mut v_facet_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2206_: *mut LeanObject = core::ptr::null_mut();
    v_res_2206_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(
        v_ws_2201_,
        v_pkg_2202_,
        v_target_2203_,
        v_decl_2204_,
        v_facet_2205_,
    );
    lean_dec_ref(v_ws_2201_);
    return v_res_2206_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(
    mut v_ws_2207_: *mut LeanObject,
    mut v_pkg_2208_: *mut LeanObject,
    mut v_target_2209_: *mut LeanObject,
    mut v_facet_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_a_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_baseName_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2211_ = l_Lake_Package_findTargetDecl_x3f(v_target_2209_, v_pkg_2208_);
                if lean_obj_tag(v___x_2211_) == 1 {
                    v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
                    lean_inc(v_val_2212_);
                    lean_dec_ref_known(v___x_2211_, 1);
                    v___x_2213_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(
                        v_ws_2207_,
                        v_pkg_2208_,
                        v_target_2209_,
                        v_val_2212_,
                        v_facet_2210_,
                    );
                    return v___x_2213_;
                } else {
                    lean_dec(v___x_2211_);
                    lean_inc_ref(v_pkg_2208_);
                    lean_inc(v_target_2209_);
                    v___x_2214_ = l_Lake_Package_findTargetModule_x3f(v_target_2209_, v_pkg_2208_);
                    if lean_obj_tag(v___x_2214_) == 1 {
                        lean_dec(v_target_2209_);
                        lean_dec_ref(v_pkg_2208_);
                        v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
                        lean_inc(v_val_2215_);
                        lean_dec_ref_known(v___x_2214_, 1);
                        v___x_2216_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
                            v_ws_2207_,
                            v_val_2215_,
                            v_facet_2210_,
                        );
                        if lean_obj_tag(v___x_2216_) == 0 {
                            v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
                            v_isSharedCheck_2224_ = (!lean_is_exclusive(v___x_2216_)) as u8;
                            if v_isSharedCheck_2224_ == 0 {
                                v___x_2219_ = v___x_2216_;
                                v_isShared_2220_ = v_isSharedCheck_2224_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2217_);
                                lean_dec(v___x_2216_);
                                v___x_2219_ = lean_box(0);
                                v_isShared_2220_ = v_isSharedCheck_2224_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2225_ = lean_ctor_get(v___x_2216_, 0);
                            v_isSharedCheck_2235_ = (!lean_is_exclusive(v___x_2216_)) as u8;
                            if v_isSharedCheck_2235_ == 0 {
                                v___x_2227_ = v___x_2216_;
                                v_isShared_2228_ = v_isSharedCheck_2235_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2225_);
                                lean_dec(v___x_2216_);
                                v___x_2227_ = lean_box(0);
                                v_isShared_2228_ = v_isSharedCheck_2235_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2214_);
                        lean_dec(v_facet_2210_);
                        v_baseName_2236_ = lean_ctor_get(v_pkg_2208_, 1);
                        lean_inc(v_baseName_2236_);
                        lean_dec_ref(v_pkg_2208_);
                        v___x_2237_ = 0;
                        v___x_2238_ = l_Lean_Name_toString(v_target_2209_, v___x_2237_);
                        v___x_2239_ = lean_alloc_ctor(17, 2, (0) as u32);
                        lean_ctor_set(v___x_2239_, 0, v_baseName_2236_);
                        lean_ctor_set(v___x_2239_, 1, v___x_2238_);
                        v___x_2240_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2240_, 0, v___x_2239_);
                        return v___x_2240_;
                    }
                }
            }
            1 => {
                if v_isShared_2220_ == 0 {
                    v___x_2222_ = v___x_2219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
                    v___x_2222_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2222_;
            }
            3 => {
                v___x_2229_ = lean_unsigned_to_nat(1);
                v___x_2230_ = lean_mk_empty_array_with_capacity(v___x_2229_);
                v___x_2231_ = lean_array_push(v___x_2230_, v_a_2225_);
                if v_isShared_2228_ == 0 {
                    lean_ctor_set(v___x_2227_, 0, v___x_2231_);
                    v___x_2233_ = v___x_2227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage___boxed(
    mut v_ws_2241_: *mut LeanObject,
    mut v_pkg_2242_: *mut LeanObject,
    mut v_target_2243_: *mut LeanObject,
    mut v_facet_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2245_: *mut LeanObject = core::ptr::null_mut();
    v_res_2245_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(
        v_ws_2241_,
        v_pkg_2242_,
        v_target_2243_,
        v_facet_2244_,
    );
    lean_dec_ref(v_ws_2241_);
    return v_res_2245_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(
    mut v_ws_2246_: *mut LeanObject,
    mut v_pkg_2247_: *mut LeanObject,
    mut v_as_2248_: *mut LeanObject,
    mut v_i_2249_: usize,
    mut v_stop_2250_: usize,
    mut v_b_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2257_ = lean_usize_dec_eq(v_i_2249_, v_stop_2250_);
                if v___x_2257_ == 0 {
                    v___x_2258_ = lean_array_uget_borrowed(v_as_2248_, v_i_2249_);
                    v___x_2259_ = lean_box(0);
                    lean_inc(v___x_2258_);
                    lean_inc_ref(v_pkg_2247_);
                    v___x_2260_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(
                        v_ws_2246_,
                        v_pkg_2247_,
                        v___x_2258_,
                        v___x_2259_,
                    );
                    if lean_obj_tag(v___x_2260_) == 0 {
                        lean_dec_ref(v_b_2251_);
                        if lean_obj_tag(v___x_2260_) == 0 {
                            lean_dec_ref(v_pkg_2247_);
                            return v___x_2260_;
                        } else {
                            v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
                            lean_inc(v_a_2261_);
                            lean_dec_ref_known(v___x_2260_, 1);
                            v_a_2253_ = v_a_2261_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2262_ = lean_ctor_get(v___x_2260_, 0);
                        lean_inc(v_a_2262_);
                        lean_dec_ref_known(v___x_2260_, 1);
                        v___x_2263_ = l_Array_append___redArg(v_b_2251_, v_a_2262_);
                        lean_dec(v_a_2262_);
                        v_a_2253_ = v___x_2263_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_2247_);
                    v___x_2264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2264_, 0, v_b_2251_);
                    return v___x_2264_;
                }
            }
            1 => {
                v___x_2254_ = 1usize;
                v___x_2255_ = lean_usize_add(v_i_2249_, v___x_2254_);
                v_i_2249_ = v___x_2255_;
                v_b_2251_ = v_a_2253_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0___boxed(
    mut v_ws_2265_: *mut LeanObject,
    mut v_pkg_2266_: *mut LeanObject,
    mut v_as_2267_: *mut LeanObject,
    mut v_i_2268_: *mut LeanObject,
    mut v_stop_2269_: *mut LeanObject,
    mut v_b_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2271_: usize = 0;
    let mut v_stop_boxed_2272_: usize = 0;
    let mut v_res_2273_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2271_ = lean_unbox_usize(v_i_2268_);
    lean_dec(v_i_2268_);
    v_stop_boxed_2272_ = lean_unbox_usize(v_stop_2269_);
    lean_dec(v_stop_2269_);
    v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_2265_, v_pkg_2266_, v_as_2267_, v_i_boxed_2271_, v_stop_boxed_2272_, v_b_2270_);
    lean_dec_ref(v_as_2267_);
    lean_dec_ref(v_ws_2265_);
    return v_res_2273_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(
    mut v_ws_2278_: *mut LeanObject,
    mut v_pkg_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defaultTargets_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    v_defaultTargets_2280_ = lean_ctor_get(v_pkg_2279_, 16);
    lean_inc_ref(v_defaultTargets_2280_);
    v___x_2281_ = lean_unsigned_to_nat(0);
    v___x_2282_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__0;
    v___x_2283_ = lean_array_get_size(v_defaultTargets_2280_);
    v___x_2284_ = lean_nat_dec_lt(v___x_2281_, v___x_2283_);
    if v___x_2284_ == 0 {
        let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_defaultTargets_2280_);
        lean_dec_ref(v_pkg_2279_);
        v___x_2285_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
        return v___x_2285_;
    } else {
        let mut v___x_2286_: u8 = 0;
        v___x_2286_ = lean_nat_dec_le(v___x_2283_, v___x_2283_);
        if v___x_2286_ == 0 {
            if v___x_2284_ == 0 {
                let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_defaultTargets_2280_);
                lean_dec_ref(v_pkg_2279_);
                v___x_2287_ =
                    l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___closed__1;
                return v___x_2287_;
            } else {
                let mut v___x_2288_: usize = 0;
                let mut v___x_2289_: usize = 0;
                let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
                v___x_2288_ = 0usize;
                v___x_2289_ = lean_usize_of_nat(v___x_2283_);
                v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_2278_, v_pkg_2279_, v_defaultTargets_2280_, v___x_2288_, v___x_2289_, v___x_2282_);
                lean_dec_ref(v_defaultTargets_2280_);
                return v___x_2290_;
            }
        } else {
            let mut v___x_2291_: usize = 0;
            let mut v___x_2292_: usize = 0;
            let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
            v___x_2291_ = 0usize;
            v___x_2292_ = lean_usize_of_nat(v___x_2283_);
            v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget_spec__0(v_ws_2278_, v_pkg_2279_, v_defaultTargets_2280_, v___x_2291_, v___x_2292_, v___x_2282_);
            lean_dec_ref(v_defaultTargets_2280_);
            return v___x_2293_;
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget___boxed(
    mut v_ws_2294_: *mut LeanObject,
    mut v_pkg_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v_res_2296_ =
        l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(v_ws_2294_, v_pkg_2295_);
    lean_dec_ref(v_ws_2294_);
    return v_res_2296_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
    mut v_ws_2298_: *mut LeanObject,
    mut v_pkg_2299_: *mut LeanObject,
    mut v_facet_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_keyName_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildable_2310_: u8 = 0;
    let mut v_format_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2301_ = l_Lean_Name_isAnonymous(v_facet_2300_);
                if v___x_2301_ == 0 {
                    v___x_2302_ = l_Lake_Package_keyword;
                    lean_inc(v_facet_2300_);
                    v___x_2303_ = l_Lean_Name_append(v___x_2302_, v_facet_2300_);
                    v___x_2304_ =
                        l_Lake_Workspace_findPackageFacetConfig_x3f(v___x_2303_, v_ws_2298_);
                    if lean_obj_tag(v___x_2304_) == 1 {
                        lean_dec(v_facet_2300_);
                        v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2321_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2321_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2321_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2305_);
                            lean_dec(v___x_2304_);
                            v___x_2307_ = lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2321_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2304_);
                        lean_dec(v___x_2303_);
                        lean_dec_ref(v_pkg_2299_);
                        v___x_2322_ =
                            l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___closed__0;
                        v___x_2323_ = lean_alloc_ctor(14, 2, (0) as u32);
                        lean_ctor_set(v___x_2323_, 0, v___x_2322_);
                        lean_ctor_set(v___x_2323_, 1, v_facet_2300_);
                        v___x_2324_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2324_, 0, v___x_2323_);
                        return v___x_2324_;
                    }
                } else {
                    lean_dec(v_facet_2300_);
                    v___x_2325_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(
                        v_ws_2298_,
                        v_pkg_2299_,
                    );
                    return v___x_2325_;
                }
            }
            1 => {
                v_keyName_2309_ = lean_ctor_get(v_pkg_2299_, 2);
                v_buildable_2310_ = lean_ctor_get_uint8(
                    v_val_2305_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_format_2311_ = lean_ctor_get(v_val_2305_, 3);
                lean_inc_ref(v_format_2311_);
                lean_dec(v_val_2305_);
                lean_inc(v_keyName_2309_);
                if v_isShared_2308_ == 0 {
                    lean_ctor_set(v___x_2307_, 0, v_keyName_2309_);
                    v___x_2313_ = v___x_2307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_keyName_2309_);
                    v___x_2313_ = v_reuseFailAlloc_2320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2314_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_2314_, 0, v___x_2313_);
                lean_ctor_set(v___x_2314_, 1, v___x_2302_);
                lean_ctor_set(v___x_2314_, 2, v_pkg_2299_);
                lean_ctor_set(v___x_2314_, 3, v___x_2303_);
                v___x_2315_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2315_, 0, v___x_2314_);
                lean_ctor_set(v___x_2315_, 1, v_format_2311_);
                lean_ctor_set_uint8(
                    v___x_2315_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_buildable_2310_,
                );
                v___x_2316_ = lean_unsigned_to_nat(1);
                v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
                v___x_2318_ = lean_array_push(v___x_2317_, v___x_2315_);
                v___x_2319_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2319_, 0, v___x_2318_);
                return v___x_2319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget___boxed(
    mut v_ws_2326_: *mut LeanObject,
    mut v_pkg_2327_: *mut LeanObject,
    mut v_facet_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
        v_ws_2326_,
        v_pkg_2327_,
        v_facet_2328_,
    );
    lean_dec_ref(v_ws_2326_);
    return v_res_2329_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(
    mut v_ws_2330_: *mut LeanObject,
    mut v_target_2331_: *mut LeanObject,
    mut v_facet_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut v_a_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2365_: usize = 0;
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = l_Lake_Workspace_findTargetDecl_x3f(v_target_2331_, v_ws_2330_);
                if lean_obj_tag(v___x_2358_) == 1 {
                    v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
                    lean_inc(v_val_2359_);
                    lean_dec_ref_known(v___x_2358_, 1);
                    v_fst_2360_ = lean_ctor_get(v_val_2359_, 0);
                    lean_inc(v_fst_2360_);
                    v_snd_2361_ = lean_ctor_get(v_val_2359_, 1);
                    lean_inc(v_snd_2361_);
                    lean_dec(v_val_2359_);
                    v___x_2362_ = l___private_Lake_CLI_Build_0__Lake_resolveConfigDeclTarget(
                        v_ws_2330_,
                        v_fst_2360_,
                        v_target_2331_,
                        v_snd_2361_,
                        v_facet_2332_,
                    );
                    return v___x_2362_;
                } else {
                    lean_dec(v___x_2358_);
                    v_packages_2363_ = lean_ctor_get(v_ws_2330_, 4);
                    v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0___closed__0;
                    v_sz_2365_ = lean_array_size(v_packages_2363_);
                    v___x_2366_ = 0usize;
                    v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_parsePackageSpec_spec__0(v_target_2331_, v_packages_2363_, v_sz_2365_, v___x_2366_, v___x_2364_);
                    v_fst_2368_ = lean_ctor_get(v___x_2367_, 0);
                    lean_inc(v_fst_2368_);
                    lean_dec_ref(v___x_2367_);
                    if lean_obj_tag(v_fst_2368_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2369_ = lean_ctor_get(v_fst_2368_, 0);
                        lean_inc(v_val_2369_);
                        lean_dec_ref_known(v_fst_2368_, 1);
                        if lean_obj_tag(v_val_2369_) == 1 {
                            lean_dec(v_target_2331_);
                            v_val_2370_ = lean_ctor_get(v_val_2369_, 0);
                            lean_inc(v_val_2370_);
                            lean_dec_ref_known(v_val_2369_, 1);
                            v___x_2371_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
                                v_ws_2330_,
                                v_val_2370_,
                                v_facet_2332_,
                            );
                            return v___x_2371_;
                        } else {
                            lean_dec(v_val_2369_);
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_target_2331_);
                v___x_2334_ = l_Lake_Workspace_findTargetModule_x3f(v_target_2331_, v_ws_2330_);
                if lean_obj_tag(v___x_2334_) == 1 {
                    lean_dec(v_target_2331_);
                    v_val_2335_ = lean_ctor_get(v___x_2334_, 0);
                    lean_inc(v_val_2335_);
                    lean_dec_ref_known(v___x_2334_, 1);
                    v___x_2336_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
                        v_ws_2330_,
                        v_val_2335_,
                        v_facet_2332_,
                    );
                    if lean_obj_tag(v___x_2336_) == 0 {
                        v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
                        v_isSharedCheck_2344_ = (!lean_is_exclusive(v___x_2336_)) as u8;
                        if v_isSharedCheck_2344_ == 0 {
                            v___x_2339_ = v___x_2336_;
                            v_isShared_2340_ = v_isSharedCheck_2344_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2337_);
                            lean_dec(v___x_2336_);
                            v___x_2339_ = lean_box(0);
                            v_isShared_2340_ = v_isSharedCheck_2344_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
                        v_isSharedCheck_2355_ = (!lean_is_exclusive(v___x_2336_)) as u8;
                        if v_isSharedCheck_2355_ == 0 {
                            v___x_2347_ = v___x_2336_;
                            v_isShared_2348_ = v_isSharedCheck_2355_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2345_);
                            lean_dec(v___x_2336_);
                            v___x_2347_ = lean_box(0);
                            v_isShared_2348_ = v_isSharedCheck_2355_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2334_);
                    lean_dec(v_facet_2332_);
                    v___x_2356_ = lean_alloc_ctor(15, 1, (0) as u32);
                    lean_ctor_set(v___x_2356_, 0, v_target_2331_);
                    v___x_2357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2357_, 0, v___x_2356_);
                    return v___x_2357_;
                }
            }
            2 => {
                if v_isShared_2340_ == 0 {
                    v___x_2342_ = v___x_2339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2342_;
            }
            4 => {
                v___x_2349_ = lean_unsigned_to_nat(1);
                v___x_2350_ = lean_mk_empty_array_with_capacity(v___x_2349_);
                v___x_2351_ = lean_array_push(v___x_2350_, v_a_2345_);
                if v_isShared_2348_ == 0 {
                    lean_ctor_set(v___x_2347_, 0, v___x_2351_);
                    v___x_2353_ = v___x_2347_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
                    v___x_2353_ = v_reuseFailAlloc_2354_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace___boxed(
    mut v_ws_2372_: *mut LeanObject,
    mut v_target_2373_: *mut LeanObject,
    mut v_facet_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2375_: *mut LeanObject = core::ptr::null_mut();
    v_res_2375_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(
        v_ws_2372_,
        v_target_2373_,
        v_facet_2374_,
    );
    lean_dec_ref(v_ws_2372_);
    return v_res_2375_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(
    mut v_s_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
    return v___x_2379_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___boxed(
    mut v_s_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2381_: *mut LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v_s_2380_);
    lean_dec_ref(v_s_2380_);
    return v_res_2381_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(
    mut v_spec_2382_: *mut LeanObject,
    mut v___x_2383_: *mut LeanObject,
    mut v___x_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_b_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v_startInclusive_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: u32 = 0;
    let mut v___x_2404_: u32 = 0;
    let mut v___x_2405_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2385_) == 0 {
                    v_currPos_2394_ = lean_ctor_get(v_a_2385_, 0);
                    v_searcher_2395_ = lean_ctor_get(v_a_2385_, 1);
                    v_isSharedCheck_2421_ = (!lean_is_exclusive(v_a_2385_)) as u8;
                    if v_isSharedCheck_2421_ == 0 {
                        v___x_2397_ = v_a_2385_;
                        v_isShared_2398_ = v_isSharedCheck_2421_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_2395_);
                        lean_inc(v_currPos_2394_);
                        lean_dec(v_a_2385_);
                        v___x_2397_ = lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2421_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2384_);
                    lean_dec_ref(v_spec_2382_);
                    return v_b_2386_;
                }
            }
            1 => {
                lean_inc_ref(v_spec_2382_);
                v___x_2391_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2391_, 0, v_spec_2382_);
                lean_ctor_set(v___x_2391_, 1, v_startInclusive_2389_);
                lean_ctor_set(v___x_2391_, 2, v_endExclusive_2390_);
                v___x_2392_ = lean_array_push(v_b_2386_, v___x_2391_);
                v_a_2385_ = v_it_2388_;
                v_b_2386_ = v___x_2392_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2399_ = lean_ctor_get(v___x_2383_, 1);
                v_endExclusive_2400_ = lean_ctor_get(v___x_2383_, 2);
                v___x_2401_ = lean_nat_sub(v_endExclusive_2400_, v_startInclusive_2399_);
                v___x_2402_ = lean_nat_dec_eq(v_searcher_2395_, v___x_2401_);
                lean_dec(v___x_2401_);
                if v___x_2402_ == 0 {
                    v___x_2403_ = 47;
                    v___x_2404_ = lean_string_utf8_get_fast(v_spec_2382_, v_searcher_2395_);
                    v___x_2405_ = lean_uint32_dec_eq(v___x_2404_, v___x_2403_);
                    if v___x_2405_ == 0 {
                        v___x_2406_ = lean_string_utf8_next_fast(v_spec_2382_, v_searcher_2395_);
                        lean_dec(v_searcher_2395_);
                        if v_isShared_2398_ == 0 {
                            lean_ctor_set(v___x_2397_, 1, v___x_2406_);
                            v___x_2408_ = v___x_2397_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_currPos_2394_);
                            lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2406_);
                            v___x_2408_ = v_reuseFailAlloc_2410_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2411_ = lean_string_utf8_next_fast(v_spec_2382_, v_searcher_2395_);
                        v___x_2412_ = lean_nat_sub(v___x_2411_, v_searcher_2395_);
                        v___x_2413_ = lean_nat_add(v_searcher_2395_, v___x_2412_);
                        lean_dec(v___x_2412_);
                        v_slice_2414_ = l_String_Slice_subslice_x21(
                            v___x_2383_,
                            v_currPos_2394_,
                            v_searcher_2395_,
                        );
                        lean_inc(v___x_2413_);
                        if v_isShared_2398_ == 0 {
                            lean_ctor_set(v___x_2397_, 1, v___x_2413_);
                            lean_ctor_set(v___x_2397_, 0, v___x_2413_);
                            v_nextIt_2416_ = v___x_2397_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2413_);
                            lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2413_);
                            v_nextIt_2416_ = v_reuseFailAlloc_2419_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2397_);
                    lean_dec(v_searcher_2395_);
                    v___x_2420_ = lean_box(1);
                    lean_inc(v___x_2384_);
                    v_it_2388_ = v___x_2420_;
                    v_startInclusive_2389_ = v_currPos_2394_;
                    v_endExclusive_2390_ = v___x_2384_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_2385_ = v___x_2408_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_2417_ = lean_ctor_get(v_slice_2414_, 0);
                lean_inc(v_startInclusive_2417_);
                v_endExclusive_2418_ = lean_ctor_get(v_slice_2414_, 1);
                lean_inc(v_endExclusive_2418_);
                lean_dec_ref(v_slice_2414_);
                v_it_2388_ = v_nextIt_2416_;
                v_startInclusive_2389_ = v_startInclusive_2417_;
                v_endExclusive_2390_ = v_endExclusive_2418_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg___boxed(
    mut v_spec_2422_: *mut LeanObject,
    mut v___x_2423_: *mut LeanObject,
    mut v___x_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
    mut v_b_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2427_: *mut LeanObject = core::ptr::null_mut();
    v_res_2427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_2422_, v___x_2423_, v___x_2424_, v_a_2425_, v_b_2426_);
    lean_dec_ref(v___x_2423_);
    return v_res_2427_;
}
pub unsafe fn _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2()
-> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
    v___x_2432_ = lean_string_utf8_byte_size(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
    mut v_ws_2433_: *mut LeanObject,
    mut v_spec_2434_: *mut LeanObject,
    mut v_facet_2435_: *mut LeanObject,
    mut v_isMaybePath_2436_: u8,
    mut v_explicit_2437_: u8,
) -> *mut LeanObject {
    let mut v___x_2439_: u32 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_a_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_a_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v_str_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_a_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2444_ = lean_unsigned_to_nat(0);
                v___x_2445_ = lean_string_utf8_byte_size(v_spec_2434_);
                lean_inc_ref_n(v_spec_2434_, 2);
                v___x_2446_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2446_, 0, v_spec_2434_);
                lean_ctor_set(v___x_2446_, 1, v___x_2444_);
                lean_ctor_set(v___x_2446_, 2, v___x_2445_);
                v___x_2447_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_2446_);
                v___x_2448_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
                v___x_2449_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_2434_, v___x_2446_, v___x_2445_, v___x_2447_, v___x_2448_);
                lean_dec_ref_known(v___x_2446_, 3);
                v___x_2450_ = lean_array_to_list(v___x_2449_);
                if lean_obj_tag(v___x_2450_) == 1 {
                    v_tail_2451_ = lean_ctor_get(v___x_2450_, 1);
                    lean_inc(v_tail_2451_);
                    if lean_obj_tag(v_tail_2451_) == 0 {
                        lean_dec_ref(v_spec_2434_);
                        v_head_2452_ = lean_ctor_get(v___x_2450_, 0);
                        lean_inc(v_head_2452_);
                        lean_dec_ref_known(v___x_2450_, 2);
                        v_str_2453_ = lean_ctor_get(v_head_2452_, 0);
                        lean_inc_ref(v_str_2453_);
                        v_startInclusive_2454_ = lean_ctor_get(v_head_2452_, 1);
                        lean_inc(v_startInclusive_2454_);
                        v_endExclusive_2455_ = lean_ctor_get(v_head_2452_, 2);
                        lean_inc(v_endExclusive_2455_);
                        lean_dec(v_head_2452_);
                        v___x_2456_ = lean_nat_sub(v_endExclusive_2455_, v_startInclusive_2454_);
                        v___x_2457_ = lean_nat_dec_eq(v___x_2456_, v___x_2444_);
                        lean_dec(v___x_2456_);
                        if v___x_2457_ == 0 {
                            if v_explicit_2437_ == 0 {
                                v___x_2458_ = lean_string_utf8_extract(
                                    v_str_2453_,
                                    v_startInclusive_2454_,
                                    v_endExclusive_2455_,
                                );
                                lean_dec(v_endExclusive_2455_);
                                lean_dec(v_startInclusive_2454_);
                                lean_dec_ref(v_str_2453_);
                                v___x_2459_ = l_Lake_stringToLegalOrSimpleName(v___x_2458_);
                                v___x_2460_ =
                                    l___private_Lake_CLI_Build_0__Lake_resolveTargetInWorkspace(
                                        v_ws_2433_,
                                        v___x_2459_,
                                        v_facet_2435_,
                                    );
                                return v___x_2460_;
                            } else {
                                v___x_2461_ = lean_string_utf8_extract(
                                    v_str_2453_,
                                    v_startInclusive_2454_,
                                    v_endExclusive_2455_,
                                );
                                lean_dec(v_endExclusive_2455_);
                                lean_dec(v_startInclusive_2454_);
                                lean_dec_ref(v_str_2453_);
                                v___x_2462_ = l_Lake_parsePackageSpec(v_ws_2433_, v___x_2461_);
                                if lean_obj_tag(v___x_2462_) == 0 {
                                    lean_dec(v_facet_2435_);
                                    v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
                                    v_isSharedCheck_2470_ = (!lean_is_exclusive(v___x_2462_)) as u8;
                                    if v_isSharedCheck_2470_ == 0 {
                                        v___x_2465_ = v___x_2462_;
                                        v_isShared_2466_ = v_isSharedCheck_2470_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2463_);
                                        lean_dec(v___x_2462_);
                                        v___x_2465_ = lean_box(0);
                                        v_isShared_2466_ = v_isSharedCheck_2470_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_2471_ = lean_ctor_get(v___x_2462_, 0);
                                    lean_inc(v_a_2471_);
                                    lean_dec_ref_known(v___x_2462_, 1);
                                    v___x_2472_ =
                                        l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
                                            v_ws_2433_,
                                            v_a_2471_,
                                            v_facet_2435_,
                                        );
                                    return v___x_2472_;
                                }
                            }
                        } else {
                            lean_dec(v_endExclusive_2455_);
                            lean_dec(v_startInclusive_2454_);
                            lean_dec_ref(v_str_2453_);
                            v_packages_2473_ = lean_ctor_get(v_ws_2433_, 4);
                            v___x_2474_ = lean_array_fget_borrowed(v_packages_2473_, v___x_2444_);
                            lean_inc(v___x_2474_);
                            v___x_2475_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
                                v_ws_2433_,
                                v___x_2474_,
                                v_facet_2435_,
                            );
                            return v___x_2475_;
                        }
                    } else {
                        v_tail_2476_ = lean_ctor_get(v_tail_2451_, 1);
                        if lean_obj_tag(v_tail_2476_) == 0 {
                            lean_dec_ref(v_spec_2434_);
                            v_head_2477_ = lean_ctor_get(v___x_2450_, 0);
                            lean_inc(v_head_2477_);
                            lean_dec_ref_known(v___x_2450_, 2);
                            v_head_2478_ = lean_ctor_get(v_tail_2451_, 0);
                            lean_inc(v_head_2478_);
                            lean_dec_ref_known(v_tail_2451_, 2);
                            v_str_2479_ = lean_ctor_get(v_head_2477_, 0);
                            lean_inc_ref(v_str_2479_);
                            v_startInclusive_2480_ = lean_ctor_get(v_head_2477_, 1);
                            lean_inc(v_startInclusive_2480_);
                            v_endExclusive_2481_ = lean_ctor_get(v_head_2477_, 2);
                            lean_inc(v_endExclusive_2481_);
                            lean_dec(v_head_2477_);
                            v___x_2482_ = lean_string_utf8_extract(
                                v_str_2479_,
                                v_startInclusive_2480_,
                                v_endExclusive_2481_,
                            );
                            lean_dec(v_endExclusive_2481_);
                            lean_dec(v_startInclusive_2480_);
                            lean_dec_ref(v_str_2479_);
                            v___x_2483_ = l_Lake_parsePackageSpec(v_ws_2433_, v___x_2482_);
                            if lean_obj_tag(v___x_2483_) == 0 {
                                lean_dec(v_head_2478_);
                                lean_dec(v_facet_2435_);
                                v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
                                v_isSharedCheck_2491_ = (!lean_is_exclusive(v___x_2483_)) as u8;
                                if v_isSharedCheck_2491_ == 0 {
                                    v___x_2486_ = v___x_2483_;
                                    v_isShared_2487_ = v_isSharedCheck_2491_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2484_);
                                    lean_dec(v___x_2483_);
                                    v___x_2486_ = lean_box(0);
                                    v_isShared_2487_ = v_isSharedCheck_2491_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_2492_ = lean_ctor_get(v___x_2483_, 0);
                                v_isSharedCheck_2541_ = (!lean_is_exclusive(v___x_2483_)) as u8;
                                if v_isSharedCheck_2541_ == 0 {
                                    v___x_2494_ = v___x_2483_;
                                    v_isShared_2495_ = v_isSharedCheck_2541_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2492_);
                                    lean_dec(v___x_2483_);
                                    v___x_2494_ = lean_box(0);
                                    v_isShared_2495_ = v_isSharedCheck_2541_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_tail_2451_, 2);
                            lean_dec_ref_known(v___x_2450_, 2);
                            lean_dec(v_facet_2435_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2450_);
                    lean_dec(v_facet_2435_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isMaybePath_2436_ == 0 {
                    v___x_2439_ = 47;
                    v___x_2440_ = lean_alloc_ctor(19, 1, (4) as u32);
                    lean_ctor_set(v___x_2440_, 0, v_spec_2434_);
                    lean_ctor_set_uint32(
                        v___x_2440_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2439_,
                    );
                    v___x_2441_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2441_, 0, v___x_2440_);
                    return v___x_2441_;
                } else {
                    v___x_2442_ = lean_alloc_ctor(12, 1, (0) as u32);
                    lean_ctor_set(v___x_2442_, 0, v_spec_2434_);
                    v___x_2443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                    return v___x_2443_;
                }
            }
            2 => {
                if v_isShared_2466_ == 0 {
                    v___x_2468_ = v___x_2465_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2468_;
            }
            4 => {
                if v_isShared_2487_ == 0 {
                    v___x_2489_ = v___x_2486_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
                    v___x_2489_ = v_reuseFailAlloc_2490_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2489_;
            }
            6 => {
                v_str_2496_ = lean_ctor_get(v_head_2478_, 0);
                lean_inc_ref(v_str_2496_);
                v_startInclusive_2497_ = lean_ctor_get(v_head_2478_, 1);
                lean_inc(v_startInclusive_2497_);
                v_endExclusive_2498_ = lean_ctor_get(v_head_2478_, 2);
                lean_inc(v_endExclusive_2498_);
                v___x_2534_ = lean_nat_sub(v_endExclusive_2498_, v_startInclusive_2497_);
                v___x_2535_ = lean_nat_dec_eq(v___x_2534_, v___x_2444_);
                if v___x_2535_ == 0 {
                    v___x_2536_ =
                        l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
                    v___x_2537_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2), core::ptr::addr_of_mut!(l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once), _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2);
                    v___x_2538_ = lean_nat_dec_le(v___x_2537_, v___x_2534_);
                    lean_dec(v___x_2534_);
                    if v___x_2538_ == 0 {
                        v___y_2500_ = v___x_2535_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2539_ = lean_string_memcmp(
                            v_str_2496_,
                            v___x_2536_,
                            v_startInclusive_2497_,
                            v___x_2444_,
                            v___x_2537_,
                        );
                        v___y_2500_ = v___x_2539_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2534_);
                    lean_dec(v_endExclusive_2498_);
                    lean_dec(v_startInclusive_2497_);
                    lean_dec_ref(v_str_2496_);
                    lean_del_object(v___x_2494_);
                    lean_dec(v_head_2478_);
                    v___x_2540_ = l___private_Lake_CLI_Build_0__Lake_resolvePackageTarget(
                        v_ws_2433_,
                        v_a_2492_,
                        v_facet_2435_,
                    );
                    return v___x_2540_;
                }
            }
            7 => {
                if v___y_2500_ == 0 {
                    lean_del_object(v___x_2494_);
                    lean_dec(v_head_2478_);
                    v___x_2501_ = lean_string_utf8_extract(
                        v_str_2496_,
                        v_startInclusive_2497_,
                        v_endExclusive_2498_,
                    );
                    lean_dec(v_endExclusive_2498_);
                    lean_dec(v_startInclusive_2497_);
                    lean_dec_ref(v_str_2496_);
                    v___x_2502_ = l_Lake_stringToLegalOrSimpleName(v___x_2501_);
                    v___x_2503_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetInPackage(
                        v_ws_2433_,
                        v_a_2492_,
                        v___x_2502_,
                        v_facet_2435_,
                    );
                    return v___x_2503_;
                } else {
                    v___x_2504_ = lean_unsigned_to_nat(1);
                    v___x_2505_ = l_String_Slice_Pos_nextn(v_head_2478_, v___x_2444_, v___x_2504_);
                    lean_dec(v_head_2478_);
                    v___x_2506_ = lean_nat_add(v_startInclusive_2497_, v___x_2505_);
                    lean_dec(v___x_2505_);
                    lean_dec(v_startInclusive_2497_);
                    v___x_2507_ =
                        lean_string_utf8_extract(v_str_2496_, v___x_2506_, v_endExclusive_2498_);
                    lean_dec(v_endExclusive_2498_);
                    lean_dec(v___x_2506_);
                    lean_dec_ref(v_str_2496_);
                    v___x_2508_ = l_String_toName(v___x_2507_);
                    lean_inc(v___x_2508_);
                    v___x_2509_ = l_Lake_Package_findTargetModule_x3f(v___x_2508_, v_a_2492_);
                    if lean_obj_tag(v___x_2509_) == 1 {
                        lean_dec(v___x_2508_);
                        lean_del_object(v___x_2494_);
                        v_val_2510_ = lean_ctor_get(v___x_2509_, 0);
                        lean_inc(v_val_2510_);
                        lean_dec_ref_known(v___x_2509_, 1);
                        v___x_2511_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
                            v_ws_2433_,
                            v_val_2510_,
                            v_facet_2435_,
                        );
                        if lean_obj_tag(v___x_2511_) == 0 {
                            v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
                            v_isSharedCheck_2519_ = (!lean_is_exclusive(v___x_2511_)) as u8;
                            if v_isSharedCheck_2519_ == 0 {
                                v___x_2514_ = v___x_2511_;
                                v_isShared_2515_ = v_isSharedCheck_2519_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2512_);
                                lean_dec(v___x_2511_);
                                v___x_2514_ = lean_box(0);
                                v_isShared_2515_ = v_isSharedCheck_2519_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_2520_ = lean_ctor_get(v___x_2511_, 0);
                            v_isSharedCheck_2529_ = (!lean_is_exclusive(v___x_2511_)) as u8;
                            if v_isSharedCheck_2529_ == 0 {
                                v___x_2522_ = v___x_2511_;
                                v_isShared_2523_ = v_isSharedCheck_2529_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2520_);
                                lean_dec(v___x_2511_);
                                v___x_2522_ = lean_box(0);
                                v_isShared_2523_ = v_isSharedCheck_2529_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2509_);
                        lean_dec(v_facet_2435_);
                        v___x_2530_ = lean_alloc_ctor(11, 1, (0) as u32);
                        lean_ctor_set(v___x_2530_, 0, v___x_2508_);
                        if v_isShared_2495_ == 0 {
                            lean_ctor_set_tag(v___x_2494_, 0);
                            lean_ctor_set(v___x_2494_, 0, v___x_2530_);
                            v___x_2532_ = v___x_2494_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
                            v___x_2532_ = v_reuseFailAlloc_2533_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_2515_ == 0 {
                    v___x_2517_ = v___x_2514_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2517_;
            }
            10 => {
                v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2504_);
                v___x_2525_ = lean_array_push(v___x_2524_, v_a_2520_);
                if v_isShared_2523_ == 0 {
                    lean_ctor_set(v___x_2522_, 0, v___x_2525_);
                    v___x_2527_ = v___x_2522_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2527_;
            }
            12 => {
                return v___x_2532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___boxed(
    mut v_ws_2542_: *mut LeanObject,
    mut v_spec_2543_: *mut LeanObject,
    mut v_facet_2544_: *mut LeanObject,
    mut v_isMaybePath_2545_: *mut LeanObject,
    mut v_explicit_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMaybePath_boxed_2547_: u8 = 0;
    let mut v_explicit_boxed_2548_: u8 = 0;
    let mut v_res_2549_: *mut LeanObject = core::ptr::null_mut();
    v_isMaybePath_boxed_2547_ = (lean_unbox(v_isMaybePath_2545_) as u8);
    v_explicit_boxed_2548_ = (lean_unbox(v_explicit_2546_) as u8);
    v_res_2549_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
        v_ws_2542_,
        v_spec_2543_,
        v_facet_2544_,
        v_isMaybePath_boxed_2547_,
        v_explicit_boxed_2548_,
    );
    lean_dec_ref(v_ws_2542_);
    return v_res_2549_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(
    mut v_spec_2550_: *mut LeanObject,
    mut v___x_2551_: *mut LeanObject,
    mut v___x_2552_: *mut LeanObject,
    mut v_inst_2553_: *mut LeanObject,
    mut v_R_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
    mut v_b_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2557_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_2550_, v___x_2551_, v___x_2552_, v_a_2555_, v_b_2556_);
    return v___x_2557_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___boxed(
    mut v_spec_2558_: *mut LeanObject,
    mut v___x_2559_: *mut LeanObject,
    mut v___x_2560_: *mut LeanObject,
    mut v_inst_2561_: *mut LeanObject,
    mut v_R_2562_: *mut LeanObject,
    mut v_a_2563_: *mut LeanObject,
    mut v_b_2564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2565_: *mut LeanObject = core::ptr::null_mut();
    v_res_2565_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1(v_spec_2558_, v___x_2559_, v___x_2560_, v_inst_2561_, v_R_2562_, v_a_2563_, v_b_2564_);
    lean_dec_ref(v___x_2559_);
    return v_res_2565_;
}
pub unsafe fn _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1()
-> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    v___x_2567_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
    v___x_2568_ = lean_string_utf8_byte_size(v___x_2567_);
    return v___x_2568_;
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(
    mut v_ws_2569_: *mut LeanObject,
    mut v_spec_2570_: *mut LeanObject,
    mut v_facet_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2574_: u8 = 0;
    let mut v___y_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_a_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_a_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_a_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_a_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut v___y_2655_: u8 = 0;
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v_a_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_a_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2691_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
                v___x_2692_ = lean_string_utf8_byte_size(v_spec_2570_);
                v___x_2693_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once
                    ),
                    _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1,
                );
                v___x_2694_ = lean_nat_dec_le(v___x_2693_, v___x_2692_);
                if v___x_2694_ == 0 {
                    v___y_2655_ = v___x_2694_;
                    state = 18;
                    continue;
                } else {
                    v___x_2695_ = lean_unsigned_to_nat(0);
                    v___x_2696_ = lean_string_memcmp(
                        v_spec_2570_,
                        v___x_2691_,
                        v___x_2695_,
                        v___x_2695_,
                        v___x_2693_,
                    );
                    if v___x_2696_ == 0 {
                        v___y_2655_ = v___x_2696_;
                        state = 18;
                        continue;
                    } else {
                        v___x_2697_ = lean_unsigned_to_nat(1);
                        lean_inc_ref(v_spec_2570_);
                        v___x_2698_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_2698_, 0, v_spec_2570_);
                        lean_ctor_set(v___x_2698_, 1, v___x_2695_);
                        lean_ctor_set(v___x_2698_, 2, v___x_2692_);
                        v___x_2699_ =
                            l_String_Slice_Pos_nextn(v___x_2698_, v___x_2695_, v___x_2697_);
                        lean_dec_ref_known(v___x_2698_, 3);
                        v___x_2700_ =
                            lean_string_utf8_extract(v_spec_2570_, v___x_2699_, v___x_2692_);
                        lean_dec(v___x_2699_);
                        lean_dec_ref(v_spec_2570_);
                        v___x_2701_ = 0;
                        v___x_2702_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
                            v_ws_2569_,
                            v___x_2700_,
                            v_facet_2571_,
                            v___x_2701_,
                            v___x_2696_,
                        );
                        if lean_obj_tag(v___x_2702_) == 0 {
                            v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
                            v_isSharedCheck_2710_ = (!lean_is_exclusive(v___x_2702_)) as u8;
                            if v_isSharedCheck_2710_ == 0 {
                                v___x_2705_ = v___x_2702_;
                                v_isShared_2706_ = v_isSharedCheck_2710_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_2703_);
                                lean_dec(v___x_2702_);
                                v___x_2705_ = lean_box(0);
                                v_isShared_2706_ = v_isSharedCheck_2710_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_a_2711_ = lean_ctor_get(v___x_2702_, 0);
                            v_isSharedCheck_2718_ = (!lean_is_exclusive(v___x_2702_)) as u8;
                            if v_isSharedCheck_2718_ == 0 {
                                v___x_2713_ = v___x_2702_;
                                v_isShared_2714_ = v_isSharedCheck_2718_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_2711_);
                                lean_dec(v___x_2702_);
                                v___x_2713_ = lean_box(0);
                                v_isShared_2714_ = v_isSharedCheck_2718_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v_spec_2570_);
                v___x_2576_ = l_Lake_resolvePath(v_spec_2570_);
                v___x_2577_ = lean_string_utf8_byte_size(v___x_2576_);
                v___x_2578_ = lean_unsigned_to_nat(0);
                v___x_2579_ = lean_nat_dec_eq(v___x_2577_, v___x_2578_);
                if v___x_2579_ == 0 {
                    v___x_2580_ = l_System_FilePath_isDir(v___x_2576_);
                    if v___x_2580_ == 0 {
                        v___x_2581_ = l_Lake_Workspace_findModuleBySrc_x3f(v___x_2576_, v_ws_2569_);
                        if lean_obj_tag(v___x_2581_) == 1 {
                            lean_dec_ref(v_spec_2570_);
                            v_val_2582_ = lean_ctor_get(v___x_2581_, 0);
                            lean_inc(v_val_2582_);
                            lean_dec_ref_known(v___x_2581_, 1);
                            v___x_2583_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
                                v_ws_2569_,
                                v_val_2582_,
                                v_facet_2571_,
                            );
                            if lean_obj_tag(v___x_2583_) == 0 {
                                v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
                                v_isSharedCheck_2591_ = (!lean_is_exclusive(v___x_2583_)) as u8;
                                if v_isSharedCheck_2591_ == 0 {
                                    v___x_2586_ = v___x_2583_;
                                    v_isShared_2587_ = v_isSharedCheck_2591_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_2584_);
                                    lean_dec(v___x_2583_);
                                    v___x_2586_ = lean_box(0);
                                    v_isShared_2587_ = v_isSharedCheck_2591_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2592_ = lean_ctor_get(v___x_2583_, 0);
                                v_isSharedCheck_2602_ = (!lean_is_exclusive(v___x_2583_)) as u8;
                                if v_isSharedCheck_2602_ == 0 {
                                    v___x_2594_ = v___x_2583_;
                                    v_isShared_2595_ = v_isSharedCheck_2602_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2592_);
                                    lean_dec(v___x_2583_);
                                    v___x_2594_ = lean_box(0);
                                    v_isShared_2595_ = v_isSharedCheck_2602_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2581_);
                            v___x_2603_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
                                v_ws_2569_,
                                v_spec_2570_,
                                v_facet_2571_,
                                v___y_2574_,
                                v___x_2580_,
                            );
                            if lean_obj_tag(v___x_2603_) == 0 {
                                v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
                                v_isSharedCheck_2611_ = (!lean_is_exclusive(v___x_2603_)) as u8;
                                if v_isSharedCheck_2611_ == 0 {
                                    v___x_2606_ = v___x_2603_;
                                    v_isShared_2607_ = v_isSharedCheck_2611_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2604_);
                                    lean_dec(v___x_2603_);
                                    v___x_2606_ = lean_box(0);
                                    v_isShared_2607_ = v_isSharedCheck_2611_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v_a_2612_ = lean_ctor_get(v___x_2603_, 0);
                                v_isSharedCheck_2619_ = (!lean_is_exclusive(v___x_2603_)) as u8;
                                if v_isSharedCheck_2619_ == 0 {
                                    v___x_2614_ = v___x_2603_;
                                    v_isShared_2615_ = v_isSharedCheck_2619_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_2612_);
                                    lean_dec(v___x_2603_);
                                    v___x_2614_ = lean_box(0);
                                    v_isShared_2615_ = v_isSharedCheck_2619_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2576_);
                        v___x_2620_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
                            v_ws_2569_,
                            v_spec_2570_,
                            v_facet_2571_,
                            v___y_2575_,
                            v___y_2575_,
                        );
                        if lean_obj_tag(v___x_2620_) == 0 {
                            v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
                            v_isSharedCheck_2628_ = (!lean_is_exclusive(v___x_2620_)) as u8;
                            if v_isSharedCheck_2628_ == 0 {
                                v___x_2623_ = v___x_2620_;
                                v_isShared_2624_ = v_isSharedCheck_2628_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2621_);
                                lean_dec(v___x_2620_);
                                v___x_2623_ = lean_box(0);
                                v_isShared_2624_ = v_isSharedCheck_2628_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v_a_2629_ = lean_ctor_get(v___x_2620_, 0);
                            v_isSharedCheck_2636_ = (!lean_is_exclusive(v___x_2620_)) as u8;
                            if v_isSharedCheck_2636_ == 0 {
                                v___x_2631_ = v___x_2620_;
                                v_isShared_2632_ = v_isSharedCheck_2636_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2629_);
                                lean_dec(v___x_2620_);
                                v___x_2631_ = lean_box(0);
                                v_isShared_2632_ = v_isSharedCheck_2636_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2576_);
                    v___x_2637_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec(
                        v_ws_2569_,
                        v_spec_2570_,
                        v_facet_2571_,
                        v___y_2574_,
                        v___y_2575_,
                    );
                    if lean_obj_tag(v___x_2637_) == 0 {
                        v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2645_ == 0 {
                            v___x_2640_ = v___x_2637_;
                            v_isShared_2641_ = v_isSharedCheck_2645_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2638_);
                            lean_dec(v___x_2637_);
                            v___x_2640_ = lean_box(0);
                            v_isShared_2641_ = v_isSharedCheck_2645_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v_a_2646_ = lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2653_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2653_ == 0 {
                            v___x_2648_ = v___x_2637_;
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2646_);
                            lean_dec(v___x_2637_);
                            v___x_2648_ = lean_box(0);
                            v_isShared_2649_ = v_isSharedCheck_2653_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2587_ == 0 {
                    lean_ctor_set_tag(v___x_2586_, 1);
                    v___x_2589_ = v___x_2586_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2589_;
            }
            4 => {
                v___x_2596_ = lean_unsigned_to_nat(1);
                v___x_2597_ = lean_mk_empty_array_with_capacity(v___x_2596_);
                v___x_2598_ = lean_array_push(v___x_2597_, v_a_2592_);
                if v_isShared_2595_ == 0 {
                    lean_ctor_set_tag(v___x_2594_, 0);
                    lean_ctor_set(v___x_2594_, 0, v___x_2598_);
                    v___x_2600_ = v___x_2594_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
                    v___x_2600_ = v_reuseFailAlloc_2601_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2600_;
            }
            6 => {
                if v_isShared_2607_ == 0 {
                    lean_ctor_set_tag(v___x_2606_, 1);
                    v___x_2609_ = v___x_2606_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
                    v___x_2609_ = v_reuseFailAlloc_2610_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2609_;
            }
            8 => {
                if v_isShared_2615_ == 0 {
                    lean_ctor_set_tag(v___x_2614_, 0);
                    v___x_2617_ = v___x_2614_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
                    v___x_2617_ = v_reuseFailAlloc_2618_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2617_;
            }
            10 => {
                if v_isShared_2624_ == 0 {
                    lean_ctor_set_tag(v___x_2623_, 1);
                    v___x_2626_ = v___x_2623_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
                    v___x_2626_ = v_reuseFailAlloc_2627_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2626_;
            }
            12 => {
                if v_isShared_2632_ == 0 {
                    lean_ctor_set_tag(v___x_2631_, 0);
                    v___x_2634_ = v___x_2631_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
                    v___x_2634_ = v_reuseFailAlloc_2635_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2634_;
            }
            14 => {
                if v_isShared_2641_ == 0 {
                    lean_ctor_set_tag(v___x_2640_, 1);
                    v___x_2643_ = v___x_2640_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
                    v___x_2643_ = v_reuseFailAlloc_2644_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2643_;
            }
            16 => {
                if v_isShared_2649_ == 0 {
                    lean_ctor_set_tag(v___x_2648_, 0);
                    v___x_2651_ = v___x_2648_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
                    v___x_2651_ = v_reuseFailAlloc_2652_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2651_;
            }
            18 => {
                v___x_2656_ = 1;
                v___x_2657_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__1;
                v___x_2658_ = lean_string_utf8_byte_size(v_spec_2570_);
                v___x_2659_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2_once
                    ),
                    _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__2,
                );
                v___x_2660_ = lean_nat_dec_le(v___x_2659_, v___x_2658_);
                if v___x_2660_ == 0 {
                    v___y_2574_ = v___x_2656_;
                    v___y_2575_ = v___y_2655_;
                    state = 1;
                    continue;
                } else {
                    v___x_2661_ = lean_unsigned_to_nat(0);
                    v___x_2662_ = lean_string_memcmp(
                        v_spec_2570_,
                        v___x_2657_,
                        v___x_2661_,
                        v___x_2661_,
                        v___x_2659_,
                    );
                    if v___x_2662_ == 0 {
                        v___y_2574_ = v___x_2656_;
                        v___y_2575_ = v___x_2662_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2663_ = lean_unsigned_to_nat(1);
                        lean_inc_ref(v_spec_2570_);
                        v___x_2664_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_2664_, 0, v_spec_2570_);
                        lean_ctor_set(v___x_2664_, 1, v___x_2661_);
                        lean_ctor_set(v___x_2664_, 2, v___x_2658_);
                        v___x_2665_ =
                            l_String_Slice_Pos_nextn(v___x_2664_, v___x_2661_, v___x_2663_);
                        lean_dec_ref_known(v___x_2664_, 3);
                        v___x_2666_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_2666_, 0, v_spec_2570_);
                        lean_ctor_set(v___x_2666_, 1, v___x_2665_);
                        lean_ctor_set(v___x_2666_, 2, v___x_2658_);
                        v_mod_2667_ = l_String_Slice_toName(v___x_2666_);
                        lean_dec_ref_known(v___x_2666_, 3);
                        lean_inc(v_mod_2667_);
                        v___x_2668_ =
                            l_Lake_Workspace_findTargetModule_x3f(v_mod_2667_, v_ws_2569_);
                        if lean_obj_tag(v___x_2668_) == 1 {
                            lean_dec(v_mod_2667_);
                            v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
                            lean_inc(v_val_2669_);
                            lean_dec_ref_known(v___x_2668_, 1);
                            v___x_2670_ = l___private_Lake_CLI_Build_0__Lake_resolveModuleTarget(
                                v_ws_2569_,
                                v_val_2669_,
                                v_facet_2571_,
                            );
                            if lean_obj_tag(v___x_2670_) == 0 {
                                v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
                                v_isSharedCheck_2678_ = (!lean_is_exclusive(v___x_2670_)) as u8;
                                if v_isSharedCheck_2678_ == 0 {
                                    v___x_2673_ = v___x_2670_;
                                    v_isShared_2674_ = v_isSharedCheck_2678_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_2671_);
                                    lean_dec(v___x_2670_);
                                    v___x_2673_ = lean_box(0);
                                    v_isShared_2674_ = v_isSharedCheck_2678_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                v_a_2679_ = lean_ctor_get(v___x_2670_, 0);
                                v_isSharedCheck_2688_ = (!lean_is_exclusive(v___x_2670_)) as u8;
                                if v_isSharedCheck_2688_ == 0 {
                                    v___x_2681_ = v___x_2670_;
                                    v_isShared_2682_ = v_isSharedCheck_2688_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_a_2679_);
                                    lean_dec(v___x_2670_);
                                    v___x_2681_ = lean_box(0);
                                    v_isShared_2682_ = v_isSharedCheck_2688_;
                                    state = 21;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2668_);
                            lean_dec(v_facet_2571_);
                            v___x_2689_ = lean_alloc_ctor(11, 1, (0) as u32);
                            lean_ctor_set(v___x_2689_, 0, v_mod_2667_);
                            v___x_2690_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2690_, 0, v___x_2689_);
                            return v___x_2690_;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_2674_ == 0 {
                    lean_ctor_set_tag(v___x_2673_, 1);
                    v___x_2676_ = v___x_2673_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2676_;
            }
            21 => {
                v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2663_);
                v___x_2684_ = lean_array_push(v___x_2683_, v_a_2679_);
                if v_isShared_2682_ == 0 {
                    lean_ctor_set_tag(v___x_2681_, 0);
                    lean_ctor_set(v___x_2681_, 0, v___x_2684_);
                    v___x_2686_ = v___x_2681_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
                    v___x_2686_ = v_reuseFailAlloc_2687_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2686_;
            }
            23 => {
                if v_isShared_2706_ == 0 {
                    lean_ctor_set_tag(v___x_2705_, 1);
                    v___x_2708_ = v___x_2705_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
                    v___x_2708_ = v_reuseFailAlloc_2709_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2708_;
            }
            25 => {
                if v_isShared_2714_ == 0 {
                    lean_ctor_set_tag(v___x_2713_, 0);
                    v___x_2716_ = v___x_2713_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
                    v___x_2716_ = v_reuseFailAlloc_2717_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___boxed(
    mut v_ws_2719_: *mut LeanObject,
    mut v_spec_2720_: *mut LeanObject,
    mut v_facet_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2723_: *mut LeanObject = core::ptr::null_mut();
    v_res_2723_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(
        v_ws_2719_,
        v_spec_2720_,
        v_facet_2721_,
    );
    lean_dec_ref(v_ws_2719_);
    return v_res_2723_;
}
pub unsafe fn l_Lake_parseExeTargetSpec(
    mut v_ws_2724_: *mut LeanObject,
    mut v_spec_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: u32 = 0;
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetName_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_head_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v_str_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut v_isSharedCheck_2801_: u8 = 0;
    let mut v_str_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2733_ = lean_unsigned_to_nat(0);
                v___x_2734_ = lean_string_utf8_byte_size(v_spec_2725_);
                lean_inc_ref_n(v_spec_2725_, 2);
                v___x_2735_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2735_, 0, v_spec_2725_);
                lean_ctor_set(v___x_2735_, 1, v___x_2733_);
                lean_ctor_set(v___x_2735_, 2, v___x_2734_);
                v___x_2736_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0(v___x_2735_);
                v___x_2737_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec___closed__0;
                v___x_2738_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__1___redArg(v_spec_2725_, v___x_2735_, v___x_2734_, v___x_2736_, v___x_2737_);
                lean_dec_ref_known(v___x_2735_, 3);
                v___x_2739_ = lean_array_to_list(v___x_2738_);
                if lean_obj_tag(v___x_2739_) == 1 {
                    v_tail_2740_ = lean_ctor_get(v___x_2739_, 1);
                    lean_inc(v_tail_2740_);
                    if lean_obj_tag(v_tail_2740_) == 0 {
                        v_head_2741_ = lean_ctor_get(v___x_2739_, 0);
                        lean_inc(v_head_2741_);
                        lean_dec_ref_known(v___x_2739_, 2);
                        v_str_2742_ = lean_ctor_get(v_head_2741_, 0);
                        lean_inc_ref(v_str_2742_);
                        v_startInclusive_2743_ = lean_ctor_get(v_head_2741_, 1);
                        lean_inc(v_startInclusive_2743_);
                        v_endExclusive_2744_ = lean_ctor_get(v_head_2741_, 2);
                        lean_inc(v_endExclusive_2744_);
                        lean_dec(v_head_2741_);
                        v___x_2745_ = lean_string_utf8_extract(
                            v_str_2742_,
                            v_startInclusive_2743_,
                            v_endExclusive_2744_,
                        );
                        lean_dec(v_endExclusive_2744_);
                        lean_dec(v_startInclusive_2743_);
                        lean_dec_ref(v_str_2742_);
                        v_targetName_2746_ = l_Lake_stringToLegalOrSimpleName(v___x_2745_);
                        v___x_2747_ =
                            l_Lake_Workspace_findLeanExe_x3f(v_targetName_2746_, v_ws_2724_);
                        lean_dec(v_targetName_2746_);
                        if lean_obj_tag(v___x_2747_) == 0 {
                            v___x_2748_ = lean_alloc_ctor(21, 1, (0) as u32);
                            lean_ctor_set(v___x_2748_, 0, v_spec_2725_);
                            v___x_2749_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2749_, 0, v___x_2748_);
                            return v___x_2749_;
                        } else {
                            lean_dec_ref(v_spec_2725_);
                            v_val_2750_ = lean_ctor_get(v___x_2747_, 0);
                            v_isSharedCheck_2757_ = (!lean_is_exclusive(v___x_2747_)) as u8;
                            if v_isSharedCheck_2757_ == 0 {
                                v___x_2752_ = v___x_2747_;
                                v_isShared_2753_ = v_isSharedCheck_2757_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_val_2750_);
                                lean_dec(v___x_2747_);
                                v___x_2752_ = lean_box(0);
                                v_isShared_2753_ = v_isSharedCheck_2757_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_head_2758_ = lean_ctor_get(v___x_2739_, 0);
                        lean_inc(v_head_2758_);
                        lean_dec_ref_known(v___x_2739_, 2);
                        v_head_2759_ = lean_ctor_get(v_tail_2740_, 0);
                        lean_inc(v_head_2759_);
                        v_tail_2760_ = lean_ctor_get(v_tail_2740_, 1);
                        lean_inc(v_tail_2760_);
                        lean_dec_ref_known(v_tail_2740_, 2);
                        if lean_obj_tag(v_tail_2760_) == 0 {
                            v_str_2802_ = lean_ctor_get(v_head_2758_, 0);
                            lean_inc_ref(v_str_2802_);
                            v_startInclusive_2803_ = lean_ctor_get(v_head_2758_, 1);
                            lean_inc(v_startInclusive_2803_);
                            v_endExclusive_2804_ = lean_ctor_get(v_head_2758_, 2);
                            lean_inc(v_endExclusive_2804_);
                            v___x_2805_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__0;
                            v___x_2806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1), core::ptr::addr_of_mut!(l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1_once), _init_l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec___closed__1);
                            v___x_2807_ =
                                lean_nat_sub(v_endExclusive_2804_, v_startInclusive_2803_);
                            v___x_2808_ = lean_nat_dec_le(v___x_2806_, v___x_2807_);
                            lean_dec(v___x_2807_);
                            if v___x_2808_ == 0 {
                                lean_dec(v_head_2758_);
                                v_str_2762_ = v_str_2802_;
                                v_startInclusive_2763_ = v_startInclusive_2803_;
                                v_endExclusive_2764_ = v_endExclusive_2804_;
                                state = 5;
                                continue;
                            } else {
                                v___x_2809_ = lean_string_memcmp(
                                    v_str_2802_,
                                    v___x_2805_,
                                    v_startInclusive_2803_,
                                    v___x_2733_,
                                    v___x_2806_,
                                );
                                if v___x_2809_ == 0 {
                                    lean_dec(v_head_2758_);
                                    v_str_2762_ = v_str_2802_;
                                    v_startInclusive_2763_ = v_startInclusive_2803_;
                                    v_endExclusive_2764_ = v_endExclusive_2804_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_2810_ = lean_unsigned_to_nat(1);
                                    v___x_2811_ = l_String_Slice_Pos_nextn(
                                        v_head_2758_,
                                        v___x_2733_,
                                        v___x_2810_,
                                    );
                                    lean_dec(v_head_2758_);
                                    v___x_2812_ = lean_nat_add(v_startInclusive_2803_, v___x_2811_);
                                    lean_dec(v___x_2811_);
                                    lean_dec(v_startInclusive_2803_);
                                    v_str_2762_ = v_str_2802_;
                                    v_startInclusive_2763_ = v___x_2812_;
                                    v_endExclusive_2764_ = v_endExclusive_2804_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_tail_2760_);
                            lean_dec(v_head_2759_);
                            lean_dec(v_head_2758_);
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2739_);
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2727_ = lean_alloc_ctor(21, 1, (0) as u32);
                lean_ctor_set(v___x_2727_, 0, v_spec_2725_);
                v___x_2728_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            2 => {
                v___x_2730_ = 47;
                v___x_2731_ = lean_alloc_ctor(19, 1, (4) as u32);
                lean_ctor_set(v___x_2731_, 0, v_spec_2725_);
                lean_ctor_set_uint32(
                    v___x_2731_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2730_,
                );
                v___x_2732_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                return v___x_2732_;
            }
            3 => {
                if v_isShared_2753_ == 0 {
                    v___x_2755_ = v___x_2752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2750_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2755_;
            }
            5 => {
                v___x_2765_ = lean_string_utf8_extract(
                    v_str_2762_,
                    v_startInclusive_2763_,
                    v_endExclusive_2764_,
                );
                lean_dec(v_endExclusive_2764_);
                lean_dec(v_startInclusive_2763_);
                lean_dec_ref(v_str_2762_);
                v___x_2766_ = l_Lake_parsePackageSpec(v_ws_2724_, v___x_2765_);
                if lean_obj_tag(v___x_2766_) == 0 {
                    lean_dec(v_head_2759_);
                    lean_dec_ref(v_spec_2725_);
                    v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
                    v_isSharedCheck_2774_ = (!lean_is_exclusive(v___x_2766_)) as u8;
                    if v_isSharedCheck_2774_ == 0 {
                        v___x_2769_ = v___x_2766_;
                        v_isShared_2770_ = v_isSharedCheck_2774_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2767_);
                        lean_dec(v___x_2766_);
                        v___x_2769_ = lean_box(0);
                        v_isShared_2770_ = v_isSharedCheck_2774_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_2775_ = lean_ctor_get(v___x_2766_, 0);
                    v_isSharedCheck_2801_ = (!lean_is_exclusive(v___x_2766_)) as u8;
                    if v_isSharedCheck_2801_ == 0 {
                        v___x_2777_ = v___x_2766_;
                        v_isShared_2778_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2775_);
                        lean_dec(v___x_2766_);
                        v___x_2777_ = lean_box(0);
                        v_isShared_2778_ = v_isSharedCheck_2801_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2770_ == 0 {
                    v___x_2772_ = v___x_2769_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
                    v___x_2772_ = v_reuseFailAlloc_2773_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2772_;
            }
            8 => {
                v_str_2779_ = lean_ctor_get(v_head_2759_, 0);
                v_startInclusive_2780_ = lean_ctor_get(v_head_2759_, 1);
                v_endExclusive_2781_ = lean_ctor_get(v_head_2759_, 2);
                v_isSharedCheck_2800_ = (!lean_is_exclusive(v_head_2759_)) as u8;
                if v_isSharedCheck_2800_ == 0 {
                    v___x_2783_ = v_head_2759_;
                    v_isShared_2784_ = v_isSharedCheck_2800_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_endExclusive_2781_);
                    lean_inc(v_startInclusive_2780_);
                    lean_inc(v_str_2779_);
                    lean_dec(v_head_2759_);
                    v___x_2783_ = lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_2800_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2785_ = lean_string_utf8_extract(
                    v_str_2779_,
                    v_startInclusive_2780_,
                    v_endExclusive_2781_,
                );
                lean_dec(v_endExclusive_2781_);
                lean_dec(v_startInclusive_2780_);
                lean_dec_ref(v_str_2779_);
                v___x_2786_ = l_Lake_stringToLegalOrSimpleName(v___x_2785_);
                v___x_2787_ = l_Lake_Package_findTargetDecl_x3f(v___x_2786_, v_a_2775_);
                lean_dec(v___x_2786_);
                if lean_obj_tag(v___x_2787_) == 0 {
                    lean_del_object(v___x_2783_);
                    lean_del_object(v___x_2777_);
                    lean_dec(v_a_2775_);
                    state = 1;
                    continue;
                } else {
                    v_val_2788_ = lean_ctor_get(v___x_2787_, 0);
                    lean_inc(v_val_2788_);
                    lean_dec_ref_known(v___x_2787_, 1);
                    v_name_2789_ = lean_ctor_get(v_val_2788_, 1);
                    lean_inc(v_name_2789_);
                    v_kind_2790_ = lean_ctor_get(v_val_2788_, 2);
                    lean_inc(v_kind_2790_);
                    v_config_2791_ = lean_ctor_get(v_val_2788_, 3);
                    lean_inc(v_config_2791_);
                    lean_dec(v_val_2788_);
                    v___x_2792_ = l_Lake_LeanExe_keyword;
                    v___x_2793_ = lean_name_eq(v_kind_2790_, v___x_2792_);
                    lean_dec(v_kind_2790_);
                    if v___x_2793_ == 0 {
                        lean_dec(v_config_2791_);
                        lean_dec(v_name_2789_);
                        lean_del_object(v___x_2783_);
                        lean_del_object(v___x_2777_);
                        lean_dec(v_a_2775_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_spec_2725_);
                        if v_isShared_2784_ == 0 {
                            lean_ctor_set(v___x_2783_, 2, v_config_2791_);
                            lean_ctor_set(v___x_2783_, 1, v_name_2789_);
                            lean_ctor_set(v___x_2783_, 0, v_a_2775_);
                            v___x_2795_ = v___x_2783_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2775_);
                            lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_name_2789_);
                            lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_config_2791_);
                            v___x_2795_ = v_reuseFailAlloc_2799_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_2778_ == 0 {
                    lean_ctor_set(v___x_2777_, 0, v___x_2795_);
                    v___x_2797_ = v___x_2777_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
                    v___x_2797_ = v_reuseFailAlloc_2798_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_parseExeTargetSpec___boxed(
    mut v_ws_2813_: *mut LeanObject,
    mut v_spec_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2815_: *mut LeanObject = core::ptr::null_mut();
    v_res_2815_ = l_Lake_parseExeTargetSpec(v_ws_2813_, v_spec_2814_);
    lean_dec_ref(v_ws_2813_);
    return v_res_2815_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(
    mut v_s_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Build_0__Lake_resolveTargetLikeSpec_spec__0___closed__0;
    return v___x_2817_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0___boxed(
    mut v_s_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2819_: *mut LeanObject = core::ptr::null_mut();
    v_res_2819_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(v_s_2818_);
    lean_dec_ref(v_s_2818_);
    return v_res_2819_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(
    mut v_spec_2820_: *mut LeanObject,
    mut v___x_2821_: *mut LeanObject,
    mut v___x_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
    mut v_b_2824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v_startInclusive_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u32 = 0;
    let mut v___x_2843_: u32 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2823_) == 0 {
                    v_currPos_2833_ = lean_ctor_get(v_a_2823_, 0);
                    v_searcher_2834_ = lean_ctor_get(v_a_2823_, 1);
                    v_isSharedCheck_2860_ = (!lean_is_exclusive(v_a_2823_)) as u8;
                    if v_isSharedCheck_2860_ == 0 {
                        v___x_2836_ = v_a_2823_;
                        v_isShared_2837_ = v_isSharedCheck_2860_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_2834_);
                        lean_inc(v_currPos_2833_);
                        lean_dec(v_a_2823_);
                        v___x_2836_ = lean_box(0);
                        v_isShared_2837_ = v_isSharedCheck_2860_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2822_);
                    lean_dec_ref(v_spec_2820_);
                    return v_b_2824_;
                }
            }
            1 => {
                lean_inc_ref(v_spec_2820_);
                v___x_2829_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2829_, 0, v_spec_2820_);
                lean_ctor_set(v___x_2829_, 1, v_startInclusive_2827_);
                lean_ctor_set(v___x_2829_, 2, v_endExclusive_2828_);
                v___x_2830_ = l_String_Slice_toString(v___x_2829_);
                lean_dec_ref_known(v___x_2829_, 3);
                v___x_2831_ = lean_array_push(v_b_2824_, v___x_2830_);
                v_a_2823_ = v_it_2826_;
                v_b_2824_ = v___x_2831_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2838_ = lean_ctor_get(v___x_2821_, 1);
                v_endExclusive_2839_ = lean_ctor_get(v___x_2821_, 2);
                v___x_2840_ = lean_nat_sub(v_endExclusive_2839_, v_startInclusive_2838_);
                v___x_2841_ = lean_nat_dec_eq(v_searcher_2834_, v___x_2840_);
                lean_dec(v___x_2840_);
                if v___x_2841_ == 0 {
                    v___x_2842_ = 58;
                    v___x_2843_ = lean_string_utf8_get_fast(v_spec_2820_, v_searcher_2834_);
                    v___x_2844_ = lean_uint32_dec_eq(v___x_2843_, v___x_2842_);
                    if v___x_2844_ == 0 {
                        v___x_2845_ = lean_string_utf8_next_fast(v_spec_2820_, v_searcher_2834_);
                        lean_dec(v_searcher_2834_);
                        if v_isShared_2837_ == 0 {
                            lean_ctor_set(v___x_2836_, 1, v___x_2845_);
                            v___x_2847_ = v___x_2836_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_currPos_2833_);
                            lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2845_);
                            v___x_2847_ = v_reuseFailAlloc_2849_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2850_ = lean_string_utf8_next_fast(v_spec_2820_, v_searcher_2834_);
                        v___x_2851_ = lean_nat_sub(v___x_2850_, v_searcher_2834_);
                        v___x_2852_ = lean_nat_add(v_searcher_2834_, v___x_2851_);
                        lean_dec(v___x_2851_);
                        v_slice_2853_ = l_String_Slice_subslice_x21(
                            v___x_2821_,
                            v_currPos_2833_,
                            v_searcher_2834_,
                        );
                        lean_inc(v___x_2852_);
                        if v_isShared_2837_ == 0 {
                            lean_ctor_set(v___x_2836_, 1, v___x_2852_);
                            lean_ctor_set(v___x_2836_, 0, v___x_2852_);
                            v_nextIt_2855_ = v___x_2836_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2852_);
                            lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2852_);
                            v_nextIt_2855_ = v_reuseFailAlloc_2858_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2836_);
                    lean_dec(v_searcher_2834_);
                    v___x_2859_ = lean_box(1);
                    lean_inc(v___x_2822_);
                    v_it_2826_ = v___x_2859_;
                    v_startInclusive_2827_ = v_currPos_2833_;
                    v_endExclusive_2828_ = v___x_2822_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_2823_ = v___x_2847_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_2856_ = lean_ctor_get(v_slice_2853_, 0);
                lean_inc(v_startInclusive_2856_);
                v_endExclusive_2857_ = lean_ctor_get(v_slice_2853_, 1);
                lean_inc(v_endExclusive_2857_);
                lean_dec_ref(v_slice_2853_);
                v_it_2826_ = v_nextIt_2855_;
                v_startInclusive_2827_ = v_startInclusive_2856_;
                v_endExclusive_2828_ = v_endExclusive_2857_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg___boxed(
    mut v_spec_2861_: *mut LeanObject,
    mut v___x_2862_: *mut LeanObject,
    mut v___x_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_b_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2866_: *mut LeanObject = core::ptr::null_mut();
    v_res_2866_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_2861_, v___x_2862_, v___x_2863_, v_a_2864_, v_b_2865_);
    lean_dec_ref(v___x_2862_);
    return v_res_2866_;
}
pub unsafe fn l_Lake_parseTargetSpec(
    mut v_ws_2869_: *mut LeanObject,
    mut v_spec_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2872_: u32 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2872_ = 58;
                v___x_2876_ = lean_unsigned_to_nat(0);
                v___x_2877_ = lean_string_utf8_byte_size(v_spec_2870_);
                lean_inc_ref_n(v_spec_2870_, 2);
                v___x_2878_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2878_, 0, v_spec_2870_);
                lean_ctor_set(v___x_2878_, 1, v___x_2876_);
                lean_ctor_set(v___x_2878_, 2, v___x_2877_);
                v___x_2879_ = l_String_Slice_splitToSubslice___at___00Lake_parseTargetSpec_spec__0(
                    v___x_2878_,
                );
                v___x_2880_ = l_Lake_parseTargetSpec___closed__0;
                v___x_2881_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_2870_, v___x_2878_, v___x_2877_, v___x_2879_, v___x_2880_);
                lean_dec_ref_known(v___x_2878_, 3);
                v___x_2882_ = lean_array_to_list(v___x_2881_);
                if lean_obj_tag(v___x_2882_) == 1 {
                    v_tail_2883_ = lean_ctor_get(v___x_2882_, 1);
                    lean_inc(v_tail_2883_);
                    if lean_obj_tag(v_tail_2883_) == 0 {
                        lean_dec_ref(v_spec_2870_);
                        v_head_2884_ = lean_ctor_get(v___x_2882_, 0);
                        lean_inc(v_head_2884_);
                        lean_dec_ref_known(v___x_2882_, 2);
                        v___x_2885_ = lean_box(0);
                        v___x_2886_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(
                            v_ws_2869_,
                            v_head_2884_,
                            v___x_2885_,
                        );
                        return v___x_2886_;
                    } else {
                        v_tail_2887_ = lean_ctor_get(v_tail_2883_, 1);
                        if lean_obj_tag(v_tail_2887_) == 0 {
                            lean_dec_ref(v_spec_2870_);
                            v_head_2888_ = lean_ctor_get(v___x_2882_, 0);
                            lean_inc(v_head_2888_);
                            lean_dec_ref_known(v___x_2882_, 2);
                            v_head_2889_ = lean_ctor_get(v_tail_2883_, 0);
                            lean_inc(v_head_2889_);
                            lean_dec_ref_known(v_tail_2883_, 2);
                            v___x_2890_ = l_String_toName(v_head_2889_);
                            v___x_2891_ = l___private_Lake_CLI_Build_0__Lake_resolveTargetBaseSpec(
                                v_ws_2869_,
                                v_head_2888_,
                                v___x_2890_,
                            );
                            return v___x_2891_;
                        } else {
                            lean_dec_ref_known(v_tail_2883_, 2);
                            lean_dec_ref_known(v___x_2882_, 2);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2882_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2874_ = lean_alloc_ctor(19, 1, (4) as u32);
                lean_ctor_set(v___x_2874_, 0, v_spec_2870_);
                lean_ctor_set_uint32(
                    v___x_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2872_,
                );
                v___x_2875_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2875_, 0, v___x_2874_);
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_parseTargetSpec___boxed(
    mut v_ws_2892_: *mut LeanObject,
    mut v_spec_2893_: *mut LeanObject,
    mut v_a_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Lake_parseTargetSpec(v_ws_2892_, v_spec_2893_);
    lean_dec_ref(v_ws_2892_);
    return v_res_2895_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(
    mut v_spec_2896_: *mut LeanObject,
    mut v___x_2897_: *mut LeanObject,
    mut v___x_2898_: *mut LeanObject,
    mut v_inst_2899_: *mut LeanObject,
    mut v_R_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
    mut v_b_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    v___x_2903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___redArg(v_spec_2896_, v___x_2897_, v___x_2898_, v_a_2901_, v_b_2902_);
    return v___x_2903_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1___boxed(
    mut v_spec_2904_: *mut LeanObject,
    mut v___x_2905_: *mut LeanObject,
    mut v___x_2906_: *mut LeanObject,
    mut v_inst_2907_: *mut LeanObject,
    mut v_R_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
    mut v_b_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2911_: *mut LeanObject = core::ptr::null_mut();
    v_res_2911_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_parseTargetSpec_spec__1(v_spec_2904_, v___x_2905_, v___x_2906_, v_inst_2907_, v_R_2908_, v_a_2909_, v_b_2910_);
    lean_dec_ref(v___x_2905_);
    return v_res_2911_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(
    mut v_ws_2912_: *mut LeanObject,
    mut v_as_x27_2913_: *mut LeanObject,
    mut v_b_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2913_) == 0 {
                    v___x_2916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2916_, 0, v_b_2914_);
                    return v___x_2916_;
                } else {
                    v_head_2917_ = lean_ctor_get(v_as_x27_2913_, 0);
                    v_tail_2918_ = lean_ctor_get(v_as_x27_2913_, 1);
                    lean_inc(v_head_2917_);
                    v___x_2919_ = l_Lake_parseTargetSpec(v_ws_2912_, v_head_2917_);
                    if lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
                        lean_inc(v_a_2920_);
                        lean_dec_ref_known(v___x_2919_, 1);
                        v___x_2921_ = l_Array_append___redArg(v_b_2914_, v_a_2920_);
                        lean_dec(v_a_2920_);
                        v_as_x27_2913_ = v_tail_2918_;
                        v_b_2914_ = v___x_2921_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_2914_);
                        return v___x_2919_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg___boxed(
    mut v_ws_2923_: *mut LeanObject,
    mut v_as_x27_2924_: *mut LeanObject,
    mut v_b_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2927_: *mut LeanObject = core::ptr::null_mut();
    v_res_2927_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(
        v_ws_2923_,
        v_as_x27_2924_,
        v_b_2925_,
    );
    lean_dec(v_as_x27_2924_);
    lean_dec_ref(v_ws_2923_);
    return v_res_2927_;
}
pub unsafe fn l_Lake_parseTargetSpecs(
    mut v_ws_2930_: *mut LeanObject,
    mut v_specs_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_results_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2941_: u8 = 0;
    let mut v_packages_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_unused_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2933_ = lean_unsigned_to_nat(0);
                v_results_2934_ = l_Lake_parseTargetSpecs___closed__0;
                v___x_2935_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(
                    v_ws_2930_,
                    v_specs_2931_,
                    v_results_2934_,
                );
                if lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
                    lean_inc(v_a_2936_);
                    v___x_2937_ = lean_array_get_size(v_a_2936_);
                    lean_dec(v_a_2936_);
                    v___x_2938_ = lean_nat_dec_eq(v___x_2937_, v___x_2933_);
                    if v___x_2938_ == 0 {
                        return v___x_2935_;
                    } else {
                        v_isSharedCheck_2953_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                        if v_isSharedCheck_2953_ == 0 {
                            v_unused_2954_ = lean_ctor_get(v___x_2935_, 0);
                            lean_dec(v_unused_2954_);
                            v___x_2940_ = v___x_2935_;
                            v_isShared_2941_ = v_isSharedCheck_2953_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2935_);
                            v___x_2940_ = lean_box(0);
                            v_isShared_2941_ = v_isSharedCheck_2953_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_2935_;
                }
            }
            1 => {
                v_packages_2942_ = lean_ctor_get(v_ws_2930_, 4);
                v___x_2943_ = lean_array_fget_borrowed(v_packages_2942_, v___x_2933_);
                lean_inc(v___x_2943_);
                v___x_2944_ = l___private_Lake_CLI_Build_0__Lake_resolveDefaultPackageTarget(
                    v_ws_2930_,
                    v___x_2943_,
                );
                if lean_obj_tag(v___x_2944_) == 0 {
                    v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
                    lean_inc(v_a_2945_);
                    lean_dec_ref_known(v___x_2944_, 1);
                    if v_isShared_2941_ == 0 {
                        lean_ctor_set_tag(v___x_2940_, 1);
                        lean_ctor_set(v___x_2940_, 0, v_a_2945_);
                        v___x_2947_ = v___x_2940_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2945_);
                        v___x_2947_ = v_reuseFailAlloc_2948_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2949_ = lean_ctor_get(v___x_2944_, 0);
                    lean_inc(v_a_2949_);
                    lean_dec_ref_known(v___x_2944_, 1);
                    if v_isShared_2941_ == 0 {
                        lean_ctor_set(v___x_2940_, 0, v_a_2949_);
                        v___x_2951_ = v___x_2940_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2949_);
                        v___x_2951_ = v_reuseFailAlloc_2952_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2947_;
            }
            3 => {
                return v___x_2951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_parseTargetSpecs___boxed(
    mut v_ws_2955_: *mut LeanObject,
    mut v_specs_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2958_: *mut LeanObject = core::ptr::null_mut();
    v_res_2958_ = l_Lake_parseTargetSpecs(v_ws_2955_, v_specs_2956_);
    lean_dec(v_specs_2956_);
    lean_dec_ref(v_ws_2955_);
    return v_res_2958_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(
    mut v_ws_2959_: *mut LeanObject,
    mut v_as_2960_: *mut LeanObject,
    mut v_as_x27_2961_: *mut LeanObject,
    mut v_b_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___redArg(
        v_ws_2959_,
        v_as_x27_2961_,
        v_b_2962_,
    );
    return v___x_2965_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0___boxed(
    mut v_ws_2966_: *mut LeanObject,
    mut v_as_2967_: *mut LeanObject,
    mut v_as_x27_2968_: *mut LeanObject,
    mut v_b_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2972_: *mut LeanObject = core::ptr::null_mut();
    v_res_2972_ = l_List_forIn_x27_loop___at___00Lake_parseTargetSpecs_spec__0(
        v_ws_2966_,
        v_as_2967_,
        v_as_x27_2968_,
        v_b_2969_,
        v_a_2970_,
    );
    lean_dec(v_as_x27_2968_);
    lean_dec(v_as_2967_);
    lean_dec_ref(v_ws_2966_);
    return v_res_2972_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Build(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Build(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Build(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Build(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Build(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_CLI_Build(builtin);
}

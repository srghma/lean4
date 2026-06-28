// Lean compiler output
// Module: Lake.Build.InputFile
// Imports: Lake.Config.FacetConfig Lake.Build.Job Lake.Build.Common Lake.Build.Infos
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lake::Build::Common::{
    initialize_Lake_Build_Common, l_Lake_inputBinFile___redArg, l_Lake_inputDir,
    l_Lake_inputTextFile___redArg, runtime_initialize_Lake_Build_Common,
};
use crate::r#gen::Lake::Build::Data::l_Lake_instDataKindFilePath;
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_InputDir_defaultFacet, l_Lake_InputFile_defaultFacet,
};
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Register::{
    l_Lake_Job_renew___redArg, l_Lake_ensureJob___redArg,
};
use crate::r#gen::Lake::Build::Job::{
    initialize_Lake_Build_Job, runtime_initialize_Lake_Build_Job,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Kinds::{l_Lake_InputDir_keyword, l_Lake_InputFile_keyword};
use crate::r#gen::Lake::Util::FilePath::{l_Lake_joinRelative, l_Lake_mkRelPathString};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lake_InputFile_defaultFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFile_defaultFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_defaultFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputFile_defaultFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFile_defaultFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_defaultFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_InputFile_defaultFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFile_defaultFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputFile_defaultFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_InputFile_initFacetConfigs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFile_initFacetConfigs___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputFile_initFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [60, 110, 105, 108, 62, 0],
};
static mut l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lake_InputDir_defaultFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDir_defaultFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_defaultFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDir_defaultFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDir_defaultFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_defaultFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_InputDir_defaultFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDir_defaultFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputDir_defaultFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_InputDir_initFacetConfigs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDir_initFacetConfigs___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputDir_initFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(
    mut v_text_582_: u8,
    mut v___x_583_: *mut LeanObject,
    mut v___y_584_: *mut LeanObject,
    mut v___y_585_: *mut LeanObject,
    mut v___y_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_text_582_ == 0 {
                    v___x_594_ = l_Lake_inputBinFile___redArg(
                        v___x_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_,
                    );
                    v___y_592_ = v___x_594_;
                    state = 1;
                    continue;
                } else {
                    v___x_595_ = l_Lake_inputTextFile___redArg(
                        v___x_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_,
                    );
                    v___y_592_ = v___x_595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_593_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_593_, 0, v___y_592_);
                lean_ctor_set(v___x_593_, 1, v___y_589_);
                return v___x_593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed(
    mut v_text_596_: *mut LeanObject,
    mut v___x_597_: *mut LeanObject,
    mut v___y_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
    mut v___y_600_: *mut LeanObject,
    mut v___y_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_text_boxed_605_: u8 = 0;
    let mut v_res_606_: *mut LeanObject = core::ptr::null_mut();
    v_text_boxed_605_ = (lean_unbox(v_text_596_) as u8);
    v_res_606_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0(
        v_text_boxed_605_,
        v___x_597_,
        v___y_598_,
        v___y_599_,
        v___y_600_,
        v___y_601_,
        v___y_602_,
        v___y_603_,
    );
    lean_dec_ref(v___y_602_);
    lean_dec(v___y_601_);
    lean_dec(v___y_600_);
    lean_dec(v___y_599_);
    return v_res_606_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(
    mut v_t_607_: *mut LeanObject,
    mut v_a_608_: *mut LeanObject,
    mut v_a_609_: *mut LeanObject,
    mut v_a_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_620_: u8 = 0;
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_630_: u8 = 0;
    let mut v_task_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v_registeredJobs_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u8 = 0;
    let mut v_job_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_651_: u8 = 0;
    let mut v_unused_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_615_ = lean_ctor_get(v_t_607_, 0);
                lean_inc_ref(v_pkg_615_);
                v_config_616_ = lean_ctor_get(v_t_607_, 2);
                lean_inc(v_config_616_);
                v_name_617_ = lean_ctor_get(v_t_607_, 1);
                lean_inc(v_name_617_);
                lean_dec_ref(v_t_607_);
                v_dir_618_ = lean_ctor_get(v_pkg_615_, 4);
                lean_inc_ref(v_dir_618_);
                lean_dec_ref(v_pkg_615_);
                v_path_619_ = lean_ctor_get(v_config_616_, 0);
                lean_inc_ref(v_path_619_);
                v_text_620_ = lean_ctor_get_uint8(
                    v_config_616_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec(v_config_616_);
                v___x_621_ = l_Lake_instDataKindFilePath;
                v___x_622_ = l_Lake_joinRelative(v_dir_618_, v_path_619_);
                v___x_623_ = lean_box((v_text_620_) as usize);
                v___f_624_ = lean_alloc_closure(
                    l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_624_, 0, v___x_623_);
                lean_closure_set(v___f_624_, 1, v___x_622_);
                v___x_625_ = l_Lake_ensureJob___redArg(
                    v___x_621_, v___f_624_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_,
                    v_a_613_,
                );
                if lean_obj_tag(v___x_625_) == 0 {
                    v_a_626_ = lean_ctor_get(v___x_625_, 0);
                    v_a_627_ = lean_ctor_get(v___x_625_, 1);
                    v_isSharedCheck_653_ = (!lean_is_exclusive(v___x_625_)) as u8;
                    if v_isSharedCheck_653_ == 0 {
                        v___x_629_ = v___x_625_;
                        v_isShared_630_ = v_isSharedCheck_653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_627_);
                        lean_inc(v_a_626_);
                        lean_dec(v___x_625_);
                        v___x_629_ = lean_box(0);
                        v_isShared_630_ = v_isSharedCheck_653_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_617_);
                    return v___x_625_;
                }
            }
            1 => {
                v_task_631_ = lean_ctor_get(v_a_626_, 0);
                v_kind_632_ = lean_ctor_get(v_a_626_, 1);
                v_isSharedCheck_651_ = (!lean_is_exclusive(v_a_626_)) as u8;
                if v_isSharedCheck_651_ == 0 {
                    v_unused_652_ = lean_ctor_get(v_a_626_, 2);
                    lean_dec(v_unused_652_);
                    v___x_634_ = v_a_626_;
                    v_isShared_635_ = v_isSharedCheck_651_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_632_);
                    lean_inc(v_task_631_);
                    lean_dec(v_a_626_);
                    v___x_634_ = lean_box(0);
                    v_isShared_635_ = v_isSharedCheck_651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_636_ = lean_ctor_get(v_a_612_, 3);
                v___x_637_ = lean_st_ref_take(v_registeredJobs_636_);
                v___x_638_ = 1;
                v___x_639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_617_,
                    v___x_638_,
                );
                v___x_640_ = 0;
                if v_isShared_635_ == 0 {
                    lean_ctor_set(v___x_634_, 2, v___x_639_);
                    v_job_642_ = v___x_634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_650_, 0, v_task_631_);
                    lean_ctor_set(v_reuseFailAlloc_650_, 1, v_kind_632_);
                    lean_ctor_set(v_reuseFailAlloc_650_, 2, v___x_639_);
                    v_job_642_ = v_reuseFailAlloc_650_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_642_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_640_,
                );
                lean_inc_ref(v_job_642_);
                v___x_643_ = l_Lake_Job_toOpaque___redArg(v_job_642_);
                v___x_644_ = lean_array_push(v___x_637_, v___x_643_);
                v___x_645_ = lean_st_ref_set(v_registeredJobs_636_, v___x_644_);
                v___x_646_ = l_Lake_Job_renew___redArg(v_job_642_);
                if v_isShared_630_ == 0 {
                    lean_ctor_set(v___x_629_, 0, v___x_646_);
                    v___x_648_ = v___x_629_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
                    lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_627_);
                    v___x_648_ = v_reuseFailAlloc_649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch___boxed(
    mut v_t_654_: *mut LeanObject,
    mut v_a_655_: *mut LeanObject,
    mut v_a_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_662_: *mut LeanObject = core::ptr::null_mut();
    v_res_662_ = l___private_Lake_Build_InputFile_0__Lake_InputFile_recFetch(
        v_t_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_,
    );
    lean_dec_ref(v_a_659_);
    lean_dec(v_a_658_);
    lean_dec(v_a_657_);
    lean_dec(v_a_656_);
    return v_res_662_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(
    mut v_fmt_663_: u8,
    mut v_a_664_: *mut LeanObject,
) -> *mut LeanObject {
    if v_fmt_663_ == 0 {
        return v_a_664_;
    } else {
        let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        v___x_665_ = l_Lake_mkRelPathString(v_a_664_);
        v___x_666_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_666_, 0, v___x_665_);
        v___x_667_ = l_Lean_Json_compress(v___x_666_);
        return v___x_667_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0___boxed(
    mut v_fmt_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_670_: u8 = 0;
    let mut v_res_671_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_670_ = (lean_unbox(v_fmt_668_) as u8);
    v_res_671_ = l_Lake_formatQuery___at___00Lake_InputFile_defaultFacetConfig_spec__0(
        v_fmt_boxed_670_,
        v_a_669_,
    );
    return v_res_671_;
}
pub unsafe fn _init_l_Lake_InputFile_defaultFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v___f_674_ = l_Lake_InputFile_defaultFacetConfig___closed__0;
    v___x_675_ = 1;
    v___x_676_ = l_Lake_instDataKindFilePath;
    v___x_677_ = l_Lake_InputFile_defaultFacetConfig___closed__1;
    v___x_678_ = l_Lake_InputFile_keyword;
    v___x_679_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_679_, 0, v___x_678_);
    lean_ctor_set(v___x_679_, 1, v___x_677_);
    lean_ctor_set(v___x_679_, 2, v___x_676_);
    lean_ctor_set(v___x_679_, 3, v___f_674_);
    lean_ctor_set_uint8(
        v___x_679_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_675_,
    );
    lean_ctor_set_uint8(
        v___x_679_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_675_,
    );
    return v___x_679_;
}
pub unsafe fn _init_l_Lake_InputFile_defaultFacetConfig() -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFile_defaultFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_InputFile_defaultFacetConfig___closed__2_once),
        _init_l_Lake_InputFile_defaultFacetConfig___closed__2,
    );
    return v___x_680_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(
    mut v_k_681_: *mut LeanObject,
    mut v_v_682_: *mut LeanObject,
    mut v_t_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut v_impl_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v_size_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_723_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut v_unused_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_763_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_unused_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut v_unused_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v_unused_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v_k_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_807_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut v_unused_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_822_: u8 = 0;
    let mut v_unused_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v_size_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_863_: u8 = 0;
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v_unused_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_905_: u8 = 0;
    let mut v_unused_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_unused_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v_k_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v_unused_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_944_: u8 = 0;
    let mut v_unused_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut v_unused_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_683_) == 0 {
                    v_size_684_ = lean_ctor_get(v_t_683_, 0);
                    v_k_685_ = lean_ctor_get(v_t_683_, 1);
                    v_v_686_ = lean_ctor_get(v_t_683_, 2);
                    v_l_687_ = lean_ctor_get(v_t_683_, 3);
                    v_r_688_ = lean_ctor_get(v_t_683_, 4);
                    v_isSharedCheck_968_ = (!lean_is_exclusive(v_t_683_)) as u8;
                    if v_isSharedCheck_968_ == 0 {
                        v___x_690_ = v_t_683_;
                        v_isShared_691_ = v_isSharedCheck_968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_688_);
                        lean_inc(v_l_687_);
                        lean_inc(v_v_686_);
                        lean_inc(v_k_685_);
                        lean_inc(v_size_684_);
                        lean_dec(v_t_683_);
                        v___x_690_ = lean_box(0);
                        v_isShared_691_ = v_isSharedCheck_968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_969_ = lean_unsigned_to_nat(1);
                    v___x_970_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_970_, 0, v___x_969_);
                    lean_ctor_set(v___x_970_, 1, v_k_681_);
                    lean_ctor_set(v___x_970_, 2, v_v_682_);
                    lean_ctor_set(v___x_970_, 3, v_t_683_);
                    lean_ctor_set(v___x_970_, 4, v_t_683_);
                    return v___x_970_;
                }
            }
            1 => {
                v___x_692_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_681_, v_k_685_);
                match v___x_692_ {
                    0 => {
                        lean_dec(v_size_684_);
                        v_impl_693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_681_, v_v_682_, v_l_687_);
                        v___x_694_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_688_) == 0 {
                            v_size_695_ = lean_ctor_get(v_r_688_, 0);
                            v_size_696_ = lean_ctor_get(v_impl_693_, 0);
                            lean_inc(v_size_696_);
                            v_k_697_ = lean_ctor_get(v_impl_693_, 1);
                            lean_inc(v_k_697_);
                            v_v_698_ = lean_ctor_get(v_impl_693_, 2);
                            lean_inc(v_v_698_);
                            v_l_699_ = lean_ctor_get(v_impl_693_, 3);
                            lean_inc(v_l_699_);
                            v_r_700_ = lean_ctor_get(v_impl_693_, 4);
                            lean_inc(v_r_700_);
                            v___x_701_ = lean_unsigned_to_nat(3);
                            v___x_702_ = lean_nat_mul(v___x_701_, v_size_695_);
                            v___x_703_ = lean_nat_dec_lt(v___x_702_, v_size_696_);
                            lean_dec(v___x_702_);
                            if v___x_703_ == 0 {
                                lean_dec(v_r_700_);
                                lean_dec(v_l_699_);
                                lean_dec(v_v_698_);
                                lean_dec(v_k_697_);
                                v___x_704_ = lean_nat_add(v___x_694_, v_size_696_);
                                lean_dec(v_size_696_);
                                v___x_705_ = lean_nat_add(v___x_704_, v_size_695_);
                                lean_dec(v___x_704_);
                                if v_isShared_691_ == 0 {
                                    lean_ctor_set(v___x_690_, 3, v_impl_693_);
                                    lean_ctor_set(v___x_690_, 0, v___x_705_);
                                    v___x_707_ = v___x_690_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
                                    lean_ctor_set(v_reuseFailAlloc_708_, 1, v_k_685_);
                                    lean_ctor_set(v_reuseFailAlloc_708_, 2, v_v_686_);
                                    lean_ctor_set(v_reuseFailAlloc_708_, 3, v_impl_693_);
                                    lean_ctor_set(v_reuseFailAlloc_708_, 4, v_r_688_);
                                    v___x_707_ = v_reuseFailAlloc_708_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_774_ = (!lean_is_exclusive(v_impl_693_)) as u8;
                                if v_isSharedCheck_774_ == 0 {
                                    v_unused_775_ = lean_ctor_get(v_impl_693_, 4);
                                    lean_dec(v_unused_775_);
                                    v_unused_776_ = lean_ctor_get(v_impl_693_, 3);
                                    lean_dec(v_unused_776_);
                                    v_unused_777_ = lean_ctor_get(v_impl_693_, 2);
                                    lean_dec(v_unused_777_);
                                    v_unused_778_ = lean_ctor_get(v_impl_693_, 1);
                                    lean_dec(v_unused_778_);
                                    v_unused_779_ = lean_ctor_get(v_impl_693_, 0);
                                    lean_dec(v_unused_779_);
                                    v___x_710_ = v_impl_693_;
                                    v_isShared_711_ = v_isSharedCheck_774_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_693_);
                                    v___x_710_ = lean_box(0);
                                    v_isShared_711_ = v_isSharedCheck_774_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_780_ = lean_ctor_get(v_impl_693_, 3);
                            lean_inc(v_l_780_);
                            if lean_obj_tag(v_l_780_) == 0 {
                                v_r_781_ = lean_ctor_get(v_impl_693_, 4);
                                v_k_782_ = lean_ctor_get(v_impl_693_, 1);
                                v_v_783_ = lean_ctor_get(v_impl_693_, 2);
                                v_isSharedCheck_794_ = (!lean_is_exclusive(v_impl_693_)) as u8;
                                if v_isSharedCheck_794_ == 0 {
                                    v_unused_795_ = lean_ctor_get(v_impl_693_, 3);
                                    lean_dec(v_unused_795_);
                                    v_unused_796_ = lean_ctor_get(v_impl_693_, 0);
                                    lean_dec(v_unused_796_);
                                    v___x_785_ = v_impl_693_;
                                    v_isShared_786_ = v_isSharedCheck_794_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_781_);
                                    lean_inc(v_v_783_);
                                    lean_inc(v_k_782_);
                                    lean_dec(v_impl_693_);
                                    v___x_785_ = lean_box(0);
                                    v_isShared_786_ = v_isSharedCheck_794_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_797_ = lean_ctor_get(v_impl_693_, 4);
                                lean_inc(v_r_797_);
                                if lean_obj_tag(v_r_797_) == 0 {
                                    v_k_798_ = lean_ctor_get(v_impl_693_, 1);
                                    v_v_799_ = lean_ctor_get(v_impl_693_, 2);
                                    v_isSharedCheck_822_ = (!lean_is_exclusive(v_impl_693_)) as u8;
                                    if v_isSharedCheck_822_ == 0 {
                                        v_unused_823_ = lean_ctor_get(v_impl_693_, 4);
                                        lean_dec(v_unused_823_);
                                        v_unused_824_ = lean_ctor_get(v_impl_693_, 3);
                                        lean_dec(v_unused_824_);
                                        v_unused_825_ = lean_ctor_get(v_impl_693_, 0);
                                        lean_dec(v_unused_825_);
                                        v___x_801_ = v_impl_693_;
                                        v_isShared_802_ = v_isSharedCheck_822_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_799_);
                                        lean_inc(v_k_798_);
                                        lean_dec(v_impl_693_);
                                        v___x_801_ = lean_box(0);
                                        v_isShared_802_ = v_isSharedCheck_822_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_826_ = lean_unsigned_to_nat(2);
                                    if v_isShared_691_ == 0 {
                                        lean_ctor_set(v___x_690_, 4, v_r_797_);
                                        lean_ctor_set(v___x_690_, 3, v_impl_693_);
                                        lean_ctor_set(v___x_690_, 0, v___x_826_);
                                        v___x_828_ = v___x_690_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
                                        lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_685_);
                                        lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_686_);
                                        lean_ctor_set(v_reuseFailAlloc_829_, 3, v_impl_693_);
                                        lean_ctor_set(v_reuseFailAlloc_829_, 4, v_r_797_);
                                        v___x_828_ = v_reuseFailAlloc_829_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_686_);
                        lean_dec(v_k_685_);
                        if v_isShared_691_ == 0 {
                            lean_ctor_set(v___x_690_, 2, v_v_682_);
                            lean_ctor_set(v___x_690_, 1, v_k_681_);
                            v___x_831_ = v___x_690_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_832_, 0, v_size_684_);
                            lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_681_);
                            lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_682_);
                            lean_ctor_set(v_reuseFailAlloc_832_, 3, v_l_687_);
                            lean_ctor_set(v_reuseFailAlloc_832_, 4, v_r_688_);
                            v___x_831_ = v_reuseFailAlloc_832_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_684_);
                        v_impl_833_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_681_, v_v_682_, v_r_688_);
                        v___x_834_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_687_) == 0 {
                            v_size_835_ = lean_ctor_get(v_l_687_, 0);
                            v_size_836_ = lean_ctor_get(v_impl_833_, 0);
                            lean_inc(v_size_836_);
                            v_k_837_ = lean_ctor_get(v_impl_833_, 1);
                            lean_inc(v_k_837_);
                            v_v_838_ = lean_ctor_get(v_impl_833_, 2);
                            lean_inc(v_v_838_);
                            v_l_839_ = lean_ctor_get(v_impl_833_, 3);
                            lean_inc(v_l_839_);
                            v_r_840_ = lean_ctor_get(v_impl_833_, 4);
                            lean_inc(v_r_840_);
                            v___x_841_ = lean_unsigned_to_nat(3);
                            v___x_842_ = lean_nat_mul(v___x_841_, v_size_835_);
                            v___x_843_ = lean_nat_dec_lt(v___x_842_, v_size_836_);
                            lean_dec(v___x_842_);
                            if v___x_843_ == 0 {
                                lean_dec(v_r_840_);
                                lean_dec(v_l_839_);
                                lean_dec(v_v_838_);
                                lean_dec(v_k_837_);
                                v___x_844_ = lean_nat_add(v___x_834_, v_size_835_);
                                v___x_845_ = lean_nat_add(v___x_844_, v_size_836_);
                                lean_dec(v_size_836_);
                                lean_dec(v___x_844_);
                                if v_isShared_691_ == 0 {
                                    lean_ctor_set(v___x_690_, 4, v_impl_833_);
                                    lean_ctor_set(v___x_690_, 0, v___x_845_);
                                    v___x_847_ = v___x_690_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
                                    lean_ctor_set(v_reuseFailAlloc_848_, 1, v_k_685_);
                                    lean_ctor_set(v_reuseFailAlloc_848_, 2, v_v_686_);
                                    lean_ctor_set(v_reuseFailAlloc_848_, 3, v_l_687_);
                                    lean_ctor_set(v_reuseFailAlloc_848_, 4, v_impl_833_);
                                    v___x_847_ = v_reuseFailAlloc_848_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_912_ = (!lean_is_exclusive(v_impl_833_)) as u8;
                                if v_isSharedCheck_912_ == 0 {
                                    v_unused_913_ = lean_ctor_get(v_impl_833_, 4);
                                    lean_dec(v_unused_913_);
                                    v_unused_914_ = lean_ctor_get(v_impl_833_, 3);
                                    lean_dec(v_unused_914_);
                                    v_unused_915_ = lean_ctor_get(v_impl_833_, 2);
                                    lean_dec(v_unused_915_);
                                    v_unused_916_ = lean_ctor_get(v_impl_833_, 1);
                                    lean_dec(v_unused_916_);
                                    v_unused_917_ = lean_ctor_get(v_impl_833_, 0);
                                    lean_dec(v_unused_917_);
                                    v___x_850_ = v_impl_833_;
                                    v_isShared_851_ = v_isSharedCheck_912_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_833_);
                                    v___x_850_ = lean_box(0);
                                    v_isShared_851_ = v_isSharedCheck_912_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_918_ = lean_ctor_get(v_impl_833_, 3);
                            lean_inc(v_l_918_);
                            if lean_obj_tag(v_l_918_) == 0 {
                                v_r_919_ = lean_ctor_get(v_impl_833_, 4);
                                v_k_920_ = lean_ctor_get(v_impl_833_, 1);
                                v_v_921_ = lean_ctor_get(v_impl_833_, 2);
                                v_isSharedCheck_944_ = (!lean_is_exclusive(v_impl_833_)) as u8;
                                if v_isSharedCheck_944_ == 0 {
                                    v_unused_945_ = lean_ctor_get(v_impl_833_, 3);
                                    lean_dec(v_unused_945_);
                                    v_unused_946_ = lean_ctor_get(v_impl_833_, 0);
                                    lean_dec(v_unused_946_);
                                    v___x_923_ = v_impl_833_;
                                    v_isShared_924_ = v_isSharedCheck_944_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_919_);
                                    lean_inc(v_v_921_);
                                    lean_inc(v_k_920_);
                                    lean_dec(v_impl_833_);
                                    v___x_923_ = lean_box(0);
                                    v_isShared_924_ = v_isSharedCheck_944_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_947_ = lean_ctor_get(v_impl_833_, 4);
                                lean_inc(v_r_947_);
                                if lean_obj_tag(v_r_947_) == 0 {
                                    v_k_948_ = lean_ctor_get(v_impl_833_, 1);
                                    v_v_949_ = lean_ctor_get(v_impl_833_, 2);
                                    v_isSharedCheck_960_ = (!lean_is_exclusive(v_impl_833_)) as u8;
                                    if v_isSharedCheck_960_ == 0 {
                                        v_unused_961_ = lean_ctor_get(v_impl_833_, 4);
                                        lean_dec(v_unused_961_);
                                        v_unused_962_ = lean_ctor_get(v_impl_833_, 3);
                                        lean_dec(v_unused_962_);
                                        v_unused_963_ = lean_ctor_get(v_impl_833_, 0);
                                        lean_dec(v_unused_963_);
                                        v___x_951_ = v_impl_833_;
                                        v_isShared_952_ = v_isSharedCheck_960_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_949_);
                                        lean_inc(v_k_948_);
                                        lean_dec(v_impl_833_);
                                        v___x_951_ = lean_box(0);
                                        v_isShared_952_ = v_isSharedCheck_960_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_964_ = lean_unsigned_to_nat(2);
                                    if v_isShared_691_ == 0 {
                                        lean_ctor_set(v___x_690_, 4, v_impl_833_);
                                        lean_ctor_set(v___x_690_, 3, v_r_947_);
                                        lean_ctor_set(v___x_690_, 0, v___x_964_);
                                        v___x_966_ = v___x_690_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
                                        lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_685_);
                                        lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_686_);
                                        lean_ctor_set(v_reuseFailAlloc_967_, 3, v_r_947_);
                                        lean_ctor_set(v_reuseFailAlloc_967_, 4, v_impl_833_);
                                        v___x_966_ = v_reuseFailAlloc_967_;
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
                return v___x_707_;
            }
            3 => {
                v_size_712_ = lean_ctor_get(v_l_699_, 0);
                v_size_713_ = lean_ctor_get(v_r_700_, 0);
                v_k_714_ = lean_ctor_get(v_r_700_, 1);
                v_v_715_ = lean_ctor_get(v_r_700_, 2);
                v_l_716_ = lean_ctor_get(v_r_700_, 3);
                v_r_717_ = lean_ctor_get(v_r_700_, 4);
                v___x_718_ = lean_unsigned_to_nat(2);
                v___x_719_ = lean_nat_mul(v___x_718_, v_size_712_);
                v___x_720_ = lean_nat_dec_lt(v_size_713_, v___x_719_);
                lean_dec(v___x_719_);
                if v___x_720_ == 0 {
                    lean_inc(v_r_717_);
                    lean_inc(v_l_716_);
                    lean_inc(v_v_715_);
                    lean_inc(v_k_714_);
                    v_isSharedCheck_749_ = (!lean_is_exclusive(v_r_700_)) as u8;
                    if v_isSharedCheck_749_ == 0 {
                        v_unused_750_ = lean_ctor_get(v_r_700_, 4);
                        lean_dec(v_unused_750_);
                        v_unused_751_ = lean_ctor_get(v_r_700_, 3);
                        lean_dec(v_unused_751_);
                        v_unused_752_ = lean_ctor_get(v_r_700_, 2);
                        lean_dec(v_unused_752_);
                        v_unused_753_ = lean_ctor_get(v_r_700_, 1);
                        lean_dec(v_unused_753_);
                        v_unused_754_ = lean_ctor_get(v_r_700_, 0);
                        lean_dec(v_unused_754_);
                        v___x_722_ = v_r_700_;
                        v_isShared_723_ = v_isSharedCheck_749_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_700_);
                        v___x_722_ = lean_box(0);
                        v_isShared_723_ = v_isSharedCheck_749_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_690_);
                    v___x_755_ = lean_nat_add(v___x_694_, v_size_696_);
                    lean_dec(v_size_696_);
                    v___x_756_ = lean_nat_add(v___x_755_, v_size_695_);
                    lean_dec(v___x_755_);
                    v___x_757_ = lean_nat_add(v___x_694_, v_size_695_);
                    v___x_758_ = lean_nat_add(v___x_757_, v_size_713_);
                    lean_dec(v___x_757_);
                    lean_inc_ref(v_r_688_);
                    if v_isShared_711_ == 0 {
                        lean_ctor_set(v___x_710_, 4, v_r_688_);
                        lean_ctor_set(v___x_710_, 3, v_r_700_);
                        lean_ctor_set(v___x_710_, 2, v_v_686_);
                        lean_ctor_set(v___x_710_, 1, v_k_685_);
                        lean_ctor_set(v___x_710_, 0, v___x_758_);
                        v___x_760_ = v___x_710_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_758_);
                        lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_685_);
                        lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_686_);
                        lean_ctor_set(v_reuseFailAlloc_773_, 3, v_r_700_);
                        lean_ctor_set(v_reuseFailAlloc_773_, 4, v_r_688_);
                        v___x_760_ = v_reuseFailAlloc_773_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_724_ = lean_nat_add(v___x_694_, v_size_696_);
                lean_dec(v_size_696_);
                v___x_725_ = lean_nat_add(v___x_724_, v_size_695_);
                lean_dec(v___x_724_);
                v___x_737_ = lean_nat_add(v___x_694_, v_size_712_);
                if lean_obj_tag(v_l_716_) == 0 {
                    v_size_747_ = lean_ctor_get(v_l_716_, 0);
                    lean_inc(v_size_747_);
                    v___y_739_ = v_size_747_;
                    state = 8;
                    continue;
                } else {
                    v___x_748_ = lean_unsigned_to_nat(0);
                    v___y_739_ = v___x_748_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_730_ = lean_nat_add(v___y_727_, v___y_729_);
                lean_dec(v___y_729_);
                lean_dec(v___y_727_);
                if v_isShared_723_ == 0 {
                    lean_ctor_set(v___x_722_, 4, v_r_688_);
                    lean_ctor_set(v___x_722_, 3, v_r_717_);
                    lean_ctor_set(v___x_722_, 2, v_v_686_);
                    lean_ctor_set(v___x_722_, 1, v_k_685_);
                    lean_ctor_set(v___x_722_, 0, v___x_730_);
                    v___x_732_ = v___x_722_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_730_);
                    lean_ctor_set(v_reuseFailAlloc_736_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_736_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_736_, 3, v_r_717_);
                    lean_ctor_set(v_reuseFailAlloc_736_, 4, v_r_688_);
                    v___x_732_ = v_reuseFailAlloc_736_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_711_ == 0 {
                    lean_ctor_set(v___x_710_, 4, v___x_732_);
                    lean_ctor_set(v___x_710_, 3, v___y_728_);
                    lean_ctor_set(v___x_710_, 2, v_v_715_);
                    lean_ctor_set(v___x_710_, 1, v_k_714_);
                    lean_ctor_set(v___x_710_, 0, v___x_725_);
                    v___x_734_ = v___x_710_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_725_);
                    lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_714_);
                    lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_715_);
                    lean_ctor_set(v_reuseFailAlloc_735_, 3, v___y_728_);
                    lean_ctor_set(v_reuseFailAlloc_735_, 4, v___x_732_);
                    v___x_734_ = v_reuseFailAlloc_735_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_734_;
            }
            8 => {
                v___x_740_ = lean_nat_add(v___x_737_, v___y_739_);
                lean_dec(v___y_739_);
                lean_dec(v___x_737_);
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v_l_716_);
                    lean_ctor_set(v___x_690_, 3, v_l_699_);
                    lean_ctor_set(v___x_690_, 2, v_v_698_);
                    lean_ctor_set(v___x_690_, 1, v_k_697_);
                    lean_ctor_set(v___x_690_, 0, v___x_740_);
                    v___x_742_ = v___x_690_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_697_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_698_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 3, v_l_699_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 4, v_l_716_);
                    v___x_742_ = v_reuseFailAlloc_746_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_743_ = lean_nat_add(v___x_694_, v_size_695_);
                if lean_obj_tag(v_r_717_) == 0 {
                    v_size_744_ = lean_ctor_get(v_r_717_, 0);
                    lean_inc(v_size_744_);
                    v___y_727_ = v___x_743_;
                    v___y_728_ = v___x_742_;
                    v___y_729_ = v_size_744_;
                    state = 5;
                    continue;
                } else {
                    v___x_745_ = lean_unsigned_to_nat(0);
                    v___y_727_ = v___x_743_;
                    v___y_728_ = v___x_742_;
                    v___y_729_ = v___x_745_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_767_ = (!lean_is_exclusive(v_r_688_)) as u8;
                if v_isSharedCheck_767_ == 0 {
                    v_unused_768_ = lean_ctor_get(v_r_688_, 4);
                    lean_dec(v_unused_768_);
                    v_unused_769_ = lean_ctor_get(v_r_688_, 3);
                    lean_dec(v_unused_769_);
                    v_unused_770_ = lean_ctor_get(v_r_688_, 2);
                    lean_dec(v_unused_770_);
                    v_unused_771_ = lean_ctor_get(v_r_688_, 1);
                    lean_dec(v_unused_771_);
                    v_unused_772_ = lean_ctor_get(v_r_688_, 0);
                    lean_dec(v_unused_772_);
                    v___x_762_ = v_r_688_;
                    v_isShared_763_ = v_isSharedCheck_767_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_688_);
                    v___x_762_ = lean_box(0);
                    v_isShared_763_ = v_isSharedCheck_767_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_763_ == 0 {
                    lean_ctor_set(v___x_762_, 4, v___x_760_);
                    lean_ctor_set(v___x_762_, 3, v_l_699_);
                    lean_ctor_set(v___x_762_, 2, v_v_698_);
                    lean_ctor_set(v___x_762_, 1, v_k_697_);
                    lean_ctor_set(v___x_762_, 0, v___x_756_);
                    v___x_765_ = v___x_762_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_756_);
                    lean_ctor_set(v_reuseFailAlloc_766_, 1, v_k_697_);
                    lean_ctor_set(v_reuseFailAlloc_766_, 2, v_v_698_);
                    lean_ctor_set(v_reuseFailAlloc_766_, 3, v_l_699_);
                    lean_ctor_set(v_reuseFailAlloc_766_, 4, v___x_760_);
                    v___x_765_ = v_reuseFailAlloc_766_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_765_;
            }
            13 => {
                v___x_787_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_781_);
                if v_isShared_786_ == 0 {
                    lean_ctor_set(v___x_785_, 3, v_r_781_);
                    lean_ctor_set(v___x_785_, 2, v_v_686_);
                    lean_ctor_set(v___x_785_, 1, v_k_685_);
                    lean_ctor_set(v___x_785_, 0, v___x_694_);
                    v___x_789_ = v___x_785_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_694_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 3, v_r_781_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 4, v_r_781_);
                    v___x_789_ = v_reuseFailAlloc_793_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v___x_789_);
                    lean_ctor_set(v___x_690_, 3, v_l_780_);
                    lean_ctor_set(v___x_690_, 2, v_v_783_);
                    lean_ctor_set(v___x_690_, 1, v_k_782_);
                    lean_ctor_set(v___x_690_, 0, v___x_787_);
                    v___x_791_ = v___x_690_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_787_);
                    lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_782_);
                    lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_783_);
                    lean_ctor_set(v_reuseFailAlloc_792_, 3, v_l_780_);
                    lean_ctor_set(v_reuseFailAlloc_792_, 4, v___x_789_);
                    v___x_791_ = v_reuseFailAlloc_792_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_791_;
            }
            16 => {
                v_k_803_ = lean_ctor_get(v_r_797_, 1);
                v_v_804_ = lean_ctor_get(v_r_797_, 2);
                v_isSharedCheck_818_ = (!lean_is_exclusive(v_r_797_)) as u8;
                if v_isSharedCheck_818_ == 0 {
                    v_unused_819_ = lean_ctor_get(v_r_797_, 4);
                    lean_dec(v_unused_819_);
                    v_unused_820_ = lean_ctor_get(v_r_797_, 3);
                    lean_dec(v_unused_820_);
                    v_unused_821_ = lean_ctor_get(v_r_797_, 0);
                    lean_dec(v_unused_821_);
                    v___x_806_ = v_r_797_;
                    v_isShared_807_ = v_isSharedCheck_818_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_804_);
                    lean_inc(v_k_803_);
                    lean_dec(v_r_797_);
                    v___x_806_ = lean_box(0);
                    v_isShared_807_ = v_isSharedCheck_818_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_808_ = lean_unsigned_to_nat(3);
                if v_isShared_807_ == 0 {
                    lean_ctor_set(v___x_806_, 4, v_l_780_);
                    lean_ctor_set(v___x_806_, 3, v_l_780_);
                    lean_ctor_set(v___x_806_, 2, v_v_799_);
                    lean_ctor_set(v___x_806_, 1, v_k_798_);
                    lean_ctor_set(v___x_806_, 0, v___x_694_);
                    v___x_810_ = v___x_806_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_694_);
                    lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_798_);
                    lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_799_);
                    lean_ctor_set(v_reuseFailAlloc_817_, 3, v_l_780_);
                    lean_ctor_set(v_reuseFailAlloc_817_, 4, v_l_780_);
                    v___x_810_ = v_reuseFailAlloc_817_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_802_ == 0 {
                    lean_ctor_set(v___x_801_, 4, v_l_780_);
                    lean_ctor_set(v___x_801_, 2, v_v_686_);
                    lean_ctor_set(v___x_801_, 1, v_k_685_);
                    lean_ctor_set(v___x_801_, 0, v___x_694_);
                    v___x_812_ = v___x_801_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_694_);
                    lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_816_, 3, v_l_780_);
                    lean_ctor_set(v_reuseFailAlloc_816_, 4, v_l_780_);
                    v___x_812_ = v_reuseFailAlloc_816_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v___x_812_);
                    lean_ctor_set(v___x_690_, 3, v___x_810_);
                    lean_ctor_set(v___x_690_, 2, v_v_804_);
                    lean_ctor_set(v___x_690_, 1, v_k_803_);
                    lean_ctor_set(v___x_690_, 0, v___x_808_);
                    v___x_814_ = v___x_690_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_808_);
                    lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_803_);
                    lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_804_);
                    lean_ctor_set(v_reuseFailAlloc_815_, 3, v___x_810_);
                    lean_ctor_set(v_reuseFailAlloc_815_, 4, v___x_812_);
                    v___x_814_ = v_reuseFailAlloc_815_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_814_;
            }
            21 => {
                return v___x_828_;
            }
            22 => {
                return v___x_831_;
            }
            23 => {
                return v___x_847_;
            }
            24 => {
                v_size_852_ = lean_ctor_get(v_l_839_, 0);
                v_k_853_ = lean_ctor_get(v_l_839_, 1);
                v_v_854_ = lean_ctor_get(v_l_839_, 2);
                v_l_855_ = lean_ctor_get(v_l_839_, 3);
                v_r_856_ = lean_ctor_get(v_l_839_, 4);
                v_size_857_ = lean_ctor_get(v_r_840_, 0);
                v___x_858_ = lean_unsigned_to_nat(2);
                v___x_859_ = lean_nat_mul(v___x_858_, v_size_857_);
                v___x_860_ = lean_nat_dec_lt(v_size_852_, v___x_859_);
                lean_dec(v___x_859_);
                if v___x_860_ == 0 {
                    lean_inc(v_r_856_);
                    lean_inc(v_l_855_);
                    lean_inc(v_v_854_);
                    lean_inc(v_k_853_);
                    v_isSharedCheck_888_ = (!lean_is_exclusive(v_l_839_)) as u8;
                    if v_isSharedCheck_888_ == 0 {
                        v_unused_889_ = lean_ctor_get(v_l_839_, 4);
                        lean_dec(v_unused_889_);
                        v_unused_890_ = lean_ctor_get(v_l_839_, 3);
                        lean_dec(v_unused_890_);
                        v_unused_891_ = lean_ctor_get(v_l_839_, 2);
                        lean_dec(v_unused_891_);
                        v_unused_892_ = lean_ctor_get(v_l_839_, 1);
                        lean_dec(v_unused_892_);
                        v_unused_893_ = lean_ctor_get(v_l_839_, 0);
                        lean_dec(v_unused_893_);
                        v___x_862_ = v_l_839_;
                        v_isShared_863_ = v_isSharedCheck_888_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_839_);
                        v___x_862_ = lean_box(0);
                        v_isShared_863_ = v_isSharedCheck_888_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_690_);
                    v___x_894_ = lean_nat_add(v___x_834_, v_size_835_);
                    v___x_895_ = lean_nat_add(v___x_894_, v_size_836_);
                    lean_dec(v_size_836_);
                    v___x_896_ = lean_nat_add(v___x_894_, v_size_852_);
                    lean_dec(v___x_894_);
                    lean_inc_ref(v_l_687_);
                    if v_isShared_851_ == 0 {
                        lean_ctor_set(v___x_850_, 4, v_l_839_);
                        lean_ctor_set(v___x_850_, 3, v_l_687_);
                        lean_ctor_set(v___x_850_, 2, v_v_686_);
                        lean_ctor_set(v___x_850_, 1, v_k_685_);
                        lean_ctor_set(v___x_850_, 0, v___x_896_);
                        v___x_898_ = v___x_850_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_896_);
                        lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_685_);
                        lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_686_);
                        lean_ctor_set(v_reuseFailAlloc_911_, 3, v_l_687_);
                        lean_ctor_set(v_reuseFailAlloc_911_, 4, v_l_839_);
                        v___x_898_ = v_reuseFailAlloc_911_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_864_ = lean_nat_add(v___x_834_, v_size_835_);
                v___x_865_ = lean_nat_add(v___x_864_, v_size_836_);
                lean_dec(v_size_836_);
                if lean_obj_tag(v_l_855_) == 0 {
                    v_size_886_ = lean_ctor_get(v_l_855_, 0);
                    lean_inc(v_size_886_);
                    v___y_878_ = v_size_886_;
                    state = 29;
                    continue;
                } else {
                    v___x_887_ = lean_unsigned_to_nat(0);
                    v___y_878_ = v___x_887_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_870_ = lean_nat_add(v___y_868_, v___y_869_);
                lean_dec(v___y_869_);
                lean_dec(v___y_868_);
                if v_isShared_863_ == 0 {
                    lean_ctor_set(v___x_862_, 4, v_r_840_);
                    lean_ctor_set(v___x_862_, 3, v_r_856_);
                    lean_ctor_set(v___x_862_, 2, v_v_838_);
                    lean_ctor_set(v___x_862_, 1, v_k_837_);
                    lean_ctor_set(v___x_862_, 0, v___x_870_);
                    v___x_872_ = v___x_862_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
                    lean_ctor_set(v_reuseFailAlloc_876_, 1, v_k_837_);
                    lean_ctor_set(v_reuseFailAlloc_876_, 2, v_v_838_);
                    lean_ctor_set(v_reuseFailAlloc_876_, 3, v_r_856_);
                    lean_ctor_set(v_reuseFailAlloc_876_, 4, v_r_840_);
                    v___x_872_ = v_reuseFailAlloc_876_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_851_ == 0 {
                    lean_ctor_set(v___x_850_, 4, v___x_872_);
                    lean_ctor_set(v___x_850_, 3, v___y_867_);
                    lean_ctor_set(v___x_850_, 2, v_v_854_);
                    lean_ctor_set(v___x_850_, 1, v_k_853_);
                    lean_ctor_set(v___x_850_, 0, v___x_865_);
                    v___x_874_ = v___x_850_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_865_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_853_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_854_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 3, v___y_867_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 4, v___x_872_);
                    v___x_874_ = v_reuseFailAlloc_875_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_874_;
            }
            29 => {
                v___x_879_ = lean_nat_add(v___x_864_, v___y_878_);
                lean_dec(v___y_878_);
                lean_dec(v___x_864_);
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v_l_855_);
                    lean_ctor_set(v___x_690_, 0, v___x_879_);
                    v___x_881_ = v___x_690_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_879_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 3, v_l_687_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 4, v_l_855_);
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_882_ = lean_nat_add(v___x_834_, v_size_857_);
                if lean_obj_tag(v_r_856_) == 0 {
                    v_size_883_ = lean_ctor_get(v_r_856_, 0);
                    lean_inc(v_size_883_);
                    v___y_867_ = v___x_881_;
                    v___y_868_ = v___x_882_;
                    v___y_869_ = v_size_883_;
                    state = 26;
                    continue;
                } else {
                    v___x_884_ = lean_unsigned_to_nat(0);
                    v___y_867_ = v___x_881_;
                    v___y_868_ = v___x_882_;
                    v___y_869_ = v___x_884_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_905_ = (!lean_is_exclusive(v_l_687_)) as u8;
                if v_isSharedCheck_905_ == 0 {
                    v_unused_906_ = lean_ctor_get(v_l_687_, 4);
                    lean_dec(v_unused_906_);
                    v_unused_907_ = lean_ctor_get(v_l_687_, 3);
                    lean_dec(v_unused_907_);
                    v_unused_908_ = lean_ctor_get(v_l_687_, 2);
                    lean_dec(v_unused_908_);
                    v_unused_909_ = lean_ctor_get(v_l_687_, 1);
                    lean_dec(v_unused_909_);
                    v_unused_910_ = lean_ctor_get(v_l_687_, 0);
                    lean_dec(v_unused_910_);
                    v___x_900_ = v_l_687_;
                    v_isShared_901_ = v_isSharedCheck_905_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_687_);
                    v___x_900_ = lean_box(0);
                    v_isShared_901_ = v_isSharedCheck_905_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_901_ == 0 {
                    lean_ctor_set(v___x_900_, 4, v_r_840_);
                    lean_ctor_set(v___x_900_, 3, v___x_898_);
                    lean_ctor_set(v___x_900_, 2, v_v_838_);
                    lean_ctor_set(v___x_900_, 1, v_k_837_);
                    lean_ctor_set(v___x_900_, 0, v___x_895_);
                    v___x_903_ = v___x_900_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_895_);
                    lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_837_);
                    lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_838_);
                    lean_ctor_set(v_reuseFailAlloc_904_, 3, v___x_898_);
                    lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_840_);
                    v___x_903_ = v_reuseFailAlloc_904_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_903_;
            }
            34 => {
                v_k_925_ = lean_ctor_get(v_l_918_, 1);
                v_v_926_ = lean_ctor_get(v_l_918_, 2);
                v_isSharedCheck_940_ = (!lean_is_exclusive(v_l_918_)) as u8;
                if v_isSharedCheck_940_ == 0 {
                    v_unused_941_ = lean_ctor_get(v_l_918_, 4);
                    lean_dec(v_unused_941_);
                    v_unused_942_ = lean_ctor_get(v_l_918_, 3);
                    lean_dec(v_unused_942_);
                    v_unused_943_ = lean_ctor_get(v_l_918_, 0);
                    lean_dec(v_unused_943_);
                    v___x_928_ = v_l_918_;
                    v_isShared_929_ = v_isSharedCheck_940_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_926_);
                    lean_inc(v_k_925_);
                    lean_dec(v_l_918_);
                    v___x_928_ = lean_box(0);
                    v_isShared_929_ = v_isSharedCheck_940_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_930_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_919_, 2);
                if v_isShared_929_ == 0 {
                    lean_ctor_set(v___x_928_, 4, v_r_919_);
                    lean_ctor_set(v___x_928_, 3, v_r_919_);
                    lean_ctor_set(v___x_928_, 2, v_v_686_);
                    lean_ctor_set(v___x_928_, 1, v_k_685_);
                    lean_ctor_set(v___x_928_, 0, v___x_834_);
                    v___x_932_ = v___x_928_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_834_);
                    lean_ctor_set(v_reuseFailAlloc_939_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_939_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_939_, 3, v_r_919_);
                    lean_ctor_set(v_reuseFailAlloc_939_, 4, v_r_919_);
                    v___x_932_ = v_reuseFailAlloc_939_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_919_);
                if v_isShared_924_ == 0 {
                    lean_ctor_set(v___x_923_, 3, v_r_919_);
                    lean_ctor_set(v___x_923_, 0, v___x_834_);
                    v___x_934_ = v___x_923_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_834_);
                    lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_920_);
                    lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_921_);
                    lean_ctor_set(v_reuseFailAlloc_938_, 3, v_r_919_);
                    lean_ctor_set(v_reuseFailAlloc_938_, 4, v_r_919_);
                    v___x_934_ = v_reuseFailAlloc_938_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v___x_934_);
                    lean_ctor_set(v___x_690_, 3, v___x_932_);
                    lean_ctor_set(v___x_690_, 2, v_v_926_);
                    lean_ctor_set(v___x_690_, 1, v_k_925_);
                    lean_ctor_set(v___x_690_, 0, v___x_930_);
                    v___x_936_ = v___x_690_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_930_);
                    lean_ctor_set(v_reuseFailAlloc_937_, 1, v_k_925_);
                    lean_ctor_set(v_reuseFailAlloc_937_, 2, v_v_926_);
                    lean_ctor_set(v_reuseFailAlloc_937_, 3, v___x_932_);
                    lean_ctor_set(v_reuseFailAlloc_937_, 4, v___x_934_);
                    v___x_936_ = v_reuseFailAlloc_937_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_936_;
            }
            39 => {
                v___x_953_ = lean_unsigned_to_nat(3);
                if v_isShared_952_ == 0 {
                    lean_ctor_set(v___x_951_, 4, v_l_918_);
                    lean_ctor_set(v___x_951_, 2, v_v_686_);
                    lean_ctor_set(v___x_951_, 1, v_k_685_);
                    lean_ctor_set(v___x_951_, 0, v___x_834_);
                    v___x_955_ = v___x_951_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_834_);
                    lean_ctor_set(v_reuseFailAlloc_959_, 1, v_k_685_);
                    lean_ctor_set(v_reuseFailAlloc_959_, 2, v_v_686_);
                    lean_ctor_set(v_reuseFailAlloc_959_, 3, v_l_918_);
                    lean_ctor_set(v_reuseFailAlloc_959_, 4, v_l_918_);
                    v___x_955_ = v_reuseFailAlloc_959_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 4, v_r_947_);
                    lean_ctor_set(v___x_690_, 3, v___x_955_);
                    lean_ctor_set(v___x_690_, 2, v_v_949_);
                    lean_ctor_set(v___x_690_, 1, v_k_948_);
                    lean_ctor_set(v___x_690_, 0, v___x_953_);
                    v___x_957_ = v___x_690_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_953_);
                    lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_948_);
                    lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_949_);
                    lean_ctor_set(v_reuseFailAlloc_958_, 3, v___x_955_);
                    lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_947_);
                    v___x_957_ = v_reuseFailAlloc_958_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_957_;
            }
            42 => {
                return v___x_966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_InputFile_initFacetConfigs___closed__0() -> *mut LeanObject {
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    v___x_971_ = lean_box(1);
    v___x_972_ = l_Lake_InputFile_defaultFacetConfig;
    v___x_973_ = l_Lake_InputFile_defaultFacet;
    v___x_974_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_973_, v___x_972_, v___x_971_);
    return v___x_974_;
}
pub unsafe fn _init_l_Lake_InputFile_initFacetConfigs() -> *mut LeanObject {
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    v___x_975_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFile_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFile_initFacetConfigs___closed__0_once),
        _init_l_Lake_InputFile_initFacetConfigs___closed__0,
    );
    return v___x_975_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0(
    mut v_00_u03b2_976_: *mut LeanObject,
    mut v_k_977_: *mut LeanObject,
    mut v_v_978_: *mut LeanObject,
    mut v_t_979_: *mut LeanObject,
    mut v_hl_980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v_k_977_, v_v_978_, v_t_979_);
    return v___x_981_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(
    mut v_filter_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
) -> u8 {
    let mut v_filter_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    v_filter_984_ = lean_ctor_get(v_filter_982_, 0);
    lean_inc_ref(v_filter_984_);
    lean_dec_ref(v_filter_982_);
    v___x_985_ = lean_apply_1(v_filter_984_, v___y_983_);
    v___x_986_ = (lean_unbox(v___x_985_) as u8);
    return v___x_986_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed(
    mut v_filter_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_989_: u8 = 0;
    let mut v_r_990_: *mut LeanObject = core::ptr::null_mut();
    v_res_989_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0(
        v_filter_987_,
        v___y_988_,
    );
    v_r_990_ = lean_box((v_res_989_) as usize);
    return v_r_990_;
}
pub unsafe fn _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__0;
    v___x_993_ = l_Lake_BuildTrace_nil(v___x_992_);
    return v___x_993_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(
    mut v___x_994_: *mut LeanObject,
    mut v_text_995_: u8,
    mut v___f_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1_once
        ),
        _init_l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___closed__1,
    );
    v___x_1005_ = l_Lake_inputDir(
        v___x_994_,
        v_text_995_,
        v___f_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___x_1004_,
    );
    v___x_1006_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1006_, 0, v___x_1005_);
    lean_ctor_set(v___x_1006_, 1, v___y_1002_);
    return v___x_1006_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed(
    mut v___x_1007_: *mut LeanObject,
    mut v_text_1008_: *mut LeanObject,
    mut v___f_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
    mut v___y_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
    mut v___y_1013_: *mut LeanObject,
    mut v___y_1014_: *mut LeanObject,
    mut v___y_1015_: *mut LeanObject,
    mut v___y_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_text_boxed_1017_: u8 = 0;
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_text_boxed_1017_ = (lean_unbox(v_text_1008_) as u8);
    v_res_1018_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1(
        v___x_1007_,
        v_text_boxed_1017_,
        v___f_1009_,
        v___y_1010_,
        v___y_1011_,
        v___y_1012_,
        v___y_1013_,
        v___y_1014_,
        v___y_1015_,
    );
    lean_dec_ref(v___y_1014_);
    lean_dec(v___y_1013_);
    lean_dec(v___y_1012_);
    lean_dec(v___y_1011_);
    return v_res_1018_;
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(
    mut v_t_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_1032_: u8 = 0;
    let mut v_filter_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v_task_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v_registeredJobs_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: u8 = 0;
    let mut v_job_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut v_unused_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1027_ = lean_ctor_get(v_t_1019_, 0);
                lean_inc_ref(v_pkg_1027_);
                v_config_1028_ = lean_ctor_get(v_t_1019_, 2);
                lean_inc(v_config_1028_);
                v_name_1029_ = lean_ctor_get(v_t_1019_, 1);
                lean_inc(v_name_1029_);
                lean_dec_ref(v_t_1019_);
                v_dir_1030_ = lean_ctor_get(v_pkg_1027_, 4);
                lean_inc_ref(v_dir_1030_);
                lean_dec_ref(v_pkg_1027_);
                v_path_1031_ = lean_ctor_get(v_config_1028_, 0);
                lean_inc_ref(v_path_1031_);
                v_text_1032_ = lean_ctor_get_uint8(
                    v_config_1028_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_filter_1033_ = lean_ctor_get(v_config_1028_, 1);
                lean_inc_ref(v_filter_1033_);
                lean_dec(v_config_1028_);
                v___x_1034_ = lean_box(0);
                v___f_1035_ = lean_alloc_closure(
                    l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1035_, 0, v_filter_1033_);
                v___x_1036_ = l_Lake_joinRelative(v_dir_1030_, v_path_1031_);
                v___x_1037_ = lean_box((v_text_1032_) as usize);
                v___f_1038_ = lean_alloc_closure(
                    l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___lam__1___boxed
                        as *mut core::ffi::c_void,
                    10,
                    3,
                );
                lean_closure_set(v___f_1038_, 0, v___x_1036_);
                lean_closure_set(v___f_1038_, 1, v___x_1037_);
                lean_closure_set(v___f_1038_, 2, v___f_1035_);
                v___x_1039_ = l_Lake_ensureJob___redArg(
                    v___x_1034_,
                    v___f_1038_,
                    v_a_1020_,
                    v_a_1021_,
                    v_a_1022_,
                    v_a_1023_,
                    v_a_1024_,
                    v_a_1025_,
                );
                if lean_obj_tag(v___x_1039_) == 0 {
                    v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
                    v_a_1041_ = lean_ctor_get(v___x_1039_, 1);
                    v_isSharedCheck_1067_ = (!lean_is_exclusive(v___x_1039_)) as u8;
                    if v_isSharedCheck_1067_ == 0 {
                        v___x_1043_ = v___x_1039_;
                        v_isShared_1044_ = v_isSharedCheck_1067_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1041_);
                        lean_inc(v_a_1040_);
                        lean_dec(v___x_1039_);
                        v___x_1043_ = lean_box(0);
                        v_isShared_1044_ = v_isSharedCheck_1067_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1029_);
                    return v___x_1039_;
                }
            }
            1 => {
                v_task_1045_ = lean_ctor_get(v_a_1040_, 0);
                v_kind_1046_ = lean_ctor_get(v_a_1040_, 1);
                v_isSharedCheck_1065_ = (!lean_is_exclusive(v_a_1040_)) as u8;
                if v_isSharedCheck_1065_ == 0 {
                    v_unused_1066_ = lean_ctor_get(v_a_1040_, 2);
                    lean_dec(v_unused_1066_);
                    v___x_1048_ = v_a_1040_;
                    v_isShared_1049_ = v_isSharedCheck_1065_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_1046_);
                    lean_inc(v_task_1045_);
                    lean_dec(v_a_1040_);
                    v___x_1048_ = lean_box(0);
                    v_isShared_1049_ = v_isSharedCheck_1065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1050_ = lean_ctor_get(v_a_1024_, 3);
                v___x_1051_ = lean_st_ref_take(v_registeredJobs_1050_);
                v___x_1052_ = 1;
                v___x_1053_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_1029_,
                    v___x_1052_,
                );
                v___x_1054_ = 0;
                if v_isShared_1049_ == 0 {
                    lean_ctor_set(v___x_1048_, 2, v___x_1053_);
                    v_job_1056_ = v___x_1048_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_task_1045_);
                    lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_kind_1046_);
                    lean_ctor_set(v_reuseFailAlloc_1064_, 2, v___x_1053_);
                    v_job_1056_ = v_reuseFailAlloc_1064_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_1056_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1054_,
                );
                lean_inc_ref(v_job_1056_);
                v___x_1057_ = l_Lake_Job_toOpaque___redArg(v_job_1056_);
                v___x_1058_ = lean_array_push(v___x_1051_, v___x_1057_);
                v___x_1059_ = lean_st_ref_set(v_registeredJobs_1050_, v___x_1058_);
                v___x_1060_ = l_Lake_Job_renew___redArg(v_job_1056_);
                if v_isShared_1044_ == 0 {
                    lean_ctor_set(v___x_1043_, 0, v___x_1060_);
                    v___x_1062_ = v___x_1043_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_a_1041_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch___boxed(
    mut v_t_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1076_: *mut LeanObject = core::ptr::null_mut();
    v_res_1076_ = l___private_Lake_Build_InputFile_0__Lake_InputDir_recFetch(
        v_t_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_,
    );
    lean_dec_ref(v_a_1073_);
    lean_dec(v_a_1072_);
    lean_dec(v_a_1071_);
    lean_dec(v_a_1070_);
    return v_res_1076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(
    mut v_sz_1077_: usize,
    mut v_i_1078_: usize,
    mut v_bs_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1080_: u8 = 0;
    let mut v_v_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: usize = 0;
    let mut v___x_1087_: usize = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1080_ = lean_usize_dec_lt(v_i_1078_, v_sz_1077_);
                if v___x_1080_ == 0 {
                    return v_bs_1079_;
                } else {
                    v_v_1081_ = lean_array_uget(v_bs_1079_, v_i_1078_);
                    v___x_1082_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1083_ = lean_array_uset(v_bs_1079_, v_i_1078_, v___x_1082_);
                    v___x_1084_ = l_Lake_mkRelPathString(v_v_1081_);
                    v___x_1085_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1085_, 0, v___x_1084_);
                    v___x_1086_ = 1usize;
                    v___x_1087_ = lean_usize_add(v_i_1078_, v___x_1086_);
                    v___x_1088_ = lean_array_uset(v_bs_x27_1083_, v_i_1078_, v___x_1085_);
                    v_i_1078_ = v___x_1087_;
                    v_bs_1079_ = v___x_1088_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2___boxed(
    mut v_sz_1090_: *mut LeanObject,
    mut v_i_1091_: *mut LeanObject,
    mut v_bs_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1093_: usize = 0;
    let mut v_i_boxed_1094_: usize = 0;
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1093_ = lean_unbox_usize(v_sz_1090_);
    lean_dec(v_sz_1090_);
    v_i_boxed_1094_ = lean_unbox_usize(v_i_1091_);
    lean_dec(v_i_1091_);
    v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_1093_, v_i_boxed_1094_, v_bs_1092_);
    return v_res_1095_;
}
pub unsafe fn l_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(
    mut v_a_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1097_: usize = 0;
    let mut v___x_1098_: usize = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1097_ = lean_array_size(v_a_1096_);
    v___x_1098_ = 0usize;
    v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1_spec__2(v_sz_1097_, v___x_1098_, v_a_1096_);
    v___x_1100_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1100_, 0, v___x_1099_);
    return v___x_1100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(
    mut v_as_1102_: *mut LeanObject,
    mut v_i_1103_: usize,
    mut v_stop_1104_: usize,
    mut v_b_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: usize = 0;
    let mut v___x_1112_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1106_ = lean_usize_dec_eq(v_i_1103_, v_stop_1104_);
                if v___x_1106_ == 0 {
                    v___x_1107_ = lean_array_uget_borrowed(v_as_1102_, v_i_1103_);
                    v___x_1108_ = lean_string_append(v_b_1105_, v___x_1107_);
                    v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___closed__0;
                    v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
                    v___x_1111_ = 1usize;
                    v___x_1112_ = lean_usize_add(v_i_1103_, v___x_1111_);
                    v_i_1103_ = v___x_1112_;
                    v_b_1105_ = v___x_1110_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1105_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0___boxed(
    mut v_as_1114_: *mut LeanObject,
    mut v_i_1115_: *mut LeanObject,
    mut v_stop_1116_: *mut LeanObject,
    mut v_b_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1118_: usize = 0;
    let mut v_stop_boxed_1119_: usize = 0;
    let mut v_res_1120_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1118_ = lean_unbox_usize(v_i_1115_);
    lean_dec(v_i_1115_);
    v_stop_boxed_1119_ = lean_unbox_usize(v_stop_1116_);
    lean_dec(v_stop_1116_);
    v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_as_1114_, v_i_boxed_1118_, v_stop_boxed_1119_, v_b_1117_);
    lean_dec_ref(v_as_1114_);
    return v_res_1120_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(
    mut v_fmt_1122_: u8,
    mut v_a_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: usize = 0;
    let mut v___x_1138_: usize = 0;
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_fmt_1122_ == 0 {
                    v___x_1132_ = l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___closed__0;
                    v___x_1133_ = lean_unsigned_to_nat(0);
                    v___x_1134_ = lean_array_get_size(v_a_1123_);
                    v___x_1135_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
                    if v___x_1135_ == 0 {
                        lean_dec_ref(v_a_1123_);
                        v___y_1125_ = v___x_1132_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1136_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
                        if v___x_1136_ == 0 {
                            if v___x_1135_ == 0 {
                                lean_dec_ref(v_a_1123_);
                                v___y_1125_ = v___x_1132_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1137_ = 0usize;
                                v___x_1138_ = lean_usize_of_nat(v___x_1134_);
                                v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_a_1123_, v___x_1137_, v___x_1138_, v___x_1132_);
                                lean_dec_ref(v_a_1123_);
                                v___y_1125_ = v___x_1139_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1140_ = 0usize;
                            v___x_1141_ = lean_usize_of_nat(v___x_1134_);
                            v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__0(v_a_1123_, v___x_1140_, v___x_1141_, v___x_1132_);
                            lean_dec_ref(v_a_1123_);
                            v___y_1125_ = v___x_1142_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1143_ = l_Array_toJson___at___00Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0_spec__1(v_a_1123_);
                    v___x_1144_ = l_Lean_Json_compress(v___x_1143_);
                    return v___x_1144_;
                }
            }
            1 => {
                v___x_1126_ = lean_unsigned_to_nat(1);
                v___x_1127_ = lean_unsigned_to_nat(0);
                v___x_1128_ = lean_string_utf8_byte_size(v___y_1125_);
                lean_inc_ref(v___y_1125_);
                v___x_1129_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1129_, 0, v___y_1125_);
                lean_ctor_set(v___x_1129_, 1, v___x_1127_);
                lean_ctor_set(v___x_1129_, 2, v___x_1128_);
                v___x_1130_ = l_String_Slice_Pos_prevn(v___x_1129_, v___x_1128_, v___x_1126_);
                lean_dec_ref_known(v___x_1129_, 3);
                v___x_1131_ = lean_string_utf8_extract(v___y_1125_, v___x_1127_, v___x_1130_);
                lean_dec(v___x_1130_);
                lean_dec_ref(v___y_1125_);
                return v___x_1131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0___boxed(
    mut v_fmt_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_1147_: u8 = 0;
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1147_ = (lean_unbox(v_fmt_1145_) as u8);
    v_res_1148_ = l_Lake_formatQuery___at___00Lake_InputDir_defaultFacetConfig_spec__0(
        v_fmt_boxed_1147_,
        v_a_1146_,
    );
    return v_res_1148_;
}
pub unsafe fn _init_l_Lake_InputDir_defaultFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    v___f_1151_ = l_Lake_InputDir_defaultFacetConfig___closed__0;
    v___x_1152_ = 1;
    v___x_1153_ = lean_box(0);
    v___x_1154_ = l_Lake_InputDir_defaultFacetConfig___closed__1;
    v___x_1155_ = l_Lake_InputDir_keyword;
    v___x_1156_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_1156_, 0, v___x_1155_);
    lean_ctor_set(v___x_1156_, 1, v___x_1154_);
    lean_ctor_set(v___x_1156_, 2, v___x_1153_);
    lean_ctor_set(v___x_1156_, 3, v___f_1151_);
    lean_ctor_set_uint8(
        v___x_1156_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_1152_,
    );
    lean_ctor_set_uint8(
        v___x_1156_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_1152_,
    );
    return v___x_1156_;
}
pub unsafe fn _init_l_Lake_InputDir_defaultFacetConfig() -> *mut LeanObject {
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDir_defaultFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_InputDir_defaultFacetConfig___closed__2_once),
        _init_l_Lake_InputDir_defaultFacetConfig___closed__2,
    );
    return v___x_1157_;
}
pub unsafe fn _init_l_Lake_InputDir_initFacetConfigs___closed__0() -> *mut LeanObject {
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1158_ = lean_box(1);
    v___x_1159_ = l_Lake_InputDir_defaultFacetConfig;
    v___x_1160_ = l_Lake_InputDir_defaultFacet;
    v___x_1161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_InputFile_initFacetConfigs_spec__0___redArg(v___x_1160_, v___x_1159_, v___x_1158_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lake_InputDir_initFacetConfigs() -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDir_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDir_initFacetConfigs___closed__0_once),
        _init_l_Lake_InputDir_initFacetConfigs___closed__0,
    );
    return v___x_1162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_InputFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Common(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_InputFile_defaultFacetConfig = _init_l_Lake_InputFile_defaultFacetConfig();
    lean_mark_persistent(l_Lake_InputFile_defaultFacetConfig);
    l_Lake_InputFile_initFacetConfigs = _init_l_Lake_InputFile_initFacetConfigs();
    lean_mark_persistent(l_Lake_InputFile_initFacetConfigs);
    l_Lake_InputDir_defaultFacetConfig = _init_l_Lake_InputDir_defaultFacetConfig();
    lean_mark_persistent(l_Lake_InputDir_defaultFacetConfig);
    l_Lake_InputDir_initFacetConfigs = _init_l_Lake_InputDir_initFacetConfigs();
    lean_mark_persistent(l_Lake_InputDir_initFacetConfigs);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_InputFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_InputFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Common(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_InputFile(builtin);
}

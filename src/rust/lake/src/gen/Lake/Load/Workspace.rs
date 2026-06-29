// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: Lake.Load.Config Lake.Config.Workspace Lake.Load.Resolve Lake.Load.Package Lake.Load.Lean.Eval Lake.Load.Toml Lake.Build.InitFacets
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lake::Build::InitFacets::{
    initialize_Lake_Build_InitFacets, l_Lake_initFacetConfigs,
    runtime_initialize_Lake_Build_InitFacets,
};
use crate::r#gen::Lake::Config::Env::l_Lake_Env_leanSearchPath;
use crate::r#gen::Lake::Config::FacetConfig::l_Lake_FacetConfigMap_insert;
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, l_Lake_computeLakeCache,
    runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Load::Lean::Eval::{
    initialize_Lake_Load_Lean_Eval, runtime_initialize_Lake_Load_Lean_Eval,
};
use crate::r#gen::Lake::Load::Manifest::l_Lake_Manifest_load_x3f;
use crate::r#gen::Lake::Load::Package::{
    initialize_Lake_Load_Package, l_Lake_loadConfigFile___redArg, l_Lake_mkPackage,
    l_Lake_resolveConfigFile, runtime_initialize_Lake_Load_Package,
};
use crate::r#gen::Lake::Load::Resolve::{
    initialize_Lake_Load_Resolve, l_Lake_Workspace_materializeDeps,
    l_Lake_Workspace_updateAndMaterialize, runtime_initialize_Lake_Load_Resolve,
};
use crate::r#gen::Lake::Load::Toml::{
    initialize_Lake_Load_Toml, l_Lake_loadLakeConfig, runtime_initialize_Lake_Load_Toml,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_empty;
use crate::r#gen::Lean::Util::Path::l_Lean_searchPathRef;
use crate::ffi::lean_array_uget_borrowed;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_usize_dec_eq,
};
use crate::ffi::lean_st_ref_set;
pub static l_Lake_loadWorkspaceRoot___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [91, 114, 111, 111, 116, 93, 0],
    };
static mut l_Lake_loadWorkspaceRoot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_loadWorkspaceRoot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_loadWorkspace___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_loadWorkspace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_loadWorkspace___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(
    mut v_as_609_: *mut crate::leanh::LeanObject,
    mut v_i_610_: usize,
    mut v_stop_611_: usize,
    mut v_b_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: usize = 0;
    let mut v___x_619_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_613_ = lean_usize_dec_eq(v_i_610_, v_stop_611_);
                if v___x_613_ == 0 {
                    v___x_614_ = lean_array_uget_borrowed(v_as_609_, v_i_610_);
                    v_name_615_ = crate::leanh::lean_ctor_get(v___x_614_, 0);
                    v_config_616_ = crate::leanh::lean_ctor_get(v___x_614_, 1);
                    crate::leanh::lean_inc(v_config_616_);
                    crate::leanh::lean_inc(v_name_615_);
                    v___x_617_ = l_Lake_FacetConfigMap_insert(v_name_615_, v_config_616_, v_b_612_);
                    v___x_618_ = 1usize;
                    v___x_619_ = lean_usize_add(v_i_610_, v___x_618_);
                    v_i_610_ = v___x_619_;
                    v_b_612_ = v___x_617_;
                    state = 0;
                    continue;
                } else {
                    return v_b_612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1___boxed(
    mut v_as_621_: *mut crate::leanh::LeanObject,
    mut v_i_622_: *mut crate::leanh::LeanObject,
    mut v_stop_623_: *mut crate::leanh::LeanObject,
    mut v_b_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_625_: usize = 0;
    let mut v_stop_boxed_626_: usize = 0;
    let mut v_res_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_625_ = crate::leanh::lean_unbox_usize(v_i_622_);
    crate::leanh::lean_dec(v_i_622_);
    v_stop_boxed_626_ = crate::leanh::lean_unbox_usize(v_stop_623_);
    crate::leanh::lean_dec(v_stop_623_);
    v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_as_621_, v_i_boxed_625_, v_stop_boxed_626_, v_b_624_);
    crate::leanh::lean_dec_ref(v_as_621_);
    return v_res_627_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(
    mut v_k_628_: *mut crate::leanh::LeanObject,
    mut v_v_629_: *mut crate::leanh::LeanObject,
    mut v_t_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: u8 = 0;
    let mut v_impl_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v_size_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut v_unused_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_710_: u8 = 0;
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_714_: u8 = 0;
    let mut v_unused_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_721_: u8 = 0;
    let mut v_unused_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v_k_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut v_unused_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_unused_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_size_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_835_: u8 = 0;
    let mut v_unused_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_848_: u8 = 0;
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_852_: u8 = 0;
    let mut v_unused_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_unused_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v_k_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_unused_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v_unused_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_907_: u8 = 0;
    let mut v_unused_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_630_) == 0 {
                    v_size_631_ = crate::leanh::lean_ctor_get(v_t_630_, 0);
                    v_k_632_ = crate::leanh::lean_ctor_get(v_t_630_, 1);
                    v_v_633_ = crate::leanh::lean_ctor_get(v_t_630_, 2);
                    v_l_634_ = crate::leanh::lean_ctor_get(v_t_630_, 3);
                    v_r_635_ = crate::leanh::lean_ctor_get(v_t_630_, 4);
                    v_isSharedCheck_915_ = (!crate::leanh::lean_is_exclusive(v_t_630_)) as u8;
                    if v_isSharedCheck_915_ == 0 {
                        v___x_637_ = v_t_630_;
                        v_isShared_638_ = v_isSharedCheck_915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_635_);
                        crate::leanh::lean_inc(v_l_634_);
                        crate::leanh::lean_inc(v_v_633_);
                        crate::leanh::lean_inc(v_k_632_);
                        crate::leanh::lean_inc(v_size_631_);
                        crate::leanh::lean_dec(v_t_630_);
                        v___x_637_ = crate::leanh::lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_916_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_917_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_917_, 0, v___x_916_);
                    crate::leanh::lean_ctor_set(v___x_917_, 1, v_k_628_);
                    crate::leanh::lean_ctor_set(v___x_917_, 2, v_v_629_);
                    crate::leanh::lean_ctor_set(v___x_917_, 3, v_t_630_);
                    crate::leanh::lean_ctor_set(v___x_917_, 4, v_t_630_);
                    return v___x_917_;
                }
            }
            1 => {
                v___x_639_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_628_, v_k_632_);
                match v___x_639_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_631_);
                        v_impl_640_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_628_, v_v_629_, v_l_634_);
                        v___x_641_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_635_) == 0 {
                            v_size_642_ = crate::leanh::lean_ctor_get(v_r_635_, 0);
                            v_size_643_ = crate::leanh::lean_ctor_get(v_impl_640_, 0);
                            crate::leanh::lean_inc(v_size_643_);
                            v_k_644_ = crate::leanh::lean_ctor_get(v_impl_640_, 1);
                            crate::leanh::lean_inc(v_k_644_);
                            v_v_645_ = crate::leanh::lean_ctor_get(v_impl_640_, 2);
                            crate::leanh::lean_inc(v_v_645_);
                            v_l_646_ = crate::leanh::lean_ctor_get(v_impl_640_, 3);
                            crate::leanh::lean_inc(v_l_646_);
                            v_r_647_ = crate::leanh::lean_ctor_get(v_impl_640_, 4);
                            crate::leanh::lean_inc(v_r_647_);
                            v___x_648_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_649_ = lean_nat_mul(v___x_648_, v_size_642_);
                            v___x_650_ = lean_nat_dec_lt(v___x_649_, v_size_643_);
                            crate::leanh::lean_dec(v___x_649_);
                            if v___x_650_ == 0 {
                                crate::leanh::lean_dec(v_r_647_);
                                crate::leanh::lean_dec(v_l_646_);
                                crate::leanh::lean_dec(v_v_645_);
                                crate::leanh::lean_dec(v_k_644_);
                                v___x_651_ = lean_nat_add(v___x_641_, v_size_643_);
                                crate::leanh::lean_dec(v_size_643_);
                                v___x_652_ = lean_nat_add(v___x_651_, v_size_642_);
                                crate::leanh::lean_dec(v___x_651_);
                                if v_isShared_638_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_637_, 3, v_impl_640_);
                                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_652_);
                                    v___x_654_ = v___x_637_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_655_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_655_,
                                        0,
                                        v___x_652_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_632_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_633_);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_655_,
                                        3,
                                        v_impl_640_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_635_);
                                    v___x_654_ = v_reuseFailAlloc_655_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_721_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                if v_isSharedCheck_721_ == 0 {
                                    v_unused_722_ = crate::leanh::lean_ctor_get(v_impl_640_, 4);
                                    crate::leanh::lean_dec(v_unused_722_);
                                    v_unused_723_ = crate::leanh::lean_ctor_get(v_impl_640_, 3);
                                    crate::leanh::lean_dec(v_unused_723_);
                                    v_unused_724_ = crate::leanh::lean_ctor_get(v_impl_640_, 2);
                                    crate::leanh::lean_dec(v_unused_724_);
                                    v_unused_725_ = crate::leanh::lean_ctor_get(v_impl_640_, 1);
                                    crate::leanh::lean_dec(v_unused_725_);
                                    v_unused_726_ = crate::leanh::lean_ctor_get(v_impl_640_, 0);
                                    crate::leanh::lean_dec(v_unused_726_);
                                    v___x_657_ = v_impl_640_;
                                    v_isShared_658_ = v_isSharedCheck_721_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_640_);
                                    v___x_657_ = crate::leanh::lean_box(0);
                                    v_isShared_658_ = v_isSharedCheck_721_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_727_ = crate::leanh::lean_ctor_get(v_impl_640_, 3);
                            crate::leanh::lean_inc(v_l_727_);
                            if crate::leanh::lean_obj_tag(v_l_727_) == 0 {
                                v_r_728_ = crate::leanh::lean_ctor_get(v_impl_640_, 4);
                                v_k_729_ = crate::leanh::lean_ctor_get(v_impl_640_, 1);
                                v_v_730_ = crate::leanh::lean_ctor_get(v_impl_640_, 2);
                                v_isSharedCheck_741_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                if v_isSharedCheck_741_ == 0 {
                                    v_unused_742_ = crate::leanh::lean_ctor_get(v_impl_640_, 3);
                                    crate::leanh::lean_dec(v_unused_742_);
                                    v_unused_743_ = crate::leanh::lean_ctor_get(v_impl_640_, 0);
                                    crate::leanh::lean_dec(v_unused_743_);
                                    v___x_732_ = v_impl_640_;
                                    v_isShared_733_ = v_isSharedCheck_741_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_728_);
                                    crate::leanh::lean_inc(v_v_730_);
                                    crate::leanh::lean_inc(v_k_729_);
                                    crate::leanh::lean_dec(v_impl_640_);
                                    v___x_732_ = crate::leanh::lean_box(0);
                                    v_isShared_733_ = v_isSharedCheck_741_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_744_ = crate::leanh::lean_ctor_get(v_impl_640_, 4);
                                crate::leanh::lean_inc(v_r_744_);
                                if crate::leanh::lean_obj_tag(v_r_744_) == 0 {
                                    v_k_745_ = crate::leanh::lean_ctor_get(v_impl_640_, 1);
                                    v_v_746_ = crate::leanh::lean_ctor_get(v_impl_640_, 2);
                                    v_isSharedCheck_769_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                    if v_isSharedCheck_769_ == 0 {
                                        v_unused_770_ = crate::leanh::lean_ctor_get(v_impl_640_, 4);
                                        crate::leanh::lean_dec(v_unused_770_);
                                        v_unused_771_ = crate::leanh::lean_ctor_get(v_impl_640_, 3);
                                        crate::leanh::lean_dec(v_unused_771_);
                                        v_unused_772_ = crate::leanh::lean_ctor_get(v_impl_640_, 0);
                                        crate::leanh::lean_dec(v_unused_772_);
                                        v___x_748_ = v_impl_640_;
                                        v_isShared_749_ = v_isSharedCheck_769_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_746_);
                                        crate::leanh::lean_inc(v_k_745_);
                                        crate::leanh::lean_dec(v_impl_640_);
                                        v___x_748_ = crate::leanh::lean_box(0);
                                        v_isShared_749_ = v_isSharedCheck_769_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_773_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_638_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_637_, 4, v_r_744_);
                                        crate::leanh::lean_ctor_set(v___x_637_, 3, v_impl_640_);
                                        crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_773_);
                                        v___x_775_ = v___x_637_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_776_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            0,
                                            v___x_773_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            1,
                                            v_k_632_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            2,
                                            v_v_633_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            3,
                                            v_impl_640_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            4,
                                            v_r_744_,
                                        );
                                        v___x_775_ = v_reuseFailAlloc_776_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_633_);
                        crate::leanh::lean_dec(v_k_632_);
                        if v_isShared_638_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_629_);
                            crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_628_);
                            v___x_778_ = v___x_637_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_779_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 0, v_size_631_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_628_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_629_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_634_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 4, v_r_635_);
                            v___x_778_ = v_reuseFailAlloc_779_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_631_);
                        v_impl_780_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_628_, v_v_629_, v_r_635_);
                        v___x_781_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_634_) == 0 {
                            v_size_782_ = crate::leanh::lean_ctor_get(v_l_634_, 0);
                            v_size_783_ = crate::leanh::lean_ctor_get(v_impl_780_, 0);
                            crate::leanh::lean_inc(v_size_783_);
                            v_k_784_ = crate::leanh::lean_ctor_get(v_impl_780_, 1);
                            crate::leanh::lean_inc(v_k_784_);
                            v_v_785_ = crate::leanh::lean_ctor_get(v_impl_780_, 2);
                            crate::leanh::lean_inc(v_v_785_);
                            v_l_786_ = crate::leanh::lean_ctor_get(v_impl_780_, 3);
                            crate::leanh::lean_inc(v_l_786_);
                            v_r_787_ = crate::leanh::lean_ctor_get(v_impl_780_, 4);
                            crate::leanh::lean_inc(v_r_787_);
                            v___x_788_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_789_ = lean_nat_mul(v___x_788_, v_size_782_);
                            v___x_790_ = lean_nat_dec_lt(v___x_789_, v_size_783_);
                            crate::leanh::lean_dec(v___x_789_);
                            if v___x_790_ == 0 {
                                crate::leanh::lean_dec(v_r_787_);
                                crate::leanh::lean_dec(v_l_786_);
                                crate::leanh::lean_dec(v_v_785_);
                                crate::leanh::lean_dec(v_k_784_);
                                v___x_791_ = lean_nat_add(v___x_781_, v_size_782_);
                                v___x_792_ = lean_nat_add(v___x_791_, v_size_783_);
                                crate::leanh::lean_dec(v_size_783_);
                                crate::leanh::lean_dec(v___x_791_);
                                if v_isShared_638_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_637_, 4, v_impl_780_);
                                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_792_);
                                    v___x_794_ = v___x_637_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_795_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_795_,
                                        0,
                                        v___x_792_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_632_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_633_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 3, v_l_634_);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_795_,
                                        4,
                                        v_impl_780_,
                                    );
                                    v___x_794_ = v_reuseFailAlloc_795_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_859_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                if v_isSharedCheck_859_ == 0 {
                                    v_unused_860_ = crate::leanh::lean_ctor_get(v_impl_780_, 4);
                                    crate::leanh::lean_dec(v_unused_860_);
                                    v_unused_861_ = crate::leanh::lean_ctor_get(v_impl_780_, 3);
                                    crate::leanh::lean_dec(v_unused_861_);
                                    v_unused_862_ = crate::leanh::lean_ctor_get(v_impl_780_, 2);
                                    crate::leanh::lean_dec(v_unused_862_);
                                    v_unused_863_ = crate::leanh::lean_ctor_get(v_impl_780_, 1);
                                    crate::leanh::lean_dec(v_unused_863_);
                                    v_unused_864_ = crate::leanh::lean_ctor_get(v_impl_780_, 0);
                                    crate::leanh::lean_dec(v_unused_864_);
                                    v___x_797_ = v_impl_780_;
                                    v_isShared_798_ = v_isSharedCheck_859_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_780_);
                                    v___x_797_ = crate::leanh::lean_box(0);
                                    v_isShared_798_ = v_isSharedCheck_859_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_865_ = crate::leanh::lean_ctor_get(v_impl_780_, 3);
                            crate::leanh::lean_inc(v_l_865_);
                            if crate::leanh::lean_obj_tag(v_l_865_) == 0 {
                                v_r_866_ = crate::leanh::lean_ctor_get(v_impl_780_, 4);
                                v_k_867_ = crate::leanh::lean_ctor_get(v_impl_780_, 1);
                                v_v_868_ = crate::leanh::lean_ctor_get(v_impl_780_, 2);
                                v_isSharedCheck_891_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                if v_isSharedCheck_891_ == 0 {
                                    v_unused_892_ = crate::leanh::lean_ctor_get(v_impl_780_, 3);
                                    crate::leanh::lean_dec(v_unused_892_);
                                    v_unused_893_ = crate::leanh::lean_ctor_get(v_impl_780_, 0);
                                    crate::leanh::lean_dec(v_unused_893_);
                                    v___x_870_ = v_impl_780_;
                                    v_isShared_871_ = v_isSharedCheck_891_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_866_);
                                    crate::leanh::lean_inc(v_v_868_);
                                    crate::leanh::lean_inc(v_k_867_);
                                    crate::leanh::lean_dec(v_impl_780_);
                                    v___x_870_ = crate::leanh::lean_box(0);
                                    v_isShared_871_ = v_isSharedCheck_891_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_894_ = crate::leanh::lean_ctor_get(v_impl_780_, 4);
                                crate::leanh::lean_inc(v_r_894_);
                                if crate::leanh::lean_obj_tag(v_r_894_) == 0 {
                                    v_k_895_ = crate::leanh::lean_ctor_get(v_impl_780_, 1);
                                    v_v_896_ = crate::leanh::lean_ctor_get(v_impl_780_, 2);
                                    v_isSharedCheck_907_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                    if v_isSharedCheck_907_ == 0 {
                                        v_unused_908_ = crate::leanh::lean_ctor_get(v_impl_780_, 4);
                                        crate::leanh::lean_dec(v_unused_908_);
                                        v_unused_909_ = crate::leanh::lean_ctor_get(v_impl_780_, 3);
                                        crate::leanh::lean_dec(v_unused_909_);
                                        v_unused_910_ = crate::leanh::lean_ctor_get(v_impl_780_, 0);
                                        crate::leanh::lean_dec(v_unused_910_);
                                        v___x_898_ = v_impl_780_;
                                        v_isShared_899_ = v_isSharedCheck_907_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_896_);
                                        crate::leanh::lean_inc(v_k_895_);
                                        crate::leanh::lean_dec(v_impl_780_);
                                        v___x_898_ = crate::leanh::lean_box(0);
                                        v_isShared_899_ = v_isSharedCheck_907_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_911_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_638_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_637_, 4, v_impl_780_);
                                        crate::leanh::lean_ctor_set(v___x_637_, 3, v_r_894_);
                                        crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_911_);
                                        v___x_913_ = v___x_637_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_914_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            0,
                                            v___x_911_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            1,
                                            v_k_632_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            2,
                                            v_v_633_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            3,
                                            v_r_894_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            4,
                                            v_impl_780_,
                                        );
                                        v___x_913_ = v_reuseFailAlloc_914_;
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
                return v___x_654_;
            }
            3 => {
                v_size_659_ = crate::leanh::lean_ctor_get(v_l_646_, 0);
                v_size_660_ = crate::leanh::lean_ctor_get(v_r_647_, 0);
                v_k_661_ = crate::leanh::lean_ctor_get(v_r_647_, 1);
                v_v_662_ = crate::leanh::lean_ctor_get(v_r_647_, 2);
                v_l_663_ = crate::leanh::lean_ctor_get(v_r_647_, 3);
                v_r_664_ = crate::leanh::lean_ctor_get(v_r_647_, 4);
                v___x_665_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_666_ = lean_nat_mul(v___x_665_, v_size_659_);
                v___x_667_ = lean_nat_dec_lt(v_size_660_, v___x_666_);
                crate::leanh::lean_dec(v___x_666_);
                if v___x_667_ == 0 {
                    crate::leanh::lean_inc(v_r_664_);
                    crate::leanh::lean_inc(v_l_663_);
                    crate::leanh::lean_inc(v_v_662_);
                    crate::leanh::lean_inc(v_k_661_);
                    v_isSharedCheck_696_ = (!crate::leanh::lean_is_exclusive(v_r_647_)) as u8;
                    if v_isSharedCheck_696_ == 0 {
                        v_unused_697_ = crate::leanh::lean_ctor_get(v_r_647_, 4);
                        crate::leanh::lean_dec(v_unused_697_);
                        v_unused_698_ = crate::leanh::lean_ctor_get(v_r_647_, 3);
                        crate::leanh::lean_dec(v_unused_698_);
                        v_unused_699_ = crate::leanh::lean_ctor_get(v_r_647_, 2);
                        crate::leanh::lean_dec(v_unused_699_);
                        v_unused_700_ = crate::leanh::lean_ctor_get(v_r_647_, 1);
                        crate::leanh::lean_dec(v_unused_700_);
                        v_unused_701_ = crate::leanh::lean_ctor_get(v_r_647_, 0);
                        crate::leanh::lean_dec(v_unused_701_);
                        v___x_669_ = v_r_647_;
                        v_isShared_670_ = v_isSharedCheck_696_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_647_);
                        v___x_669_ = crate::leanh::lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_696_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_637_);
                    v___x_702_ = lean_nat_add(v___x_641_, v_size_643_);
                    crate::leanh::lean_dec(v_size_643_);
                    v___x_703_ = lean_nat_add(v___x_702_, v_size_642_);
                    crate::leanh::lean_dec(v___x_702_);
                    v___x_704_ = lean_nat_add(v___x_641_, v_size_642_);
                    v___x_705_ = lean_nat_add(v___x_704_, v_size_660_);
                    crate::leanh::lean_dec(v___x_704_);
                    crate::leanh::lean_inc_ref(v_r_635_);
                    if v_isShared_658_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_657_, 4, v_r_635_);
                        crate::leanh::lean_ctor_set(v___x_657_, 3, v_r_647_);
                        crate::leanh::lean_ctor_set(v___x_657_, 2, v_v_633_);
                        crate::leanh::lean_ctor_set(v___x_657_, 1, v_k_632_);
                        crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_705_);
                        v___x_707_ = v___x_657_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_720_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_705_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_632_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 3, v_r_647_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 4, v_r_635_);
                        v___x_707_ = v_reuseFailAlloc_720_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_671_ = lean_nat_add(v___x_641_, v_size_643_);
                crate::leanh::lean_dec(v_size_643_);
                v___x_672_ = lean_nat_add(v___x_671_, v_size_642_);
                crate::leanh::lean_dec(v___x_671_);
                v___x_684_ = lean_nat_add(v___x_641_, v_size_659_);
                if crate::leanh::lean_obj_tag(v_l_663_) == 0 {
                    v_size_694_ = crate::leanh::lean_ctor_get(v_l_663_, 0);
                    crate::leanh::lean_inc(v_size_694_);
                    v___y_686_ = v_size_694_;
                    state = 8;
                    continue;
                } else {
                    v___x_695_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_686_ = v___x_695_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_677_ = lean_nat_add(v___y_675_, v___y_676_);
                crate::leanh::lean_dec(v___y_676_);
                crate::leanh::lean_dec(v___y_675_);
                if v_isShared_670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_669_, 4, v_r_635_);
                    crate::leanh::lean_ctor_set(v___x_669_, 3, v_r_664_);
                    crate::leanh::lean_ctor_set(v___x_669_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v___x_669_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v___x_669_, 0, v___x_677_);
                    v___x_679_ = v___x_669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 3, v_r_664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 4, v_r_635_);
                    v___x_679_ = v_reuseFailAlloc_683_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_657_, 4, v___x_679_);
                    crate::leanh::lean_ctor_set(v___x_657_, 3, v___y_674_);
                    crate::leanh::lean_ctor_set(v___x_657_, 2, v_v_662_);
                    crate::leanh::lean_ctor_set(v___x_657_, 1, v_k_661_);
                    crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_672_);
                    v___x_681_ = v___x_657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 3, v___y_674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 4, v___x_679_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_681_;
            }
            8 => {
                v___x_687_ = lean_nat_add(v___x_684_, v___y_686_);
                crate::leanh::lean_dec(v___y_686_);
                crate::leanh::lean_dec(v___x_684_);
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v_l_663_);
                    crate::leanh::lean_ctor_set(v___x_637_, 3, v_l_646_);
                    crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_645_);
                    crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_644_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_687_);
                    v___x_689_ = v___x_637_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 3, v_l_646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 4, v_l_663_);
                    v___x_689_ = v_reuseFailAlloc_693_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_690_ = lean_nat_add(v___x_641_, v_size_642_);
                if crate::leanh::lean_obj_tag(v_r_664_) == 0 {
                    v_size_691_ = crate::leanh::lean_ctor_get(v_r_664_, 0);
                    crate::leanh::lean_inc(v_size_691_);
                    v___y_674_ = v___x_689_;
                    v___y_675_ = v___x_690_;
                    v___y_676_ = v_size_691_;
                    state = 5;
                    continue;
                } else {
                    v___x_692_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_674_ = v___x_689_;
                    v___y_675_ = v___x_690_;
                    v___y_676_ = v___x_692_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_714_ = (!crate::leanh::lean_is_exclusive(v_r_635_)) as u8;
                if v_isSharedCheck_714_ == 0 {
                    v_unused_715_ = crate::leanh::lean_ctor_get(v_r_635_, 4);
                    crate::leanh::lean_dec(v_unused_715_);
                    v_unused_716_ = crate::leanh::lean_ctor_get(v_r_635_, 3);
                    crate::leanh::lean_dec(v_unused_716_);
                    v_unused_717_ = crate::leanh::lean_ctor_get(v_r_635_, 2);
                    crate::leanh::lean_dec(v_unused_717_);
                    v_unused_718_ = crate::leanh::lean_ctor_get(v_r_635_, 1);
                    crate::leanh::lean_dec(v_unused_718_);
                    v_unused_719_ = crate::leanh::lean_ctor_get(v_r_635_, 0);
                    crate::leanh::lean_dec(v_unused_719_);
                    v___x_709_ = v_r_635_;
                    v_isShared_710_ = v_isSharedCheck_714_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_635_);
                    v___x_709_ = crate::leanh::lean_box(0);
                    v_isShared_710_ = v_isSharedCheck_714_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_710_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_709_, 4, v___x_707_);
                    crate::leanh::lean_ctor_set(v___x_709_, 3, v_l_646_);
                    crate::leanh::lean_ctor_set(v___x_709_, 2, v_v_645_);
                    crate::leanh::lean_ctor_set(v___x_709_, 1, v_k_644_);
                    crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_703_);
                    v___x_712_ = v___x_709_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_713_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_713_, 1, v_k_644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_713_, 2, v_v_645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_713_, 3, v_l_646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_713_, 4, v___x_707_);
                    v___x_712_ = v_reuseFailAlloc_713_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_712_;
            }
            13 => {
                v___x_734_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_728_);
                if v_isShared_733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_732_, 3, v_r_728_);
                    crate::leanh::lean_ctor_set(v___x_732_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v___x_732_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_641_);
                    v___x_736_ = v___x_732_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 3, v_r_728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 4, v_r_728_);
                    v___x_736_ = v_reuseFailAlloc_740_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v___x_736_);
                    crate::leanh::lean_ctor_set(v___x_637_, 3, v_l_727_);
                    crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_730_);
                    crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_729_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_734_);
                    v___x_738_ = v___x_637_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 3, v_l_727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_736_);
                    v___x_738_ = v_reuseFailAlloc_739_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_738_;
            }
            16 => {
                v_k_750_ = crate::leanh::lean_ctor_get(v_r_744_, 1);
                v_v_751_ = crate::leanh::lean_ctor_get(v_r_744_, 2);
                v_isSharedCheck_765_ = (!crate::leanh::lean_is_exclusive(v_r_744_)) as u8;
                if v_isSharedCheck_765_ == 0 {
                    v_unused_766_ = crate::leanh::lean_ctor_get(v_r_744_, 4);
                    crate::leanh::lean_dec(v_unused_766_);
                    v_unused_767_ = crate::leanh::lean_ctor_get(v_r_744_, 3);
                    crate::leanh::lean_dec(v_unused_767_);
                    v_unused_768_ = crate::leanh::lean_ctor_get(v_r_744_, 0);
                    crate::leanh::lean_dec(v_unused_768_);
                    v___x_753_ = v_r_744_;
                    v_isShared_754_ = v_isSharedCheck_765_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_751_);
                    crate::leanh::lean_inc(v_k_750_);
                    crate::leanh::lean_dec(v_r_744_);
                    v___x_753_ = crate::leanh::lean_box(0);
                    v_isShared_754_ = v_isSharedCheck_765_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_755_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_753_, 4, v_l_727_);
                    crate::leanh::lean_ctor_set(v___x_753_, 3, v_l_727_);
                    crate::leanh::lean_ctor_set(v___x_753_, 2, v_v_746_);
                    crate::leanh::lean_ctor_set(v___x_753_, 1, v_k_745_);
                    crate::leanh::lean_ctor_set(v___x_753_, 0, v___x_641_);
                    v___x_757_ = v___x_753_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 3, v_l_727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 4, v_l_727_);
                    v___x_757_ = v_reuseFailAlloc_764_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_748_, 4, v_l_727_);
                    crate::leanh::lean_ctor_set(v___x_748_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v___x_748_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v___x_748_, 0, v___x_641_);
                    v___x_759_ = v___x_748_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_763_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 3, v_l_727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 4, v_l_727_);
                    v___x_759_ = v_reuseFailAlloc_763_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v___x_759_);
                    crate::leanh::lean_ctor_set(v___x_637_, 3, v___x_757_);
                    crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_751_);
                    crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_750_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_755_);
                    v___x_761_ = v___x_637_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_762_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 3, v___x_757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_759_);
                    v___x_761_ = v_reuseFailAlloc_762_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_761_;
            }
            21 => {
                return v___x_775_;
            }
            22 => {
                return v___x_778_;
            }
            23 => {
                return v___x_794_;
            }
            24 => {
                v_size_799_ = crate::leanh::lean_ctor_get(v_l_786_, 0);
                v_k_800_ = crate::leanh::lean_ctor_get(v_l_786_, 1);
                v_v_801_ = crate::leanh::lean_ctor_get(v_l_786_, 2);
                v_l_802_ = crate::leanh::lean_ctor_get(v_l_786_, 3);
                v_r_803_ = crate::leanh::lean_ctor_get(v_l_786_, 4);
                v_size_804_ = crate::leanh::lean_ctor_get(v_r_787_, 0);
                v___x_805_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_806_ = lean_nat_mul(v___x_805_, v_size_804_);
                v___x_807_ = lean_nat_dec_lt(v_size_799_, v___x_806_);
                crate::leanh::lean_dec(v___x_806_);
                if v___x_807_ == 0 {
                    crate::leanh::lean_inc(v_r_803_);
                    crate::leanh::lean_inc(v_l_802_);
                    crate::leanh::lean_inc(v_v_801_);
                    crate::leanh::lean_inc(v_k_800_);
                    v_isSharedCheck_835_ = (!crate::leanh::lean_is_exclusive(v_l_786_)) as u8;
                    if v_isSharedCheck_835_ == 0 {
                        v_unused_836_ = crate::leanh::lean_ctor_get(v_l_786_, 4);
                        crate::leanh::lean_dec(v_unused_836_);
                        v_unused_837_ = crate::leanh::lean_ctor_get(v_l_786_, 3);
                        crate::leanh::lean_dec(v_unused_837_);
                        v_unused_838_ = crate::leanh::lean_ctor_get(v_l_786_, 2);
                        crate::leanh::lean_dec(v_unused_838_);
                        v_unused_839_ = crate::leanh::lean_ctor_get(v_l_786_, 1);
                        crate::leanh::lean_dec(v_unused_839_);
                        v_unused_840_ = crate::leanh::lean_ctor_get(v_l_786_, 0);
                        crate::leanh::lean_dec(v_unused_840_);
                        v___x_809_ = v_l_786_;
                        v_isShared_810_ = v_isSharedCheck_835_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_786_);
                        v___x_809_ = crate::leanh::lean_box(0);
                        v_isShared_810_ = v_isSharedCheck_835_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_637_);
                    v___x_841_ = lean_nat_add(v___x_781_, v_size_782_);
                    v___x_842_ = lean_nat_add(v___x_841_, v_size_783_);
                    crate::leanh::lean_dec(v_size_783_);
                    v___x_843_ = lean_nat_add(v___x_841_, v_size_799_);
                    crate::leanh::lean_dec(v___x_841_);
                    crate::leanh::lean_inc_ref(v_l_634_);
                    if v_isShared_798_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_797_, 4, v_l_786_);
                        crate::leanh::lean_ctor_set(v___x_797_, 3, v_l_634_);
                        crate::leanh::lean_ctor_set(v___x_797_, 2, v_v_633_);
                        crate::leanh::lean_ctor_set(v___x_797_, 1, v_k_632_);
                        crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_843_);
                        v___x_845_ = v___x_797_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_858_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_843_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_632_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 4, v_l_786_);
                        v___x_845_ = v_reuseFailAlloc_858_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_811_ = lean_nat_add(v___x_781_, v_size_782_);
                v___x_812_ = lean_nat_add(v___x_811_, v_size_783_);
                crate::leanh::lean_dec(v_size_783_);
                if crate::leanh::lean_obj_tag(v_l_802_) == 0 {
                    v_size_833_ = crate::leanh::lean_ctor_get(v_l_802_, 0);
                    crate::leanh::lean_inc(v_size_833_);
                    v___y_825_ = v_size_833_;
                    state = 29;
                    continue;
                } else {
                    v___x_834_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_825_ = v___x_834_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_817_ = lean_nat_add(v___y_814_, v___y_816_);
                crate::leanh::lean_dec(v___y_816_);
                crate::leanh::lean_dec(v___y_814_);
                if v_isShared_810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_809_, 4, v_r_787_);
                    crate::leanh::lean_ctor_set(v___x_809_, 3, v_r_803_);
                    crate::leanh::lean_ctor_set(v___x_809_, 2, v_v_785_);
                    crate::leanh::lean_ctor_set(v___x_809_, 1, v_k_784_);
                    crate::leanh::lean_ctor_set(v___x_809_, 0, v___x_817_);
                    v___x_819_ = v___x_809_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 3, v_r_803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 4, v_r_787_);
                    v___x_819_ = v_reuseFailAlloc_823_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_797_, 4, v___x_819_);
                    crate::leanh::lean_ctor_set(v___x_797_, 3, v___y_815_);
                    crate::leanh::lean_ctor_set(v___x_797_, 2, v_v_801_);
                    crate::leanh::lean_ctor_set(v___x_797_, 1, v_k_800_);
                    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_812_);
                    v___x_821_ = v___x_797_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 3, v___y_815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 4, v___x_819_);
                    v___x_821_ = v_reuseFailAlloc_822_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_821_;
            }
            29 => {
                v___x_826_ = lean_nat_add(v___x_811_, v___y_825_);
                crate::leanh::lean_dec(v___y_825_);
                crate::leanh::lean_dec(v___x_811_);
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v_l_802_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_826_);
                    v___x_828_ = v___x_637_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 3, v_l_634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 4, v_l_802_);
                    v___x_828_ = v_reuseFailAlloc_832_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_829_ = lean_nat_add(v___x_781_, v_size_804_);
                if crate::leanh::lean_obj_tag(v_r_803_) == 0 {
                    v_size_830_ = crate::leanh::lean_ctor_get(v_r_803_, 0);
                    crate::leanh::lean_inc(v_size_830_);
                    v___y_814_ = v___x_829_;
                    v___y_815_ = v___x_828_;
                    v___y_816_ = v_size_830_;
                    state = 26;
                    continue;
                } else {
                    v___x_831_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_814_ = v___x_829_;
                    v___y_815_ = v___x_828_;
                    v___y_816_ = v___x_831_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_852_ = (!crate::leanh::lean_is_exclusive(v_l_634_)) as u8;
                if v_isSharedCheck_852_ == 0 {
                    v_unused_853_ = crate::leanh::lean_ctor_get(v_l_634_, 4);
                    crate::leanh::lean_dec(v_unused_853_);
                    v_unused_854_ = crate::leanh::lean_ctor_get(v_l_634_, 3);
                    crate::leanh::lean_dec(v_unused_854_);
                    v_unused_855_ = crate::leanh::lean_ctor_get(v_l_634_, 2);
                    crate::leanh::lean_dec(v_unused_855_);
                    v_unused_856_ = crate::leanh::lean_ctor_get(v_l_634_, 1);
                    crate::leanh::lean_dec(v_unused_856_);
                    v_unused_857_ = crate::leanh::lean_ctor_get(v_l_634_, 0);
                    crate::leanh::lean_dec(v_unused_857_);
                    v___x_847_ = v_l_634_;
                    v_isShared_848_ = v_isSharedCheck_852_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_634_);
                    v___x_847_ = crate::leanh::lean_box(0);
                    v_isShared_848_ = v_isSharedCheck_852_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_847_, 4, v_r_787_);
                    crate::leanh::lean_ctor_set(v___x_847_, 3, v___x_845_);
                    crate::leanh::lean_ctor_set(v___x_847_, 2, v_v_785_);
                    crate::leanh::lean_ctor_set(v___x_847_, 1, v_k_784_);
                    crate::leanh::lean_ctor_set(v___x_847_, 0, v___x_842_);
                    v___x_850_ = v___x_847_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_851_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 3, v___x_845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 4, v_r_787_);
                    v___x_850_ = v_reuseFailAlloc_851_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_850_;
            }
            34 => {
                v_k_872_ = crate::leanh::lean_ctor_get(v_l_865_, 1);
                v_v_873_ = crate::leanh::lean_ctor_get(v_l_865_, 2);
                v_isSharedCheck_887_ = (!crate::leanh::lean_is_exclusive(v_l_865_)) as u8;
                if v_isSharedCheck_887_ == 0 {
                    v_unused_888_ = crate::leanh::lean_ctor_get(v_l_865_, 4);
                    crate::leanh::lean_dec(v_unused_888_);
                    v_unused_889_ = crate::leanh::lean_ctor_get(v_l_865_, 3);
                    crate::leanh::lean_dec(v_unused_889_);
                    v_unused_890_ = crate::leanh::lean_ctor_get(v_l_865_, 0);
                    crate::leanh::lean_dec(v_unused_890_);
                    v___x_875_ = v_l_865_;
                    v_isShared_876_ = v_isSharedCheck_887_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_873_);
                    crate::leanh::lean_inc(v_k_872_);
                    crate::leanh::lean_dec(v_l_865_);
                    v___x_875_ = crate::leanh::lean_box(0);
                    v_isShared_876_ = v_isSharedCheck_887_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_877_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_866_, 2);
                if v_isShared_876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_875_, 4, v_r_866_);
                    crate::leanh::lean_ctor_set(v___x_875_, 3, v_r_866_);
                    crate::leanh::lean_ctor_set(v___x_875_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v___x_875_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_781_);
                    v___x_879_ = v___x_875_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_886_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 3, v_r_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 4, v_r_866_);
                    v___x_879_ = v_reuseFailAlloc_886_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_866_);
                if v_isShared_871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_870_, 3, v_r_866_);
                    crate::leanh::lean_ctor_set(v___x_870_, 0, v___x_781_);
                    v___x_881_ = v___x_870_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 3, v_r_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 4, v_r_866_);
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v___x_881_);
                    crate::leanh::lean_ctor_set(v___x_637_, 3, v___x_879_);
                    crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_873_);
                    crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_872_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_877_);
                    v___x_883_ = v___x_637_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 1, v_k_872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 2, v_v_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 3, v___x_879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 4, v___x_881_);
                    v___x_883_ = v_reuseFailAlloc_884_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_883_;
            }
            39 => {
                v___x_900_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_898_, 4, v_l_865_);
                    crate::leanh::lean_ctor_set(v___x_898_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v___x_898_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v___x_898_, 0, v___x_781_);
                    v___x_902_ = v___x_898_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_906_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 3, v_l_865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 4, v_l_865_);
                    v___x_902_ = v_reuseFailAlloc_906_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 4, v_r_894_);
                    crate::leanh::lean_ctor_set(v___x_637_, 3, v___x_902_);
                    crate::leanh::lean_ctor_set(v___x_637_, 2, v_v_896_);
                    crate::leanh::lean_ctor_set(v___x_637_, 1, v_k_895_);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_900_);
                    v___x_904_ = v___x_637_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 3, v___x_902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_894_);
                    v___x_904_ = v_reuseFailAlloc_905_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_904_;
            }
            42 => {
                return v___x_913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_loadWorkspaceRoot(
    mut v_config_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lakeEnv_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsDir_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgName_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relPkgDir_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configLang_x3f_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_935_: u8 = 0;
    let mut v_updateDeps_936_: u8 = 0;
    let mut v_updateToolchain_937_: u8 = 0;
    let mut v_scope_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v_facetDecls_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: usize = 0;
    let mut v___x_984_: usize = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut v_a_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_a_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_unused_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_922_ = crate::leanh::lean_ctor_get(v_config_919_, 0);
                v_lakeArgs_x3f_923_ = crate::leanh::lean_ctor_get(v_config_919_, 1);
                v_wsDir_924_ = crate::leanh::lean_ctor_get(v_config_919_, 2);
                v_pkgName_925_ = crate::leanh::lean_ctor_get(v_config_919_, 4);
                v_relPkgDir_926_ = crate::leanh::lean_ctor_get(v_config_919_, 5);
                v_pkgDir_927_ = crate::leanh::lean_ctor_get(v_config_919_, 6);
                v_relConfigFile_928_ = crate::leanh::lean_ctor_get(v_config_919_, 7);
                v_configFile_929_ = crate::leanh::lean_ctor_get(v_config_919_, 8);
                v_configLang_x3f_930_ = crate::leanh::lean_ctor_get(v_config_919_, 9);
                v_relManifestFile_931_ = crate::leanh::lean_ctor_get(v_config_919_, 10);
                v_packageOverrides_932_ = crate::leanh::lean_ctor_get(v_config_919_, 11);
                v_lakeOpts_933_ = crate::leanh::lean_ctor_get(v_config_919_, 12);
                v_leanOpts_934_ = crate::leanh::lean_ctor_get(v_config_919_, 13);
                v_reconfigure_935_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                );
                v_updateDeps_936_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                );
                v_updateToolchain_937_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                );
                v_scope_938_ = crate::leanh::lean_ctor_get(v_config_919_, 14);
                v_remoteUrl_939_ = crate::leanh::lean_ctor_get(v_config_919_, 15);
                v_isSharedCheck_1018_ = (!crate::leanh::lean_is_exclusive(v_config_919_)) as u8;
                if v_isSharedCheck_1018_ == 0 {
                    v_unused_1019_ = crate::leanh::lean_ctor_get(v_config_919_, 3);
                    crate::leanh::lean_dec(v_unused_1019_);
                    v___x_941_ = v_config_919_;
                    v_isShared_942_ = v_isSharedCheck_1018_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_remoteUrl_939_);
                    crate::leanh::lean_inc(v_scope_938_);
                    crate::leanh::lean_inc(v_leanOpts_934_);
                    crate::leanh::lean_inc(v_lakeOpts_933_);
                    crate::leanh::lean_inc(v_packageOverrides_932_);
                    crate::leanh::lean_inc(v_relManifestFile_931_);
                    crate::leanh::lean_inc(v_configLang_x3f_930_);
                    crate::leanh::lean_inc(v_configFile_929_);
                    crate::leanh::lean_inc(v_relConfigFile_928_);
                    crate::leanh::lean_inc(v_pkgDir_927_);
                    crate::leanh::lean_inc(v_relPkgDir_926_);
                    crate::leanh::lean_inc(v_pkgName_925_);
                    crate::leanh::lean_inc(v_wsDir_924_);
                    crate::leanh::lean_inc(v_lakeArgs_x3f_923_);
                    crate::leanh::lean_inc(v_lakeEnv_922_);
                    crate::leanh::lean_dec(v_config_919_);
                    v___x_941_ = crate::leanh::lean_box(0);
                    v_isShared_942_ = v_isSharedCheck_1018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_943_ = l_Lean_searchPathRef;
                v___x_944_ = l_Lake_Env_leanSearchPath(v_lakeEnv_922_);
                v___x_945_ = lean_st_ref_set(v___x_943_, v___x_944_);
                crate::leanh::lean_inc_ref(v_lakeEnv_922_);
                v___x_946_ = l_Lake_loadLakeConfig(v_lakeEnv_922_, v_a_920_);
                if crate::leanh::lean_obj_tag(v___x_946_) == 0 {
                    v_a_947_ = crate::leanh::lean_ctor_get(v___x_946_, 0);
                    crate::leanh::lean_inc(v_a_947_);
                    v_a_948_ = crate::leanh::lean_ctor_get(v___x_946_, 1);
                    crate::leanh::lean_inc(v_a_948_);
                    crate::leanh::lean_dec_ref_known(v___x_946_, 2);
                    v___x_949_ = crate::leanh::lean_unsigned_to_nat(0);
                    if v_isShared_942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_941_, 3, v___x_949_);
                        v___x_951_ = v___x_941_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_lakeEnv_922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_lakeArgs_x3f_923_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_wsDir_924_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 3, v___x_949_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_pkgName_925_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 5, v_relPkgDir_926_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 6, v_pkgDir_927_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            7,
                            v_relConfigFile_928_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 8, v_configFile_929_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            9,
                            v_configLang_x3f_930_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            10,
                            v_relManifestFile_931_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            11,
                            v_packageOverrides_932_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 12, v_lakeOpts_933_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 13, v_leanOpts_934_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 14, v_scope_938_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 15, v_remoteUrl_939_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                            v_reconfigure_935_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                            v_updateDeps_936_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                            v_updateToolchain_937_,
                        );
                        v___x_951_ = v_reuseFailAlloc_1008_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_941_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_939_);
                    crate::leanh::lean_dec_ref(v_scope_938_);
                    crate::leanh::lean_dec_ref(v_leanOpts_934_);
                    crate::leanh::lean_dec(v_lakeOpts_933_);
                    crate::leanh::lean_dec_ref(v_packageOverrides_932_);
                    crate::leanh::lean_dec_ref(v_relManifestFile_931_);
                    crate::leanh::lean_dec(v_configLang_x3f_930_);
                    crate::leanh::lean_dec_ref(v_configFile_929_);
                    crate::leanh::lean_dec_ref(v_relConfigFile_928_);
                    crate::leanh::lean_dec_ref(v_pkgDir_927_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_926_);
                    crate::leanh::lean_dec(v_pkgName_925_);
                    crate::leanh::lean_dec_ref(v_wsDir_924_);
                    crate::leanh::lean_dec(v_lakeArgs_x3f_923_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_922_);
                    v_a_1009_ = crate::leanh::lean_ctor_get(v___x_946_, 0);
                    v_a_1010_ = crate::leanh::lean_ctor_get(v___x_946_, 1);
                    v_isSharedCheck_1017_ = (!crate::leanh::lean_is_exclusive(v___x_946_)) as u8;
                    if v_isSharedCheck_1017_ == 0 {
                        v___x_1012_ = v___x_946_;
                        v_isShared_1013_ = v_isSharedCheck_1017_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1010_);
                        crate::leanh::lean_inc(v_a_1009_);
                        crate::leanh::lean_dec(v___x_946_);
                        v___x_1012_ = crate::leanh::lean_box(0);
                        v_isShared_1013_ = v_isSharedCheck_1017_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_952_ = l_Lake_loadWorkspaceRoot___closed__0;
                v___x_953_ = l_Lake_resolveConfigFile(v___x_952_, v___x_951_, v_a_948_);
                if crate::leanh::lean_obj_tag(v___x_953_) == 0 {
                    v_a_954_ = crate::leanh::lean_ctor_get(v___x_953_, 0);
                    crate::leanh::lean_inc_n(v_a_954_, 2);
                    v_a_955_ = crate::leanh::lean_ctor_get(v___x_953_, 1);
                    crate::leanh::lean_inc(v_a_955_);
                    crate::leanh::lean_dec_ref_known(v___x_953_, 2);
                    v___x_956_ = l_Lake_loadConfigFile___redArg(v_a_954_, v_a_955_);
                    if crate::leanh::lean_obj_tag(v___x_956_) == 0 {
                        v_a_957_ = crate::leanh::lean_ctor_get(v___x_956_, 0);
                        v_a_958_ = crate::leanh::lean_ctor_get(v___x_956_, 1);
                        v_isSharedCheck_989_ = (!crate::leanh::lean_is_exclusive(v___x_956_)) as u8;
                        if v_isSharedCheck_989_ == 0 {
                            v___x_960_ = v___x_956_;
                            v_isShared_961_ = v_isSharedCheck_989_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_958_);
                            crate::leanh::lean_inc(v_a_957_);
                            crate::leanh::lean_dec(v___x_956_);
                            v___x_960_ = crate::leanh::lean_box(0);
                            v_isShared_961_ = v_isSharedCheck_989_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_954_);
                        crate::leanh::lean_dec(v_a_947_);
                        v_a_990_ = crate::leanh::lean_ctor_get(v___x_956_, 0);
                        v_a_991_ = crate::leanh::lean_ctor_get(v___x_956_, 1);
                        v_isSharedCheck_998_ = (!crate::leanh::lean_is_exclusive(v___x_956_)) as u8;
                        if v_isSharedCheck_998_ == 0 {
                            v___x_993_ = v___x_956_;
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_991_);
                            crate::leanh::lean_inc(v_a_990_);
                            crate::leanh::lean_dec(v___x_956_);
                            v___x_993_ = crate::leanh::lean_box(0);
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_947_);
                    v_a_999_ = crate::leanh::lean_ctor_get(v___x_953_, 0);
                    v_a_1000_ = crate::leanh::lean_ctor_get(v___x_953_, 1);
                    v_isSharedCheck_1007_ = (!crate::leanh::lean_is_exclusive(v___x_953_)) as u8;
                    if v_isSharedCheck_1007_ == 0 {
                        v___x_1002_ = v___x_953_;
                        v_isShared_1003_ = v_isSharedCheck_1007_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1000_);
                        crate::leanh::lean_inc(v_a_999_);
                        crate::leanh::lean_dec(v___x_953_);
                        v___x_1002_ = crate::leanh::lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1007_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_facetDecls_962_ = crate::leanh::lean_ctor_get(v_a_957_, 2);
                crate::leanh::lean_inc_ref(v_facetDecls_962_);
                v___x_963_ = l_Lake_mkPackage(v_a_954_, v_a_957_, v___x_949_);
                v___x_979_ = l_Lake_initFacetConfigs;
                v___x_980_ = lean_array_get_size(v_facetDecls_962_);
                v___x_981_ = lean_nat_dec_lt(v___x_949_, v___x_980_);
                if v___x_981_ == 0 {
                    crate::leanh::lean_dec_ref(v_facetDecls_962_);
                    v___y_965_ = v___x_979_;
                    state = 4;
                    continue;
                } else {
                    v___x_982_ = lean_nat_dec_le(v___x_980_, v___x_980_);
                    if v___x_982_ == 0 {
                        if v___x_981_ == 0 {
                            crate::leanh::lean_dec_ref(v_facetDecls_962_);
                            v___y_965_ = v___x_979_;
                            state = 4;
                            continue;
                        } else {
                            v___x_983_ = 0usize;
                            v___x_984_ = lean_usize_of_nat(v___x_980_);
                            v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_962_, v___x_983_, v___x_984_, v___x_979_);
                            crate::leanh::lean_dec_ref(v_facetDecls_962_);
                            v___y_965_ = v___x_985_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_986_ = 0usize;
                        v___x_987_ = lean_usize_of_nat(v___x_980_);
                        v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_962_, v___x_986_, v___x_987_, v___x_979_);
                        crate::leanh::lean_dec_ref(v_facetDecls_962_);
                        v___y_965_ = v___x_988_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v_lakeEnv_966_ = crate::leanh::lean_ctor_get(v_a_954_, 0);
                crate::leanh::lean_inc_ref(v_lakeEnv_966_);
                v_lakeArgs_x3f_967_ = crate::leanh::lean_ctor_get(v_a_954_, 1);
                crate::leanh::lean_inc(v_lakeArgs_x3f_967_);
                crate::leanh::lean_dec(v_a_954_);
                v_keyName_968_ = crate::leanh::lean_ctor_get(v___x_963_, 2);
                crate::leanh::lean_inc(v_keyName_968_);
                crate::leanh::lean_inc_ref_n(v___x_963_, 2);
                v___x_969_ = l_Lake_computeLakeCache(v___x_963_, v_lakeEnv_966_);
                v___x_970_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
                v___x_972_ = lean_array_push(v___x_971_, v___x_963_);
                v___x_973_ = crate::leanh::lean_box(1);
                v___x_974_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_keyName_968_, v___x_963_, v___x_973_);
                v___x_975_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_975_, 0, v_lakeEnv_966_);
                crate::leanh::lean_ctor_set(v___x_975_, 1, v_a_947_);
                crate::leanh::lean_ctor_set(v___x_975_, 2, v___x_969_);
                crate::leanh::lean_ctor_set(v___x_975_, 3, v_lakeArgs_x3f_967_);
                crate::leanh::lean_ctor_set(v___x_975_, 4, v___x_972_);
                crate::leanh::lean_ctor_set(v___x_975_, 5, v___x_974_);
                crate::leanh::lean_ctor_set(v___x_975_, 6, v___y_965_);
                if v_isShared_961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_960_, 0, v___x_975_);
                    v___x_977_ = v___x_960_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_958_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_977_;
            }
            6 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_996_;
            }
            8 => {
                if v_isShared_1003_ == 0 {
                    v___x_1005_ = v___x_1002_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_a_1000_);
                    v___x_1005_ = v_reuseFailAlloc_1006_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1005_;
            }
            10 => {
                if v_isShared_1013_ == 0 {
                    v___x_1015_ = v___x_1012_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1010_);
                    v___x_1015_ = v_reuseFailAlloc_1016_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_loadWorkspaceRoot___boxed(
    mut v_config_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Lake_loadWorkspaceRoot(v_config_1020_, v_a_1021_);
    return v_res_1023_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0(
    mut v_00_u03b2_1024_: *mut crate::leanh::LeanObject,
    mut v_k_1025_: *mut crate::leanh::LeanObject,
    mut v_v_1026_: *mut crate::leanh::LeanObject,
    mut v_t_1027_: *mut crate::leanh::LeanObject,
    mut v_hl_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(
            v_k_1025_, v_v_1026_, v_t_1027_,
        );
    return v___x_1029_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(
    mut v_as_1030_: *mut crate::leanh::LeanObject,
    mut v_i_1031_: usize,
    mut v_stop_1032_: usize,
    mut v_b_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: usize = 0;
    let mut v___x_1040_: usize = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
                if v___x_1036_ == 0 {
                    v___x_1037_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
                    crate::leanh::lean_inc_ref(v___y_1034_);
                    crate::leanh::lean_inc(v___x_1037_);
                    v___x_1038_ = crate::leanh::lean_apply_2(
                        v___y_1034_,
                        v___x_1037_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_1039_ = 1usize;
                    v___x_1040_ = lean_usize_add(v_i_1031_, v___x_1039_);
                    v_i_1031_ = v___x_1040_;
                    v_b_1033_ = v___x_1038_;
                    state = 0;
                    continue;
                } else {
                    v___x_1042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1042_, 0, v_b_1033_);
                    return v___x_1042_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(
    mut v_as_1043_: *mut crate::leanh::LeanObject,
    mut v_i_1044_: *mut crate::leanh::LeanObject,
    mut v_stop_1045_: *mut crate::leanh::LeanObject,
    mut v_b_1046_: *mut crate::leanh::LeanObject,
    mut v___y_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1049_: usize = 0;
    let mut v_stop_boxed_1050_: usize = 0;
    let mut v_res_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1049_ = crate::leanh::lean_unbox_usize(v_i_1044_);
    crate::leanh::lean_dec(v_i_1044_);
    v_stop_boxed_1050_ = crate::leanh::lean_unbox_usize(v_stop_1045_);
    crate::leanh::lean_dec(v_stop_1045_);
    v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_1043_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1046_, v___y_1047_);
    crate::leanh::lean_dec_ref(v___y_1047_);
    crate::leanh::lean_dec_ref(v_as_1043_);
    return v_res_1051_;
}
pub unsafe fn l_Lake_loadWorkspace(
    mut v_config_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_1062_: u8 = 0;
    let mut v_updateDeps_1063_: u8 = 0;
    let mut v_updateToolchain_1064_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: usize = 0;
    let mut v___x_1102_: usize = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v___x_1112_: usize = 0;
    let mut v___x_1113_: usize = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1118_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_a_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: usize = 0;
    let mut v___x_1131_: usize = 0;
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1136_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_packageOverrides_1060_ = crate::leanh::lean_ctor_get(v_config_1054_, 11);
                crate::leanh::lean_inc_ref(v_packageOverrides_1060_);
                v_leanOpts_1061_ = crate::leanh::lean_ctor_get(v_config_1054_, 13);
                crate::leanh::lean_inc_ref(v_leanOpts_1061_);
                v_reconfigure_1062_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                );
                v_updateDeps_1063_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                );
                v_updateToolchain_1064_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                );
                v___x_1065_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1066_ = l_Lake_loadWorkspace___closed__0;
                v___x_1067_ = l_Lake_loadWorkspaceRoot(v_config_1054_, v___x_1066_);
                if crate::leanh::lean_obj_tag(v___x_1067_) == 0 {
                    v_a_1068_ = crate::leanh::lean_ctor_get(v___x_1067_, 0);
                    crate::leanh::lean_inc(v_a_1068_);
                    v_a_1069_ = crate::leanh::lean_ctor_get(v___x_1067_, 1);
                    crate::leanh::lean_inc(v_a_1069_);
                    crate::leanh::lean_dec_ref_known(v___x_1067_, 2);
                    v___x_1097_ = lean_array_get_size(v_a_1069_);
                    v___x_1098_ = lean_nat_dec_lt(v___x_1065_, v___x_1097_);
                    if v___x_1098_ == 0 {
                        crate::leanh::lean_dec(v_a_1069_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1099_ = crate::leanh::lean_box(0);
                        v___x_1100_ = lean_nat_dec_le(v___x_1097_, v___x_1097_);
                        if v___x_1100_ == 0 {
                            if v___x_1098_ == 0 {
                                crate::leanh::lean_dec(v_a_1069_);
                                state = 2;
                                continue;
                            } else {
                                v___x_1101_ = 0usize;
                                v___x_1102_ = lean_usize_of_nat(v___x_1097_);
                                v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1069_, v___x_1101_, v___x_1102_, v___x_1099_, v_a_1055_);
                                crate::leanh::lean_dec(v_a_1069_);
                                if crate::leanh::lean_obj_tag(v___x_1103_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1103_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1068_);
                                    crate::leanh::lean_dec_ref(v_leanOpts_1061_);
                                    crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                                    v_a_1104_ = crate::leanh::lean_ctor_get(v___x_1103_, 0);
                                    v_isSharedCheck_1111_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1103_)) as u8;
                                    if v_isSharedCheck_1111_ == 0 {
                                        v___x_1106_ = v___x_1103_;
                                        v_isShared_1107_ = v_isSharedCheck_1111_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1104_);
                                        crate::leanh::lean_dec(v___x_1103_);
                                        v___x_1106_ = crate::leanh::lean_box(0);
                                        v_isShared_1107_ = v_isSharedCheck_1111_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_1112_ = 0usize;
                            v___x_1113_ = lean_usize_of_nat(v___x_1097_);
                            v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1069_, v___x_1112_, v___x_1113_, v___x_1099_, v_a_1055_);
                            crate::leanh::lean_dec(v_a_1069_);
                            if crate::leanh::lean_obj_tag(v___x_1114_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1114_, 1);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1068_);
                                crate::leanh::lean_dec_ref(v_leanOpts_1061_);
                                crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                                v_a_1115_ = crate::leanh::lean_ctor_get(v___x_1114_, 0);
                                v_isSharedCheck_1122_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1114_)) as u8;
                                if v_isSharedCheck_1122_ == 0 {
                                    v___x_1117_ = v___x_1114_;
                                    v_isShared_1118_ = v_isSharedCheck_1122_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1115_);
                                    crate::leanh::lean_dec(v___x_1114_);
                                    v___x_1117_ = crate::leanh::lean_box(0);
                                    v_isShared_1118_ = v_isSharedCheck_1122_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_leanOpts_1061_);
                    crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                    v_a_1123_ = crate::leanh::lean_ctor_get(v___x_1067_, 1);
                    crate::leanh::lean_inc(v_a_1123_);
                    crate::leanh::lean_dec_ref_known(v___x_1067_, 2);
                    v___x_1124_ = lean_array_get_size(v_a_1123_);
                    v___x_1125_ = lean_nat_dec_lt(v___x_1065_, v___x_1124_);
                    if v___x_1125_ == 0 {
                        crate::leanh::lean_dec(v_a_1123_);
                        v___x_1126_ = crate::leanh::lean_box(0);
                        v___x_1127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
                        return v___x_1127_;
                    } else {
                        v___x_1128_ = crate::leanh::lean_box(0);
                        v___x_1129_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
                        if v___x_1129_ == 0 {
                            if v___x_1125_ == 0 {
                                crate::leanh::lean_dec(v_a_1123_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1130_ = 0usize;
                                v___x_1131_ = lean_usize_of_nat(v___x_1124_);
                                v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1123_, v___x_1130_, v___x_1131_, v___x_1128_, v_a_1055_);
                                crate::leanh::lean_dec(v_a_1123_);
                                if crate::leanh::lean_obj_tag(v___x_1132_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1132_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_1133_ = crate::leanh::lean_ctor_get(v___x_1132_, 0);
                                    v_isSharedCheck_1140_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1132_)) as u8;
                                    if v_isSharedCheck_1140_ == 0 {
                                        v___x_1135_ = v___x_1132_;
                                        v_isShared_1136_ = v_isSharedCheck_1140_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1133_);
                                        crate::leanh::lean_dec(v___x_1132_);
                                        v___x_1135_ = crate::leanh::lean_box(0);
                                        v_isShared_1136_ = v_isSharedCheck_1140_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_1141_ = 0usize;
                            v___x_1142_ = lean_usize_of_nat(v___x_1124_);
                            v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1123_, v___x_1141_, v___x_1142_, v___x_1128_, v_a_1055_);
                            crate::leanh::lean_dec(v_a_1123_);
                            if crate::leanh::lean_obj_tag(v___x_1143_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1143_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_1144_ = crate::leanh::lean_ctor_get(v___x_1143_, 0);
                                v_isSharedCheck_1151_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1143_)) as u8;
                                if v_isSharedCheck_1151_ == 0 {
                                    v___x_1146_ = v___x_1143_;
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1144_);
                                    crate::leanh::lean_dec(v___x_1143_);
                                    v___x_1146_ = crate::leanh::lean_box(0);
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1058_ = crate::leanh::lean_box(0);
                v___x_1059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1059_, 0, v___x_1058_);
                return v___x_1059_;
            }
            2 => {
                if v_updateDeps_1063_ == 0 {
                    v_packages_1071_ = crate::leanh::lean_ctor_get(v_a_1068_, 4);
                    v___x_1072_ = lean_array_fget_borrowed(v_packages_1071_, v___x_1065_);
                    v_dir_1073_ = crate::leanh::lean_ctor_get(v___x_1072_, 4);
                    v_relManifestFile_1074_ = crate::leanh::lean_ctor_get(v___x_1072_, 9);
                    crate::leanh::lean_inc_ref(v_relManifestFile_1074_);
                    crate::leanh::lean_inc_ref(v_dir_1073_);
                    v___x_1075_ = l_Lake_joinRelative(v_dir_1073_, v_relManifestFile_1074_);
                    v___x_1076_ = l_Lake_Manifest_load_x3f(v___x_1075_);
                    if crate::leanh::lean_obj_tag(v___x_1076_) == 0 {
                        v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1076_, 0);
                        crate::leanh::lean_inc(v_a_1077_);
                        crate::leanh::lean_dec_ref_known(v___x_1076_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1077_) == 1 {
                            v_val_1078_ = crate::leanh::lean_ctor_get(v_a_1077_, 0);
                            crate::leanh::lean_inc(v_val_1078_);
                            crate::leanh::lean_dec_ref_known(v_a_1077_, 1);
                            v___x_1079_ = l_Lake_Workspace_materializeDeps(
                                v_a_1068_,
                                v_val_1078_,
                                v_leanOpts_1061_,
                                v_reconfigure_1062_,
                                v_packageOverrides_1060_,
                                v_a_1055_,
                            );
                            crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                            return v___x_1079_;
                        } else {
                            crate::leanh::lean_dec(v_a_1077_);
                            crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                            v___x_1080_ = l_Lean_NameSet_empty;
                            v___x_1081_ = l_Lake_Workspace_updateAndMaterialize(
                                v_a_1068_,
                                v___x_1080_,
                                v_leanOpts_1061_,
                                v_updateToolchain_1064_,
                                v_a_1055_,
                            );
                            return v___x_1081_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1068_);
                        crate::leanh::lean_dec_ref(v_leanOpts_1061_);
                        crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                        v_a_1082_ = crate::leanh::lean_ctor_get(v___x_1076_, 0);
                        v_isSharedCheck_1094_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1076_)) as u8;
                        if v_isSharedCheck_1094_ == 0 {
                            v___x_1084_ = v___x_1076_;
                            v_isShared_1085_ = v_isSharedCheck_1094_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1082_);
                            crate::leanh::lean_dec(v___x_1076_);
                            v___x_1084_ = crate::leanh::lean_box(0);
                            v_isShared_1085_ = v_isSharedCheck_1094_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_packageOverrides_1060_);
                    v___x_1095_ = l_Lean_NameSet_empty;
                    v___x_1096_ = l_Lake_Workspace_updateAndMaterialize(
                        v_a_1068_,
                        v___x_1095_,
                        v_leanOpts_1061_,
                        v_updateToolchain_1064_,
                        v_a_1055_,
                    );
                    return v___x_1096_;
                }
            }
            3 => {
                v___x_1086_ = lean_io_error_to_string(v_a_1082_);
                v___x_1087_ = 3;
                v___x_1088_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1088_, 0, v___x_1086_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1088_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1087_,
                );
                crate::leanh::lean_inc_ref(v_a_1055_);
                v___x_1089_ =
                    crate::leanh::lean_apply_2(v_a_1055_, v___x_1088_, crate::leanh::lean_box(0));
                v___x_1090_ = crate::leanh::lean_box(0);
                if v_isShared_1085_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1084_, 0, v___x_1090_);
                    v___x_1092_ = v___x_1084_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
                    v___x_1092_ = v_reuseFailAlloc_1093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1092_;
            }
            5 => {
                if v_isShared_1107_ == 0 {
                    v___x_1109_ = v___x_1106_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1109_;
            }
            7 => {
                if v_isShared_1118_ == 0 {
                    v___x_1120_ = v___x_1117_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
                    v___x_1120_ = v_reuseFailAlloc_1121_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1120_;
            }
            9 => {
                if v_isShared_1136_ == 0 {
                    v___x_1138_ = v___x_1135_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
                    v___x_1138_ = v_reuseFailAlloc_1139_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1138_;
            }
            11 => {
                if v_isShared_1147_ == 0 {
                    v___x_1149_ = v___x_1146_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
                    v___x_1149_ = v_reuseFailAlloc_1150_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_loadWorkspace___boxed(
    mut v_config_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lake_loadWorkspace(v_config_1152_, v_a_1153_);
    crate::leanh::lean_dec_ref(v_a_1153_);
    return v_res_1155_;
}
pub unsafe fn l_Lake_updateManifest(
    mut v_config_1156_: *mut crate::leanh::LeanObject,
    mut v_toUpdate_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateToolchain_1164_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_unused_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: usize = 0;
    let mut v___x_1194_: usize = 0;
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: usize = 0;
    let mut v___x_1210_: usize = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_leanOpts_1163_ = crate::leanh::lean_ctor_get(v_config_1156_, 13);
                crate::leanh::lean_inc_ref(v_leanOpts_1163_);
                v_updateToolchain_1164_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1156_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                );
                v___x_1165_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1166_ = l_Lake_loadWorkspace___closed__0;
                v___x_1167_ = l_Lake_loadWorkspaceRoot(v_config_1156_, v___x_1166_);
                if crate::leanh::lean_obj_tag(v___x_1167_) == 0 {
                    v_a_1168_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    crate::leanh::lean_inc(v_a_1168_);
                    v_a_1169_ = crate::leanh::lean_ctor_get(v___x_1167_, 1);
                    crate::leanh::lean_inc(v_a_1169_);
                    crate::leanh::lean_dec_ref_known(v___x_1167_, 2);
                    v___x_1189_ = lean_array_get_size(v_a_1169_);
                    v___x_1190_ = lean_nat_dec_lt(v___x_1165_, v___x_1189_);
                    if v___x_1190_ == 0 {
                        crate::leanh::lean_dec(v_a_1169_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1191_ = crate::leanh::lean_box(0);
                        v___x_1192_ = lean_nat_dec_le(v___x_1189_, v___x_1189_);
                        if v___x_1192_ == 0 {
                            if v___x_1190_ == 0 {
                                crate::leanh::lean_dec(v_a_1169_);
                                state = 2;
                                continue;
                            } else {
                                v___x_1193_ = 0usize;
                                v___x_1194_ = lean_usize_of_nat(v___x_1189_);
                                v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1169_, v___x_1193_, v___x_1194_, v___x_1191_, v_a_1158_);
                                crate::leanh::lean_dec(v_a_1169_);
                                if crate::leanh::lean_obj_tag(v___x_1195_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1195_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1168_);
                                    crate::leanh::lean_dec_ref(v_leanOpts_1163_);
                                    return v___x_1195_;
                                }
                            }
                        } else {
                            v___x_1196_ = 0usize;
                            v___x_1197_ = lean_usize_of_nat(v___x_1189_);
                            v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1169_, v___x_1196_, v___x_1197_, v___x_1191_, v_a_1158_);
                            crate::leanh::lean_dec(v_a_1169_);
                            if crate::leanh::lean_obj_tag(v___x_1198_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1198_, 1);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1168_);
                                crate::leanh::lean_dec_ref(v_leanOpts_1163_);
                                return v___x_1198_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_leanOpts_1163_);
                    v_a_1199_ = crate::leanh::lean_ctor_get(v___x_1167_, 1);
                    crate::leanh::lean_inc(v_a_1199_);
                    crate::leanh::lean_dec_ref_known(v___x_1167_, 2);
                    v___x_1200_ = lean_array_get_size(v_a_1199_);
                    v___x_1201_ = lean_nat_dec_lt(v___x_1165_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        crate::leanh::lean_dec(v_a_1199_);
                        v___x_1202_ = crate::leanh::lean_box(0);
                        v___x_1203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1203_, 0, v___x_1202_);
                        return v___x_1203_;
                    } else {
                        v___x_1204_ = crate::leanh::lean_box(0);
                        v___x_1205_ = lean_nat_dec_le(v___x_1200_, v___x_1200_);
                        if v___x_1205_ == 0 {
                            if v___x_1201_ == 0 {
                                crate::leanh::lean_dec(v_a_1199_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1206_ = 0usize;
                                v___x_1207_ = lean_usize_of_nat(v___x_1200_);
                                v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1199_, v___x_1206_, v___x_1207_, v___x_1204_, v_a_1158_);
                                crate::leanh::lean_dec(v_a_1199_);
                                if crate::leanh::lean_obj_tag(v___x_1208_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1208_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_1208_;
                                }
                            }
                        } else {
                            v___x_1209_ = 0usize;
                            v___x_1210_ = lean_usize_of_nat(v___x_1200_);
                            v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1199_, v___x_1209_, v___x_1210_, v___x_1204_, v_a_1158_);
                            crate::leanh::lean_dec(v_a_1199_);
                            if crate::leanh::lean_obj_tag(v___x_1211_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1211_, 1);
                                state = 1;
                                continue;
                            } else {
                                return v___x_1211_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1161_ = crate::leanh::lean_box(0);
                v___x_1162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                return v___x_1162_;
            }
            2 => {
                v___x_1171_ = l_Lake_Workspace_updateAndMaterialize(
                    v_a_1168_,
                    v_toUpdate_1157_,
                    v_leanOpts_1163_,
                    v_updateToolchain_1164_,
                    v_a_1158_,
                );
                if crate::leanh::lean_obj_tag(v___x_1171_) == 0 {
                    v_isSharedCheck_1179_ = (!crate::leanh::lean_is_exclusive(v___x_1171_)) as u8;
                    if v_isSharedCheck_1179_ == 0 {
                        v_unused_1180_ = crate::leanh::lean_ctor_get(v___x_1171_, 0);
                        crate::leanh::lean_dec(v_unused_1180_);
                        v___x_1173_ = v___x_1171_;
                        v_isShared_1174_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1171_);
                        v___x_1173_ = crate::leanh::lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1181_ = crate::leanh::lean_ctor_get(v___x_1171_, 0);
                    v_isSharedCheck_1188_ = (!crate::leanh::lean_is_exclusive(v___x_1171_)) as u8;
                    if v_isSharedCheck_1188_ == 0 {
                        v___x_1183_ = v___x_1171_;
                        v_isShared_1184_ = v_isSharedCheck_1188_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1181_);
                        crate::leanh::lean_dec(v___x_1171_);
                        v___x_1183_ = crate::leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1188_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1175_ = crate::leanh::lean_box(0);
                if v_isShared_1174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1175_);
                    v___x_1177_ = v___x_1173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1177_;
            }
            5 => {
                if v_isShared_1184_ == 0 {
                    v___x_1186_ = v___x_1183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
                    v___x_1186_ = v_reuseFailAlloc_1187_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_updateManifest___boxed(
    mut v_config_1212_: *mut crate::leanh::LeanObject,
    mut v_toUpdate_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
    mut v_a_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Lake_updateManifest(v_config_1212_, v_toUpdate_1213_, v_a_1214_);
    crate::leanh::lean_dec_ref(v_a_1214_);
    crate::leanh::lean_dec(v_toUpdate_1213_);
    return v_res_1216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Workspace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Resolve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_InitFacets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Workspace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Workspace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Resolve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_InitFacets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Workspace(builtin);
}

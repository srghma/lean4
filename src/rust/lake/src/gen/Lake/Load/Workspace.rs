// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: Lake.Load.Config Lake.Config.Workspace Lake.Load.Resolve Lake.Load.Package Lake.Load.Lean.Eval Lake.Load.Toml Lake.Build.InitFacets
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_st_ref_set, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
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
pub static l_Lake_loadWorkspaceRoot___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_loadWorkspaceRoot___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_loadWorkspaceRoot___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_loadWorkspace___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_loadWorkspace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_loadWorkspace___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(
    mut v_as_609_: *mut leanh::LeanObject,
    mut v_i_610_: usize,
    mut v_stop_611_: usize,
    mut v_b_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: usize = 0;
    let mut v___x_619_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_613_ = lean_usize_dec_eq(v_i_610_, v_stop_611_);
                if v___x_613_ == 0 {
                    v___x_614_ = lean_array_uget_borrowed(v_as_609_, v_i_610_);
                    v_name_615_ = leanh::lean_ctor_get(v___x_614_, 0);
                    v_config_616_ = leanh::lean_ctor_get(v___x_614_, 1);
                    leanh::lean_inc(v_config_616_);
                    leanh::lean_inc(v_name_615_);
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
    mut v_as_621_: *mut leanh::LeanObject,
    mut v_i_622_: *mut leanh::LeanObject,
    mut v_stop_623_: *mut leanh::LeanObject,
    mut v_b_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_625_: usize = 0;
    let mut v_stop_boxed_626_: usize = 0;
    let mut v_res_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_625_ = leanh::lean_unbox_usize(v_i_622_);
    leanh::lean_dec(v_i_622_);
    v_stop_boxed_626_ = leanh::lean_unbox_usize(v_stop_623_);
    leanh::lean_dec(v_stop_623_);
    v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_as_621_, v_i_boxed_625_, v_stop_boxed_626_, v_b_624_);
    leanh::lean_dec_ref(v_as_621_);
    return v_res_627_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(
    mut v_k_628_: *mut leanh::LeanObject,
    mut v_v_629_: *mut leanh::LeanObject,
    mut v_t_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: u8 = 0;
    let mut v_impl_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v_size_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut v_unused_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_710_: u8 = 0;
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_714_: u8 = 0;
    let mut v_unused_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_721_: u8 = 0;
    let mut v_unused_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v_k_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut v_unused_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_unused_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_size_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_835_: u8 = 0;
    let mut v_unused_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_848_: u8 = 0;
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_852_: u8 = 0;
    let mut v_unused_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_unused_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v_k_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_unused_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v_unused_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_907_: u8 = 0;
    let mut v_unused_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_630_) == 0 {
                    v_size_631_ = leanh::lean_ctor_get(v_t_630_, 0);
                    v_k_632_ = leanh::lean_ctor_get(v_t_630_, 1);
                    v_v_633_ = leanh::lean_ctor_get(v_t_630_, 2);
                    v_l_634_ = leanh::lean_ctor_get(v_t_630_, 3);
                    v_r_635_ = leanh::lean_ctor_get(v_t_630_, 4);
                    v_isSharedCheck_915_ = (!leanh::lean_is_exclusive(v_t_630_)) as u8;
                    if v_isSharedCheck_915_ == 0 {
                        v___x_637_ = v_t_630_;
                        v_isShared_638_ = v_isSharedCheck_915_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_635_);
                        leanh::lean_inc(v_l_634_);
                        leanh::lean_inc(v_v_633_);
                        leanh::lean_inc(v_k_632_);
                        leanh::lean_inc(v_size_631_);
                        leanh::lean_dec(v_t_630_);
                        v___x_637_ = leanh::lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_916_ = leanh::lean_unsigned_to_nat(1);
                    v___x_917_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_917_, 0, v___x_916_);
                    leanh::lean_ctor_set(v___x_917_, 1, v_k_628_);
                    leanh::lean_ctor_set(v___x_917_, 2, v_v_629_);
                    leanh::lean_ctor_set(v___x_917_, 3, v_t_630_);
                    leanh::lean_ctor_set(v___x_917_, 4, v_t_630_);
                    return v___x_917_;
                }
            }
            1 => {
                v___x_639_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_628_, v_k_632_);
                match v___x_639_ {
                    0 => {
                        leanh::lean_dec(v_size_631_);
                        v_impl_640_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_628_, v_v_629_, v_l_634_);
                        v___x_641_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_635_) == 0 {
                            v_size_642_ = leanh::lean_ctor_get(v_r_635_, 0);
                            v_size_643_ = leanh::lean_ctor_get(v_impl_640_, 0);
                            leanh::lean_inc(v_size_643_);
                            v_k_644_ = leanh::lean_ctor_get(v_impl_640_, 1);
                            leanh::lean_inc(v_k_644_);
                            v_v_645_ = leanh::lean_ctor_get(v_impl_640_, 2);
                            leanh::lean_inc(v_v_645_);
                            v_l_646_ = leanh::lean_ctor_get(v_impl_640_, 3);
                            leanh::lean_inc(v_l_646_);
                            v_r_647_ = leanh::lean_ctor_get(v_impl_640_, 4);
                            leanh::lean_inc(v_r_647_);
                            v___x_648_ = leanh::lean_unsigned_to_nat(3);
                            v___x_649_ = lean_nat_mul(v___x_648_, v_size_642_);
                            v___x_650_ = lean_nat_dec_lt(v___x_649_, v_size_643_);
                            leanh::lean_dec(v___x_649_);
                            if v___x_650_ == 0 {
                                leanh::lean_dec(v_r_647_);
                                leanh::lean_dec(v_l_646_);
                                leanh::lean_dec(v_v_645_);
                                leanh::lean_dec(v_k_644_);
                                v___x_651_ = lean_nat_add(v___x_641_, v_size_643_);
                                leanh::lean_dec(v_size_643_);
                                v___x_652_ = lean_nat_add(v___x_651_, v_size_642_);
                                leanh::lean_dec(v___x_651_);
                                if v_isShared_638_ == 0 {
                                    leanh::lean_ctor_set(v___x_637_, 3, v_impl_640_);
                                    leanh::lean_ctor_set(v___x_637_, 0, v___x_652_);
                                    v___x_654_ = v___x_637_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_655_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_655_,
                                        0,
                                        v___x_652_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_632_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_633_);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_655_,
                                        3,
                                        v_impl_640_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_635_);
                                    v___x_654_ = v_reuseFailAlloc_655_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_721_ =
                                    (!leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                if v_isSharedCheck_721_ == 0 {
                                    v_unused_722_ = leanh::lean_ctor_get(v_impl_640_, 4);
                                    leanh::lean_dec(v_unused_722_);
                                    v_unused_723_ = leanh::lean_ctor_get(v_impl_640_, 3);
                                    leanh::lean_dec(v_unused_723_);
                                    v_unused_724_ = leanh::lean_ctor_get(v_impl_640_, 2);
                                    leanh::lean_dec(v_unused_724_);
                                    v_unused_725_ = leanh::lean_ctor_get(v_impl_640_, 1);
                                    leanh::lean_dec(v_unused_725_);
                                    v_unused_726_ = leanh::lean_ctor_get(v_impl_640_, 0);
                                    leanh::lean_dec(v_unused_726_);
                                    v___x_657_ = v_impl_640_;
                                    v_isShared_658_ = v_isSharedCheck_721_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_640_);
                                    v___x_657_ = leanh::lean_box(0);
                                    v_isShared_658_ = v_isSharedCheck_721_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_727_ = leanh::lean_ctor_get(v_impl_640_, 3);
                            leanh::lean_inc(v_l_727_);
                            if leanh::lean_obj_tag(v_l_727_) == 0 {
                                v_r_728_ = leanh::lean_ctor_get(v_impl_640_, 4);
                                v_k_729_ = leanh::lean_ctor_get(v_impl_640_, 1);
                                v_v_730_ = leanh::lean_ctor_get(v_impl_640_, 2);
                                v_isSharedCheck_741_ =
                                    (!leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                if v_isSharedCheck_741_ == 0 {
                                    v_unused_742_ = leanh::lean_ctor_get(v_impl_640_, 3);
                                    leanh::lean_dec(v_unused_742_);
                                    v_unused_743_ = leanh::lean_ctor_get(v_impl_640_, 0);
                                    leanh::lean_dec(v_unused_743_);
                                    v___x_732_ = v_impl_640_;
                                    v_isShared_733_ = v_isSharedCheck_741_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_728_);
                                    leanh::lean_inc(v_v_730_);
                                    leanh::lean_inc(v_k_729_);
                                    leanh::lean_dec(v_impl_640_);
                                    v___x_732_ = leanh::lean_box(0);
                                    v_isShared_733_ = v_isSharedCheck_741_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_744_ = leanh::lean_ctor_get(v_impl_640_, 4);
                                leanh::lean_inc(v_r_744_);
                                if leanh::lean_obj_tag(v_r_744_) == 0 {
                                    v_k_745_ = leanh::lean_ctor_get(v_impl_640_, 1);
                                    v_v_746_ = leanh::lean_ctor_get(v_impl_640_, 2);
                                    v_isSharedCheck_769_ =
                                        (!leanh::lean_is_exclusive(v_impl_640_)) as u8;
                                    if v_isSharedCheck_769_ == 0 {
                                        v_unused_770_ = leanh::lean_ctor_get(v_impl_640_, 4);
                                        leanh::lean_dec(v_unused_770_);
                                        v_unused_771_ = leanh::lean_ctor_get(v_impl_640_, 3);
                                        leanh::lean_dec(v_unused_771_);
                                        v_unused_772_ = leanh::lean_ctor_get(v_impl_640_, 0);
                                        leanh::lean_dec(v_unused_772_);
                                        v___x_748_ = v_impl_640_;
                                        v_isShared_749_ = v_isSharedCheck_769_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_746_);
                                        leanh::lean_inc(v_k_745_);
                                        leanh::lean_dec(v_impl_640_);
                                        v___x_748_ = leanh::lean_box(0);
                                        v_isShared_749_ = v_isSharedCheck_769_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_773_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_638_ == 0 {
                                        leanh::lean_ctor_set(v___x_637_, 4, v_r_744_);
                                        leanh::lean_ctor_set(v___x_637_, 3, v_impl_640_);
                                        leanh::lean_ctor_set(v___x_637_, 0, v___x_773_);
                                        v___x_775_ = v___x_637_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_776_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            0,
                                            v___x_773_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            1,
                                            v_k_632_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            2,
                                            v_v_633_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_776_,
                                            3,
                                            v_impl_640_,
                                        );
                                        leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_v_633_);
                        leanh::lean_dec(v_k_632_);
                        if v_isShared_638_ == 0 {
                            leanh::lean_ctor_set(v___x_637_, 2, v_v_629_);
                            leanh::lean_ctor_set(v___x_637_, 1, v_k_628_);
                            v___x_778_ = v___x_637_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_779_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_779_, 0, v_size_631_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_628_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_629_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_634_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_779_, 4, v_r_635_);
                            v___x_778_ = v_reuseFailAlloc_779_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_631_);
                        v_impl_780_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_628_, v_v_629_, v_r_635_);
                        v___x_781_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_634_) == 0 {
                            v_size_782_ = leanh::lean_ctor_get(v_l_634_, 0);
                            v_size_783_ = leanh::lean_ctor_get(v_impl_780_, 0);
                            leanh::lean_inc(v_size_783_);
                            v_k_784_ = leanh::lean_ctor_get(v_impl_780_, 1);
                            leanh::lean_inc(v_k_784_);
                            v_v_785_ = leanh::lean_ctor_get(v_impl_780_, 2);
                            leanh::lean_inc(v_v_785_);
                            v_l_786_ = leanh::lean_ctor_get(v_impl_780_, 3);
                            leanh::lean_inc(v_l_786_);
                            v_r_787_ = leanh::lean_ctor_get(v_impl_780_, 4);
                            leanh::lean_inc(v_r_787_);
                            v___x_788_ = leanh::lean_unsigned_to_nat(3);
                            v___x_789_ = lean_nat_mul(v___x_788_, v_size_782_);
                            v___x_790_ = lean_nat_dec_lt(v___x_789_, v_size_783_);
                            leanh::lean_dec(v___x_789_);
                            if v___x_790_ == 0 {
                                leanh::lean_dec(v_r_787_);
                                leanh::lean_dec(v_l_786_);
                                leanh::lean_dec(v_v_785_);
                                leanh::lean_dec(v_k_784_);
                                v___x_791_ = lean_nat_add(v___x_781_, v_size_782_);
                                v___x_792_ = lean_nat_add(v___x_791_, v_size_783_);
                                leanh::lean_dec(v_size_783_);
                                leanh::lean_dec(v___x_791_);
                                if v_isShared_638_ == 0 {
                                    leanh::lean_ctor_set(v___x_637_, 4, v_impl_780_);
                                    leanh::lean_ctor_set(v___x_637_, 0, v___x_792_);
                                    v___x_794_ = v___x_637_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_795_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_795_,
                                        0,
                                        v___x_792_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_632_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_633_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 3, v_l_634_);
                                    leanh::lean_ctor_set(
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
                                    (!leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                if v_isSharedCheck_859_ == 0 {
                                    v_unused_860_ = leanh::lean_ctor_get(v_impl_780_, 4);
                                    leanh::lean_dec(v_unused_860_);
                                    v_unused_861_ = leanh::lean_ctor_get(v_impl_780_, 3);
                                    leanh::lean_dec(v_unused_861_);
                                    v_unused_862_ = leanh::lean_ctor_get(v_impl_780_, 2);
                                    leanh::lean_dec(v_unused_862_);
                                    v_unused_863_ = leanh::lean_ctor_get(v_impl_780_, 1);
                                    leanh::lean_dec(v_unused_863_);
                                    v_unused_864_ = leanh::lean_ctor_get(v_impl_780_, 0);
                                    leanh::lean_dec(v_unused_864_);
                                    v___x_797_ = v_impl_780_;
                                    v_isShared_798_ = v_isSharedCheck_859_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_780_);
                                    v___x_797_ = leanh::lean_box(0);
                                    v_isShared_798_ = v_isSharedCheck_859_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_865_ = leanh::lean_ctor_get(v_impl_780_, 3);
                            leanh::lean_inc(v_l_865_);
                            if leanh::lean_obj_tag(v_l_865_) == 0 {
                                v_r_866_ = leanh::lean_ctor_get(v_impl_780_, 4);
                                v_k_867_ = leanh::lean_ctor_get(v_impl_780_, 1);
                                v_v_868_ = leanh::lean_ctor_get(v_impl_780_, 2);
                                v_isSharedCheck_891_ =
                                    (!leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                if v_isSharedCheck_891_ == 0 {
                                    v_unused_892_ = leanh::lean_ctor_get(v_impl_780_, 3);
                                    leanh::lean_dec(v_unused_892_);
                                    v_unused_893_ = leanh::lean_ctor_get(v_impl_780_, 0);
                                    leanh::lean_dec(v_unused_893_);
                                    v___x_870_ = v_impl_780_;
                                    v_isShared_871_ = v_isSharedCheck_891_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_866_);
                                    leanh::lean_inc(v_v_868_);
                                    leanh::lean_inc(v_k_867_);
                                    leanh::lean_dec(v_impl_780_);
                                    v___x_870_ = leanh::lean_box(0);
                                    v_isShared_871_ = v_isSharedCheck_891_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_894_ = leanh::lean_ctor_get(v_impl_780_, 4);
                                leanh::lean_inc(v_r_894_);
                                if leanh::lean_obj_tag(v_r_894_) == 0 {
                                    v_k_895_ = leanh::lean_ctor_get(v_impl_780_, 1);
                                    v_v_896_ = leanh::lean_ctor_get(v_impl_780_, 2);
                                    v_isSharedCheck_907_ =
                                        (!leanh::lean_is_exclusive(v_impl_780_)) as u8;
                                    if v_isSharedCheck_907_ == 0 {
                                        v_unused_908_ = leanh::lean_ctor_get(v_impl_780_, 4);
                                        leanh::lean_dec(v_unused_908_);
                                        v_unused_909_ = leanh::lean_ctor_get(v_impl_780_, 3);
                                        leanh::lean_dec(v_unused_909_);
                                        v_unused_910_ = leanh::lean_ctor_get(v_impl_780_, 0);
                                        leanh::lean_dec(v_unused_910_);
                                        v___x_898_ = v_impl_780_;
                                        v_isShared_899_ = v_isSharedCheck_907_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_896_);
                                        leanh::lean_inc(v_k_895_);
                                        leanh::lean_dec(v_impl_780_);
                                        v___x_898_ = leanh::lean_box(0);
                                        v_isShared_899_ = v_isSharedCheck_907_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_911_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_638_ == 0 {
                                        leanh::lean_ctor_set(v___x_637_, 4, v_impl_780_);
                                        leanh::lean_ctor_set(v___x_637_, 3, v_r_894_);
                                        leanh::lean_ctor_set(v___x_637_, 0, v___x_911_);
                                        v___x_913_ = v___x_637_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_914_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            0,
                                            v___x_911_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            1,
                                            v_k_632_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            2,
                                            v_v_633_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_914_,
                                            3,
                                            v_r_894_,
                                        );
                                        leanh::lean_ctor_set(
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
                v_size_659_ = leanh::lean_ctor_get(v_l_646_, 0);
                v_size_660_ = leanh::lean_ctor_get(v_r_647_, 0);
                v_k_661_ = leanh::lean_ctor_get(v_r_647_, 1);
                v_v_662_ = leanh::lean_ctor_get(v_r_647_, 2);
                v_l_663_ = leanh::lean_ctor_get(v_r_647_, 3);
                v_r_664_ = leanh::lean_ctor_get(v_r_647_, 4);
                v___x_665_ = leanh::lean_unsigned_to_nat(2);
                v___x_666_ = lean_nat_mul(v___x_665_, v_size_659_);
                v___x_667_ = lean_nat_dec_lt(v_size_660_, v___x_666_);
                leanh::lean_dec(v___x_666_);
                if v___x_667_ == 0 {
                    leanh::lean_inc(v_r_664_);
                    leanh::lean_inc(v_l_663_);
                    leanh::lean_inc(v_v_662_);
                    leanh::lean_inc(v_k_661_);
                    v_isSharedCheck_696_ = (!leanh::lean_is_exclusive(v_r_647_)) as u8;
                    if v_isSharedCheck_696_ == 0 {
                        v_unused_697_ = leanh::lean_ctor_get(v_r_647_, 4);
                        leanh::lean_dec(v_unused_697_);
                        v_unused_698_ = leanh::lean_ctor_get(v_r_647_, 3);
                        leanh::lean_dec(v_unused_698_);
                        v_unused_699_ = leanh::lean_ctor_get(v_r_647_, 2);
                        leanh::lean_dec(v_unused_699_);
                        v_unused_700_ = leanh::lean_ctor_get(v_r_647_, 1);
                        leanh::lean_dec(v_unused_700_);
                        v_unused_701_ = leanh::lean_ctor_get(v_r_647_, 0);
                        leanh::lean_dec(v_unused_701_);
                        v___x_669_ = v_r_647_;
                        v_isShared_670_ = v_isSharedCheck_696_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_647_);
                        v___x_669_ = leanh::lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_696_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_637_);
                    v___x_702_ = lean_nat_add(v___x_641_, v_size_643_);
                    leanh::lean_dec(v_size_643_);
                    v___x_703_ = lean_nat_add(v___x_702_, v_size_642_);
                    leanh::lean_dec(v___x_702_);
                    v___x_704_ = lean_nat_add(v___x_641_, v_size_642_);
                    v___x_705_ = lean_nat_add(v___x_704_, v_size_660_);
                    leanh::lean_dec(v___x_704_);
                    leanh::lean_inc_ref(v_r_635_);
                    if v_isShared_658_ == 0 {
                        leanh::lean_ctor_set(v___x_657_, 4, v_r_635_);
                        leanh::lean_ctor_set(v___x_657_, 3, v_r_647_);
                        leanh::lean_ctor_set(v___x_657_, 2, v_v_633_);
                        leanh::lean_ctor_set(v___x_657_, 1, v_k_632_);
                        leanh::lean_ctor_set(v___x_657_, 0, v___x_705_);
                        v___x_707_ = v___x_657_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_720_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_705_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_632_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_633_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_720_, 3, v_r_647_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_720_, 4, v_r_635_);
                        v___x_707_ = v_reuseFailAlloc_720_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_671_ = lean_nat_add(v___x_641_, v_size_643_);
                leanh::lean_dec(v_size_643_);
                v___x_672_ = lean_nat_add(v___x_671_, v_size_642_);
                leanh::lean_dec(v___x_671_);
                v___x_684_ = lean_nat_add(v___x_641_, v_size_659_);
                if leanh::lean_obj_tag(v_l_663_) == 0 {
                    v_size_694_ = leanh::lean_ctor_get(v_l_663_, 0);
                    leanh::lean_inc(v_size_694_);
                    v___y_686_ = v_size_694_;
                    state = 8;
                    continue;
                } else {
                    v___x_695_ = leanh::lean_unsigned_to_nat(0);
                    v___y_686_ = v___x_695_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_677_ = lean_nat_add(v___y_675_, v___y_676_);
                leanh::lean_dec(v___y_676_);
                leanh::lean_dec(v___y_675_);
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v_r_635_);
                    leanh::lean_ctor_set(v___x_669_, 3, v_r_664_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_633_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_632_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_677_);
                    v___x_679_ = v___x_669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 3, v_r_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 4, v_r_635_);
                    v___x_679_ = v_reuseFailAlloc_683_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_658_ == 0 {
                    leanh::lean_ctor_set(v___x_657_, 4, v___x_679_);
                    leanh::lean_ctor_set(v___x_657_, 3, v___y_674_);
                    leanh::lean_ctor_set(v___x_657_, 2, v_v_662_);
                    leanh::lean_ctor_set(v___x_657_, 1, v_k_661_);
                    leanh::lean_ctor_set(v___x_657_, 0, v___x_672_);
                    v___x_681_ = v___x_657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 3, v___y_674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 4, v___x_679_);
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
                leanh::lean_dec(v___y_686_);
                leanh::lean_dec(v___x_684_);
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v_l_663_);
                    leanh::lean_ctor_set(v___x_637_, 3, v_l_646_);
                    leanh::lean_ctor_set(v___x_637_, 2, v_v_645_);
                    leanh::lean_ctor_set(v___x_637_, 1, v_k_644_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_687_);
                    v___x_689_ = v___x_637_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 3, v_l_646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 4, v_l_663_);
                    v___x_689_ = v_reuseFailAlloc_693_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_690_ = lean_nat_add(v___x_641_, v_size_642_);
                if leanh::lean_obj_tag(v_r_664_) == 0 {
                    v_size_691_ = leanh::lean_ctor_get(v_r_664_, 0);
                    leanh::lean_inc(v_size_691_);
                    v___y_674_ = v___x_689_;
                    v___y_675_ = v___x_690_;
                    v___y_676_ = v_size_691_;
                    state = 5;
                    continue;
                } else {
                    v___x_692_ = leanh::lean_unsigned_to_nat(0);
                    v___y_674_ = v___x_689_;
                    v___y_675_ = v___x_690_;
                    v___y_676_ = v___x_692_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_714_ = (!leanh::lean_is_exclusive(v_r_635_)) as u8;
                if v_isSharedCheck_714_ == 0 {
                    v_unused_715_ = leanh::lean_ctor_get(v_r_635_, 4);
                    leanh::lean_dec(v_unused_715_);
                    v_unused_716_ = leanh::lean_ctor_get(v_r_635_, 3);
                    leanh::lean_dec(v_unused_716_);
                    v_unused_717_ = leanh::lean_ctor_get(v_r_635_, 2);
                    leanh::lean_dec(v_unused_717_);
                    v_unused_718_ = leanh::lean_ctor_get(v_r_635_, 1);
                    leanh::lean_dec(v_unused_718_);
                    v_unused_719_ = leanh::lean_ctor_get(v_r_635_, 0);
                    leanh::lean_dec(v_unused_719_);
                    v___x_709_ = v_r_635_;
                    v_isShared_710_ = v_isSharedCheck_714_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_635_);
                    v___x_709_ = leanh::lean_box(0);
                    v_isShared_710_ = v_isSharedCheck_714_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_710_ == 0 {
                    leanh::lean_ctor_set(v___x_709_, 4, v___x_707_);
                    leanh::lean_ctor_set(v___x_709_, 3, v_l_646_);
                    leanh::lean_ctor_set(v___x_709_, 2, v_v_645_);
                    leanh::lean_ctor_set(v___x_709_, 1, v_k_644_);
                    leanh::lean_ctor_set(v___x_709_, 0, v___x_703_);
                    v___x_712_ = v___x_709_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_713_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_713_, 1, v_k_644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_713_, 2, v_v_645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_713_, 3, v_l_646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_713_, 4, v___x_707_);
                    v___x_712_ = v_reuseFailAlloc_713_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_712_;
            }
            13 => {
                v___x_734_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_728_);
                if v_isShared_733_ == 0 {
                    leanh::lean_ctor_set(v___x_732_, 3, v_r_728_);
                    leanh::lean_ctor_set(v___x_732_, 2, v_v_633_);
                    leanh::lean_ctor_set(v___x_732_, 1, v_k_632_);
                    leanh::lean_ctor_set(v___x_732_, 0, v___x_641_);
                    v___x_736_ = v___x_732_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 3, v_r_728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 4, v_r_728_);
                    v___x_736_ = v_reuseFailAlloc_740_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v___x_736_);
                    leanh::lean_ctor_set(v___x_637_, 3, v_l_727_);
                    leanh::lean_ctor_set(v___x_637_, 2, v_v_730_);
                    leanh::lean_ctor_set(v___x_637_, 1, v_k_729_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_734_);
                    v___x_738_ = v___x_637_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 3, v_l_727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_736_);
                    v___x_738_ = v_reuseFailAlloc_739_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_738_;
            }
            16 => {
                v_k_750_ = leanh::lean_ctor_get(v_r_744_, 1);
                v_v_751_ = leanh::lean_ctor_get(v_r_744_, 2);
                v_isSharedCheck_765_ = (!leanh::lean_is_exclusive(v_r_744_)) as u8;
                if v_isSharedCheck_765_ == 0 {
                    v_unused_766_ = leanh::lean_ctor_get(v_r_744_, 4);
                    leanh::lean_dec(v_unused_766_);
                    v_unused_767_ = leanh::lean_ctor_get(v_r_744_, 3);
                    leanh::lean_dec(v_unused_767_);
                    v_unused_768_ = leanh::lean_ctor_get(v_r_744_, 0);
                    leanh::lean_dec(v_unused_768_);
                    v___x_753_ = v_r_744_;
                    v_isShared_754_ = v_isSharedCheck_765_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_751_);
                    leanh::lean_inc(v_k_750_);
                    leanh::lean_dec(v_r_744_);
                    v___x_753_ = leanh::lean_box(0);
                    v_isShared_754_ = v_isSharedCheck_765_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_755_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_754_ == 0 {
                    leanh::lean_ctor_set(v___x_753_, 4, v_l_727_);
                    leanh::lean_ctor_set(v___x_753_, 3, v_l_727_);
                    leanh::lean_ctor_set(v___x_753_, 2, v_v_746_);
                    leanh::lean_ctor_set(v___x_753_, 1, v_k_745_);
                    leanh::lean_ctor_set(v___x_753_, 0, v___x_641_);
                    v___x_757_ = v___x_753_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_764_, 3, v_l_727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_764_, 4, v_l_727_);
                    v___x_757_ = v_reuseFailAlloc_764_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_749_ == 0 {
                    leanh::lean_ctor_set(v___x_748_, 4, v_l_727_);
                    leanh::lean_ctor_set(v___x_748_, 2, v_v_633_);
                    leanh::lean_ctor_set(v___x_748_, 1, v_k_632_);
                    leanh::lean_ctor_set(v___x_748_, 0, v___x_641_);
                    v___x_759_ = v___x_748_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_763_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 3, v_l_727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 4, v_l_727_);
                    v___x_759_ = v_reuseFailAlloc_763_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v___x_759_);
                    leanh::lean_ctor_set(v___x_637_, 3, v___x_757_);
                    leanh::lean_ctor_set(v___x_637_, 2, v_v_751_);
                    leanh::lean_ctor_set(v___x_637_, 1, v_k_750_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_755_);
                    v___x_761_ = v___x_637_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_762_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_762_, 3, v___x_757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_759_);
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
                v_size_799_ = leanh::lean_ctor_get(v_l_786_, 0);
                v_k_800_ = leanh::lean_ctor_get(v_l_786_, 1);
                v_v_801_ = leanh::lean_ctor_get(v_l_786_, 2);
                v_l_802_ = leanh::lean_ctor_get(v_l_786_, 3);
                v_r_803_ = leanh::lean_ctor_get(v_l_786_, 4);
                v_size_804_ = leanh::lean_ctor_get(v_r_787_, 0);
                v___x_805_ = leanh::lean_unsigned_to_nat(2);
                v___x_806_ = lean_nat_mul(v___x_805_, v_size_804_);
                v___x_807_ = lean_nat_dec_lt(v_size_799_, v___x_806_);
                leanh::lean_dec(v___x_806_);
                if v___x_807_ == 0 {
                    leanh::lean_inc(v_r_803_);
                    leanh::lean_inc(v_l_802_);
                    leanh::lean_inc(v_v_801_);
                    leanh::lean_inc(v_k_800_);
                    v_isSharedCheck_835_ = (!leanh::lean_is_exclusive(v_l_786_)) as u8;
                    if v_isSharedCheck_835_ == 0 {
                        v_unused_836_ = leanh::lean_ctor_get(v_l_786_, 4);
                        leanh::lean_dec(v_unused_836_);
                        v_unused_837_ = leanh::lean_ctor_get(v_l_786_, 3);
                        leanh::lean_dec(v_unused_837_);
                        v_unused_838_ = leanh::lean_ctor_get(v_l_786_, 2);
                        leanh::lean_dec(v_unused_838_);
                        v_unused_839_ = leanh::lean_ctor_get(v_l_786_, 1);
                        leanh::lean_dec(v_unused_839_);
                        v_unused_840_ = leanh::lean_ctor_get(v_l_786_, 0);
                        leanh::lean_dec(v_unused_840_);
                        v___x_809_ = v_l_786_;
                        v_isShared_810_ = v_isSharedCheck_835_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_786_);
                        v___x_809_ = leanh::lean_box(0);
                        v_isShared_810_ = v_isSharedCheck_835_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_637_);
                    v___x_841_ = lean_nat_add(v___x_781_, v_size_782_);
                    v___x_842_ = lean_nat_add(v___x_841_, v_size_783_);
                    leanh::lean_dec(v_size_783_);
                    v___x_843_ = lean_nat_add(v___x_841_, v_size_799_);
                    leanh::lean_dec(v___x_841_);
                    leanh::lean_inc_ref(v_l_634_);
                    if v_isShared_798_ == 0 {
                        leanh::lean_ctor_set(v___x_797_, 4, v_l_786_);
                        leanh::lean_ctor_set(v___x_797_, 3, v_l_634_);
                        leanh::lean_ctor_set(v___x_797_, 2, v_v_633_);
                        leanh::lean_ctor_set(v___x_797_, 1, v_k_632_);
                        leanh::lean_ctor_set(v___x_797_, 0, v___x_843_);
                        v___x_845_ = v___x_797_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_858_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_843_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_632_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_633_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_634_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_858_, 4, v_l_786_);
                        v___x_845_ = v_reuseFailAlloc_858_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_811_ = lean_nat_add(v___x_781_, v_size_782_);
                v___x_812_ = lean_nat_add(v___x_811_, v_size_783_);
                leanh::lean_dec(v_size_783_);
                if leanh::lean_obj_tag(v_l_802_) == 0 {
                    v_size_833_ = leanh::lean_ctor_get(v_l_802_, 0);
                    leanh::lean_inc(v_size_833_);
                    v___y_825_ = v_size_833_;
                    state = 29;
                    continue;
                } else {
                    v___x_834_ = leanh::lean_unsigned_to_nat(0);
                    v___y_825_ = v___x_834_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_817_ = lean_nat_add(v___y_814_, v___y_816_);
                leanh::lean_dec(v___y_816_);
                leanh::lean_dec(v___y_814_);
                if v_isShared_810_ == 0 {
                    leanh::lean_ctor_set(v___x_809_, 4, v_r_787_);
                    leanh::lean_ctor_set(v___x_809_, 3, v_r_803_);
                    leanh::lean_ctor_set(v___x_809_, 2, v_v_785_);
                    leanh::lean_ctor_set(v___x_809_, 1, v_k_784_);
                    leanh::lean_ctor_set(v___x_809_, 0, v___x_817_);
                    v___x_819_ = v___x_809_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 3, v_r_803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 4, v_r_787_);
                    v___x_819_ = v_reuseFailAlloc_823_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_798_ == 0 {
                    leanh::lean_ctor_set(v___x_797_, 4, v___x_819_);
                    leanh::lean_ctor_set(v___x_797_, 3, v___y_815_);
                    leanh::lean_ctor_set(v___x_797_, 2, v_v_801_);
                    leanh::lean_ctor_set(v___x_797_, 1, v_k_800_);
                    leanh::lean_ctor_set(v___x_797_, 0, v___x_812_);
                    v___x_821_ = v___x_797_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 3, v___y_815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 4, v___x_819_);
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
                leanh::lean_dec(v___y_825_);
                leanh::lean_dec(v___x_811_);
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v_l_802_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_826_);
                    v___x_828_ = v___x_637_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 3, v_l_634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 4, v_l_802_);
                    v___x_828_ = v_reuseFailAlloc_832_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_829_ = lean_nat_add(v___x_781_, v_size_804_);
                if leanh::lean_obj_tag(v_r_803_) == 0 {
                    v_size_830_ = leanh::lean_ctor_get(v_r_803_, 0);
                    leanh::lean_inc(v_size_830_);
                    v___y_814_ = v___x_829_;
                    v___y_815_ = v___x_828_;
                    v___y_816_ = v_size_830_;
                    state = 26;
                    continue;
                } else {
                    v___x_831_ = leanh::lean_unsigned_to_nat(0);
                    v___y_814_ = v___x_829_;
                    v___y_815_ = v___x_828_;
                    v___y_816_ = v___x_831_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_852_ = (!leanh::lean_is_exclusive(v_l_634_)) as u8;
                if v_isSharedCheck_852_ == 0 {
                    v_unused_853_ = leanh::lean_ctor_get(v_l_634_, 4);
                    leanh::lean_dec(v_unused_853_);
                    v_unused_854_ = leanh::lean_ctor_get(v_l_634_, 3);
                    leanh::lean_dec(v_unused_854_);
                    v_unused_855_ = leanh::lean_ctor_get(v_l_634_, 2);
                    leanh::lean_dec(v_unused_855_);
                    v_unused_856_ = leanh::lean_ctor_get(v_l_634_, 1);
                    leanh::lean_dec(v_unused_856_);
                    v_unused_857_ = leanh::lean_ctor_get(v_l_634_, 0);
                    leanh::lean_dec(v_unused_857_);
                    v___x_847_ = v_l_634_;
                    v_isShared_848_ = v_isSharedCheck_852_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_634_);
                    v___x_847_ = leanh::lean_box(0);
                    v_isShared_848_ = v_isSharedCheck_852_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_848_ == 0 {
                    leanh::lean_ctor_set(v___x_847_, 4, v_r_787_);
                    leanh::lean_ctor_set(v___x_847_, 3, v___x_845_);
                    leanh::lean_ctor_set(v___x_847_, 2, v_v_785_);
                    leanh::lean_ctor_set(v___x_847_, 1, v_k_784_);
                    leanh::lean_ctor_set(v___x_847_, 0, v___x_842_);
                    v___x_850_ = v___x_847_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_851_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 3, v___x_845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 4, v_r_787_);
                    v___x_850_ = v_reuseFailAlloc_851_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_850_;
            }
            34 => {
                v_k_872_ = leanh::lean_ctor_get(v_l_865_, 1);
                v_v_873_ = leanh::lean_ctor_get(v_l_865_, 2);
                v_isSharedCheck_887_ = (!leanh::lean_is_exclusive(v_l_865_)) as u8;
                if v_isSharedCheck_887_ == 0 {
                    v_unused_888_ = leanh::lean_ctor_get(v_l_865_, 4);
                    leanh::lean_dec(v_unused_888_);
                    v_unused_889_ = leanh::lean_ctor_get(v_l_865_, 3);
                    leanh::lean_dec(v_unused_889_);
                    v_unused_890_ = leanh::lean_ctor_get(v_l_865_, 0);
                    leanh::lean_dec(v_unused_890_);
                    v___x_875_ = v_l_865_;
                    v_isShared_876_ = v_isSharedCheck_887_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_873_);
                    leanh::lean_inc(v_k_872_);
                    leanh::lean_dec(v_l_865_);
                    v___x_875_ = leanh::lean_box(0);
                    v_isShared_876_ = v_isSharedCheck_887_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_877_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_866_, 2);
                if v_isShared_876_ == 0 {
                    leanh::lean_ctor_set(v___x_875_, 4, v_r_866_);
                    leanh::lean_ctor_set(v___x_875_, 3, v_r_866_);
                    leanh::lean_ctor_set(v___x_875_, 2, v_v_633_);
                    leanh::lean_ctor_set(v___x_875_, 1, v_k_632_);
                    leanh::lean_ctor_set(v___x_875_, 0, v___x_781_);
                    v___x_879_ = v___x_875_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_886_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_886_, 3, v_r_866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_886_, 4, v_r_866_);
                    v___x_879_ = v_reuseFailAlloc_886_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_866_);
                if v_isShared_871_ == 0 {
                    leanh::lean_ctor_set(v___x_870_, 3, v_r_866_);
                    leanh::lean_ctor_set(v___x_870_, 0, v___x_781_);
                    v___x_881_ = v___x_870_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 3, v_r_866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 4, v_r_866_);
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v___x_881_);
                    leanh::lean_ctor_set(v___x_637_, 3, v___x_879_);
                    leanh::lean_ctor_set(v___x_637_, 2, v_v_873_);
                    leanh::lean_ctor_set(v___x_637_, 1, v_k_872_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_877_);
                    v___x_883_ = v___x_637_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 1, v_k_872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 2, v_v_873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 3, v___x_879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 4, v___x_881_);
                    v___x_883_ = v_reuseFailAlloc_884_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_883_;
            }
            39 => {
                v___x_900_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_899_ == 0 {
                    leanh::lean_ctor_set(v___x_898_, 4, v_l_865_);
                    leanh::lean_ctor_set(v___x_898_, 2, v_v_633_);
                    leanh::lean_ctor_set(v___x_898_, 1, v_k_632_);
                    leanh::lean_ctor_set(v___x_898_, 0, v___x_781_);
                    v___x_902_ = v___x_898_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_906_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_906_, 3, v_l_865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_906_, 4, v_l_865_);
                    v___x_902_ = v_reuseFailAlloc_906_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_638_ == 0 {
                    leanh::lean_ctor_set(v___x_637_, 4, v_r_894_);
                    leanh::lean_ctor_set(v___x_637_, 3, v___x_902_);
                    leanh::lean_ctor_set(v___x_637_, 2, v_v_896_);
                    leanh::lean_ctor_set(v___x_637_, 1, v_k_895_);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_900_);
                    v___x_904_ = v___x_637_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 3, v___x_902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_894_);
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
    mut v_config_919_: *mut leanh::LeanObject,
    mut v_a_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsDir_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgName_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relPkgDir_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configLang_x3f_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_935_: u8 = 0;
    let mut v_updateDeps_936_: u8 = 0;
    let mut v_updateToolchain_937_: u8 = 0;
    let mut v_scope_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_942_: u8 = 0;
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v_facetDecls_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: usize = 0;
    let mut v___x_984_: usize = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut v_a_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_a_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_reuseFailAlloc_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_unused_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_922_ = leanh::lean_ctor_get(v_config_919_, 0);
                v_lakeArgs_x3f_923_ = leanh::lean_ctor_get(v_config_919_, 1);
                v_wsDir_924_ = leanh::lean_ctor_get(v_config_919_, 2);
                v_pkgName_925_ = leanh::lean_ctor_get(v_config_919_, 4);
                v_relPkgDir_926_ = leanh::lean_ctor_get(v_config_919_, 5);
                v_pkgDir_927_ = leanh::lean_ctor_get(v_config_919_, 6);
                v_relConfigFile_928_ = leanh::lean_ctor_get(v_config_919_, 7);
                v_configFile_929_ = leanh::lean_ctor_get(v_config_919_, 8);
                v_configLang_x3f_930_ = leanh::lean_ctor_get(v_config_919_, 9);
                v_relManifestFile_931_ = leanh::lean_ctor_get(v_config_919_, 10);
                v_packageOverrides_932_ = leanh::lean_ctor_get(v_config_919_, 11);
                v_lakeOpts_933_ = leanh::lean_ctor_get(v_config_919_, 12);
                v_leanOpts_934_ = leanh::lean_ctor_get(v_config_919_, 13);
                v_reconfigure_935_ = leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16) as u32,
                );
                v_updateDeps_936_ = leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 1) as u32,
                );
                v_updateToolchain_937_ = leanh::lean_ctor_get_uint8(
                    v_config_919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 2) as u32,
                );
                v_scope_938_ = leanh::lean_ctor_get(v_config_919_, 14);
                v_remoteUrl_939_ = leanh::lean_ctor_get(v_config_919_, 15);
                v_isSharedCheck_1018_ = (!leanh::lean_is_exclusive(v_config_919_)) as u8;
                if v_isSharedCheck_1018_ == 0 {
                    v_unused_1019_ = leanh::lean_ctor_get(v_config_919_, 3);
                    leanh::lean_dec(v_unused_1019_);
                    v___x_941_ = v_config_919_;
                    v_isShared_942_ = v_isSharedCheck_1018_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_remoteUrl_939_);
                    leanh::lean_inc(v_scope_938_);
                    leanh::lean_inc(v_leanOpts_934_);
                    leanh::lean_inc(v_lakeOpts_933_);
                    leanh::lean_inc(v_packageOverrides_932_);
                    leanh::lean_inc(v_relManifestFile_931_);
                    leanh::lean_inc(v_configLang_x3f_930_);
                    leanh::lean_inc(v_configFile_929_);
                    leanh::lean_inc(v_relConfigFile_928_);
                    leanh::lean_inc(v_pkgDir_927_);
                    leanh::lean_inc(v_relPkgDir_926_);
                    leanh::lean_inc(v_pkgName_925_);
                    leanh::lean_inc(v_wsDir_924_);
                    leanh::lean_inc(v_lakeArgs_x3f_923_);
                    leanh::lean_inc(v_lakeEnv_922_);
                    leanh::lean_dec(v_config_919_);
                    v___x_941_ = leanh::lean_box(0);
                    v_isShared_942_ = v_isSharedCheck_1018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_943_ = l_Lean_searchPathRef;
                v___x_944_ = l_Lake_Env_leanSearchPath(v_lakeEnv_922_);
                v___x_945_ = lean_st_ref_set(v___x_943_, v___x_944_);
                leanh::lean_inc_ref(v_lakeEnv_922_);
                v___x_946_ = l_Lake_loadLakeConfig(v_lakeEnv_922_, v_a_920_);
                if leanh::lean_obj_tag(v___x_946_) == 0 {
                    v_a_947_ = leanh::lean_ctor_get(v___x_946_, 0);
                    leanh::lean_inc(v_a_947_);
                    v_a_948_ = leanh::lean_ctor_get(v___x_946_, 1);
                    leanh::lean_inc(v_a_948_);
                    leanh::lean_dec_ref_known(v___x_946_, 2);
                    v___x_949_ = leanh::lean_unsigned_to_nat(0);
                    if v_isShared_942_ == 0 {
                        leanh::lean_ctor_set(v___x_941_, 3, v___x_949_);
                        v___x_951_ = v___x_941_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1008_ = leanh::lean_alloc_ctor(0, 16, (3) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_lakeEnv_922_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_lakeArgs_x3f_923_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_wsDir_924_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 3, v___x_949_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_pkgName_925_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 5, v_relPkgDir_926_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 6, v_pkgDir_927_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            7,
                            v_relConfigFile_928_,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 8, v_configFile_929_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            9,
                            v_configLang_x3f_930_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            10,
                            v_relManifestFile_931_,
                        );
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1008_,
                            11,
                            v_packageOverrides_932_,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 12, v_lakeOpts_933_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 13, v_leanOpts_934_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 14, v_scope_938_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 15, v_remoteUrl_939_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 16) as u32,
                            v_reconfigure_935_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 1) as u32,
                            v_updateDeps_936_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1008_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 2) as u32,
                            v_updateToolchain_937_,
                        );
                        v___x_951_ = v_reuseFailAlloc_1008_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_941_);
                    leanh::lean_dec_ref(v_remoteUrl_939_);
                    leanh::lean_dec_ref(v_scope_938_);
                    leanh::lean_dec_ref(v_leanOpts_934_);
                    leanh::lean_dec(v_lakeOpts_933_);
                    leanh::lean_dec_ref(v_packageOverrides_932_);
                    leanh::lean_dec_ref(v_relManifestFile_931_);
                    leanh::lean_dec(v_configLang_x3f_930_);
                    leanh::lean_dec_ref(v_configFile_929_);
                    leanh::lean_dec_ref(v_relConfigFile_928_);
                    leanh::lean_dec_ref(v_pkgDir_927_);
                    leanh::lean_dec_ref(v_relPkgDir_926_);
                    leanh::lean_dec(v_pkgName_925_);
                    leanh::lean_dec_ref(v_wsDir_924_);
                    leanh::lean_dec(v_lakeArgs_x3f_923_);
                    leanh::lean_dec_ref(v_lakeEnv_922_);
                    v_a_1009_ = leanh::lean_ctor_get(v___x_946_, 0);
                    v_a_1010_ = leanh::lean_ctor_get(v___x_946_, 1);
                    v_isSharedCheck_1017_ = (!leanh::lean_is_exclusive(v___x_946_)) as u8;
                    if v_isSharedCheck_1017_ == 0 {
                        v___x_1012_ = v___x_946_;
                        v_isShared_1013_ = v_isSharedCheck_1017_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1010_);
                        leanh::lean_inc(v_a_1009_);
                        leanh::lean_dec(v___x_946_);
                        v___x_1012_ = leanh::lean_box(0);
                        v_isShared_1013_ = v_isSharedCheck_1017_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_952_ = l_Lake_loadWorkspaceRoot___closed__0;
                v___x_953_ = l_Lake_resolveConfigFile(v___x_952_, v___x_951_, v_a_948_);
                if leanh::lean_obj_tag(v___x_953_) == 0 {
                    v_a_954_ = leanh::lean_ctor_get(v___x_953_, 0);
                    leanh::lean_inc_n(v_a_954_, 2);
                    v_a_955_ = leanh::lean_ctor_get(v___x_953_, 1);
                    leanh::lean_inc(v_a_955_);
                    leanh::lean_dec_ref_known(v___x_953_, 2);
                    v___x_956_ = l_Lake_loadConfigFile___redArg(v_a_954_, v_a_955_);
                    if leanh::lean_obj_tag(v___x_956_) == 0 {
                        v_a_957_ = leanh::lean_ctor_get(v___x_956_, 0);
                        v_a_958_ = leanh::lean_ctor_get(v___x_956_, 1);
                        v_isSharedCheck_989_ = (!leanh::lean_is_exclusive(v___x_956_)) as u8;
                        if v_isSharedCheck_989_ == 0 {
                            v___x_960_ = v___x_956_;
                            v_isShared_961_ = v_isSharedCheck_989_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_958_);
                            leanh::lean_inc(v_a_957_);
                            leanh::lean_dec(v___x_956_);
                            v___x_960_ = leanh::lean_box(0);
                            v_isShared_961_ = v_isSharedCheck_989_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_954_);
                        leanh::lean_dec(v_a_947_);
                        v_a_990_ = leanh::lean_ctor_get(v___x_956_, 0);
                        v_a_991_ = leanh::lean_ctor_get(v___x_956_, 1);
                        v_isSharedCheck_998_ = (!leanh::lean_is_exclusive(v___x_956_)) as u8;
                        if v_isSharedCheck_998_ == 0 {
                            v___x_993_ = v___x_956_;
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_991_);
                            leanh::lean_inc(v_a_990_);
                            leanh::lean_dec(v___x_956_);
                            v___x_993_ = leanh::lean_box(0);
                            v_isShared_994_ = v_isSharedCheck_998_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_947_);
                    v_a_999_ = leanh::lean_ctor_get(v___x_953_, 0);
                    v_a_1000_ = leanh::lean_ctor_get(v___x_953_, 1);
                    v_isSharedCheck_1007_ = (!leanh::lean_is_exclusive(v___x_953_)) as u8;
                    if v_isSharedCheck_1007_ == 0 {
                        v___x_1002_ = v___x_953_;
                        v_isShared_1003_ = v_isSharedCheck_1007_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1000_);
                        leanh::lean_inc(v_a_999_);
                        leanh::lean_dec(v___x_953_);
                        v___x_1002_ = leanh::lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1007_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_facetDecls_962_ = leanh::lean_ctor_get(v_a_957_, 2);
                leanh::lean_inc_ref(v_facetDecls_962_);
                v___x_963_ = l_Lake_mkPackage(v_a_954_, v_a_957_, v___x_949_);
                v___x_979_ = l_Lake_initFacetConfigs;
                v___x_980_ = lean_array_get_size(v_facetDecls_962_);
                v___x_981_ = lean_nat_dec_lt(v___x_949_, v___x_980_);
                if v___x_981_ == 0 {
                    leanh::lean_dec_ref(v_facetDecls_962_);
                    v___y_965_ = v___x_979_;
                    state = 4;
                    continue;
                } else {
                    v___x_982_ = lean_nat_dec_le(v___x_980_, v___x_980_);
                    if v___x_982_ == 0 {
                        if v___x_981_ == 0 {
                            leanh::lean_dec_ref(v_facetDecls_962_);
                            v___y_965_ = v___x_979_;
                            state = 4;
                            continue;
                        } else {
                            v___x_983_ = 0usize;
                            v___x_984_ = lean_usize_of_nat(v___x_980_);
                            v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_962_, v___x_983_, v___x_984_, v___x_979_);
                            leanh::lean_dec_ref(v_facetDecls_962_);
                            v___y_965_ = v___x_985_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_986_ = 0usize;
                        v___x_987_ = lean_usize_of_nat(v___x_980_);
                        v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_962_, v___x_986_, v___x_987_, v___x_979_);
                        leanh::lean_dec_ref(v_facetDecls_962_);
                        v___y_965_ = v___x_988_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v_lakeEnv_966_ = leanh::lean_ctor_get(v_a_954_, 0);
                leanh::lean_inc_ref(v_lakeEnv_966_);
                v_lakeArgs_x3f_967_ = leanh::lean_ctor_get(v_a_954_, 1);
                leanh::lean_inc(v_lakeArgs_x3f_967_);
                leanh::lean_dec(v_a_954_);
                v_keyName_968_ = leanh::lean_ctor_get(v___x_963_, 2);
                leanh::lean_inc(v_keyName_968_);
                leanh::lean_inc_ref_n(v___x_963_, 2);
                v___x_969_ = l_Lake_computeLakeCache(v___x_963_, v_lakeEnv_966_);
                v___x_970_ = leanh::lean_unsigned_to_nat(1);
                v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
                v___x_972_ = lean_array_push(v___x_971_, v___x_963_);
                v___x_973_ = leanh::lean_box(1);
                v___x_974_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_keyName_968_, v___x_963_, v___x_973_);
                v___x_975_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                leanh::lean_ctor_set(v___x_975_, 0, v_lakeEnv_966_);
                leanh::lean_ctor_set(v___x_975_, 1, v_a_947_);
                leanh::lean_ctor_set(v___x_975_, 2, v___x_969_);
                leanh::lean_ctor_set(v___x_975_, 3, v_lakeArgs_x3f_967_);
                leanh::lean_ctor_set(v___x_975_, 4, v___x_972_);
                leanh::lean_ctor_set(v___x_975_, 5, v___x_974_);
                leanh::lean_ctor_set(v___x_975_, 6, v___y_965_);
                if v_isShared_961_ == 0 {
                    leanh::lean_ctor_set(v___x_960_, 0, v___x_975_);
                    v___x_977_ = v___x_960_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_958_);
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
                    v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_990_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_991_);
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
                    v_reuseFailAlloc_1006_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_a_1000_);
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
                    v_reuseFailAlloc_1016_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1010_);
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
    mut v_config_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Lake_loadWorkspaceRoot(v_config_1020_, v_a_1021_);
    return v_res_1023_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0(
    mut v_00_u03b2_1024_: *mut leanh::LeanObject,
    mut v_k_1025_: *mut leanh::LeanObject,
    mut v_v_1026_: *mut leanh::LeanObject,
    mut v_t_1027_: *mut leanh::LeanObject,
    mut v_hl_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(
            v_k_1025_, v_v_1026_, v_t_1027_,
        );
    return v___x_1029_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(
    mut v_as_1030_: *mut leanh::LeanObject,
    mut v_i_1031_: usize,
    mut v_stop_1032_: usize,
    mut v_b_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: usize = 0;
    let mut v___x_1040_: usize = 0;
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
                if v___x_1036_ == 0 {
                    v___x_1037_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
                    leanh::lean_inc_ref(v___y_1034_);
                    leanh::lean_inc(v___x_1037_);
                    v___x_1038_ = leanh::lean_apply_2(
                        v___y_1034_,
                        v___x_1037_,
                        leanh::lean_box(0),
                    );
                    v___x_1039_ = 1usize;
                    v___x_1040_ = lean_usize_add(v_i_1031_, v___x_1039_);
                    v_i_1031_ = v___x_1040_;
                    v_b_1033_ = v___x_1038_;
                    state = 0;
                    continue;
                } else {
                    v___x_1042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1042_, 0, v_b_1033_);
                    return v___x_1042_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(
    mut v_as_1043_: *mut leanh::LeanObject,
    mut v_i_1044_: *mut leanh::LeanObject,
    mut v_stop_1045_: *mut leanh::LeanObject,
    mut v_b_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1049_: usize = 0;
    let mut v_stop_boxed_1050_: usize = 0;
    let mut v_res_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1049_ = leanh::lean_unbox_usize(v_i_1044_);
    leanh::lean_dec(v_i_1044_);
    v_stop_boxed_1050_ = leanh::lean_unbox_usize(v_stop_1045_);
    leanh::lean_dec(v_stop_1045_);
    v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_1043_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1046_, v___y_1047_);
    leanh::lean_dec_ref(v___y_1047_);
    leanh::lean_dec_ref(v_as_1043_);
    return v_res_1051_;
}
pub unsafe fn l_Lake_loadWorkspace(
    mut v_config_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_1062_: u8 = 0;
    let mut v_updateDeps_1063_: u8 = 0;
    let mut v_updateToolchain_1064_: u8 = 0;
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: usize = 0;
    let mut v___x_1102_: usize = 0;
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v___x_1112_: usize = 0;
    let mut v___x_1113_: usize = 0;
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1118_: u8 = 0;
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_a_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: usize = 0;
    let mut v___x_1131_: usize = 0;
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1136_: u8 = 0;
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_packageOverrides_1060_ = leanh::lean_ctor_get(v_config_1054_, 11);
                leanh::lean_inc_ref(v_packageOverrides_1060_);
                v_leanOpts_1061_ = leanh::lean_ctor_get(v_config_1054_, 13);
                leanh::lean_inc_ref(v_leanOpts_1061_);
                v_reconfigure_1062_ = leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16) as u32,
                );
                v_updateDeps_1063_ = leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 1) as u32,
                );
                v_updateToolchain_1064_ = leanh::lean_ctor_get_uint8(
                    v_config_1054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 2) as u32,
                );
                v___x_1065_ = leanh::lean_unsigned_to_nat(0);
                v___x_1066_ = l_Lake_loadWorkspace___closed__0;
                v___x_1067_ = l_Lake_loadWorkspaceRoot(v_config_1054_, v___x_1066_);
                if leanh::lean_obj_tag(v___x_1067_) == 0 {
                    v_a_1068_ = leanh::lean_ctor_get(v___x_1067_, 0);
                    leanh::lean_inc(v_a_1068_);
                    v_a_1069_ = leanh::lean_ctor_get(v___x_1067_, 1);
                    leanh::lean_inc(v_a_1069_);
                    leanh::lean_dec_ref_known(v___x_1067_, 2);
                    v___x_1097_ = lean_array_get_size(v_a_1069_);
                    v___x_1098_ = lean_nat_dec_lt(v___x_1065_, v___x_1097_);
                    if v___x_1098_ == 0 {
                        leanh::lean_dec(v_a_1069_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1099_ = leanh::lean_box(0);
                        v___x_1100_ = lean_nat_dec_le(v___x_1097_, v___x_1097_);
                        if v___x_1100_ == 0 {
                            if v___x_1098_ == 0 {
                                leanh::lean_dec(v_a_1069_);
                                state = 2;
                                continue;
                            } else {
                                v___x_1101_ = 0usize;
                                v___x_1102_ = lean_usize_of_nat(v___x_1097_);
                                v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1069_, v___x_1101_, v___x_1102_, v___x_1099_, v_a_1055_);
                                leanh::lean_dec(v_a_1069_);
                                if leanh::lean_obj_tag(v___x_1103_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1103_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_1068_);
                                    leanh::lean_dec_ref(v_leanOpts_1061_);
                                    leanh::lean_dec_ref(v_packageOverrides_1060_);
                                    v_a_1104_ = leanh::lean_ctor_get(v___x_1103_, 0);
                                    v_isSharedCheck_1111_ =
                                        (!leanh::lean_is_exclusive(v___x_1103_)) as u8;
                                    if v_isSharedCheck_1111_ == 0 {
                                        v___x_1106_ = v___x_1103_;
                                        v_isShared_1107_ = v_isSharedCheck_1111_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1104_);
                                        leanh::lean_dec(v___x_1103_);
                                        v___x_1106_ = leanh::lean_box(0);
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
                            leanh::lean_dec(v_a_1069_);
                            if leanh::lean_obj_tag(v___x_1114_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1114_, 1);
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_1068_);
                                leanh::lean_dec_ref(v_leanOpts_1061_);
                                leanh::lean_dec_ref(v_packageOverrides_1060_);
                                v_a_1115_ = leanh::lean_ctor_get(v___x_1114_, 0);
                                v_isSharedCheck_1122_ =
                                    (!leanh::lean_is_exclusive(v___x_1114_)) as u8;
                                if v_isSharedCheck_1122_ == 0 {
                                    v___x_1117_ = v___x_1114_;
                                    v_isShared_1118_ = v_isSharedCheck_1122_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1115_);
                                    leanh::lean_dec(v___x_1114_);
                                    v___x_1117_ = leanh::lean_box(0);
                                    v_isShared_1118_ = v_isSharedCheck_1122_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_leanOpts_1061_);
                    leanh::lean_dec_ref(v_packageOverrides_1060_);
                    v_a_1123_ = leanh::lean_ctor_get(v___x_1067_, 1);
                    leanh::lean_inc(v_a_1123_);
                    leanh::lean_dec_ref_known(v___x_1067_, 2);
                    v___x_1124_ = lean_array_get_size(v_a_1123_);
                    v___x_1125_ = lean_nat_dec_lt(v___x_1065_, v___x_1124_);
                    if v___x_1125_ == 0 {
                        leanh::lean_dec(v_a_1123_);
                        v___x_1126_ = leanh::lean_box(0);
                        v___x_1127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
                        return v___x_1127_;
                    } else {
                        v___x_1128_ = leanh::lean_box(0);
                        v___x_1129_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
                        if v___x_1129_ == 0 {
                            if v___x_1125_ == 0 {
                                leanh::lean_dec(v_a_1123_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1130_ = 0usize;
                                v___x_1131_ = lean_usize_of_nat(v___x_1124_);
                                v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1123_, v___x_1130_, v___x_1131_, v___x_1128_, v_a_1055_);
                                leanh::lean_dec(v_a_1123_);
                                if leanh::lean_obj_tag(v___x_1132_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1132_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_1133_ = leanh::lean_ctor_get(v___x_1132_, 0);
                                    v_isSharedCheck_1140_ =
                                        (!leanh::lean_is_exclusive(v___x_1132_)) as u8;
                                    if v_isSharedCheck_1140_ == 0 {
                                        v___x_1135_ = v___x_1132_;
                                        v_isShared_1136_ = v_isSharedCheck_1140_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1133_);
                                        leanh::lean_dec(v___x_1132_);
                                        v___x_1135_ = leanh::lean_box(0);
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
                            leanh::lean_dec(v_a_1123_);
                            if leanh::lean_obj_tag(v___x_1143_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1143_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_1144_ = leanh::lean_ctor_get(v___x_1143_, 0);
                                v_isSharedCheck_1151_ =
                                    (!leanh::lean_is_exclusive(v___x_1143_)) as u8;
                                if v_isSharedCheck_1151_ == 0 {
                                    v___x_1146_ = v___x_1143_;
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1144_);
                                    leanh::lean_dec(v___x_1143_);
                                    v___x_1146_ = leanh::lean_box(0);
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
                v___x_1058_ = leanh::lean_box(0);
                v___x_1059_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1059_, 0, v___x_1058_);
                return v___x_1059_;
            }
            2 => {
                if v_updateDeps_1063_ == 0 {
                    v_packages_1071_ = leanh::lean_ctor_get(v_a_1068_, 4);
                    v___x_1072_ = lean_array_fget_borrowed(v_packages_1071_, v___x_1065_);
                    v_dir_1073_ = leanh::lean_ctor_get(v___x_1072_, 4);
                    v_relManifestFile_1074_ = leanh::lean_ctor_get(v___x_1072_, 9);
                    leanh::lean_inc_ref(v_relManifestFile_1074_);
                    leanh::lean_inc_ref(v_dir_1073_);
                    v___x_1075_ = l_Lake_joinRelative(v_dir_1073_, v_relManifestFile_1074_);
                    v___x_1076_ = l_Lake_Manifest_load_x3f(v___x_1075_);
                    if leanh::lean_obj_tag(v___x_1076_) == 0 {
                        v_a_1077_ = leanh::lean_ctor_get(v___x_1076_, 0);
                        leanh::lean_inc(v_a_1077_);
                        leanh::lean_dec_ref_known(v___x_1076_, 1);
                        if leanh::lean_obj_tag(v_a_1077_) == 1 {
                            v_val_1078_ = leanh::lean_ctor_get(v_a_1077_, 0);
                            leanh::lean_inc(v_val_1078_);
                            leanh::lean_dec_ref_known(v_a_1077_, 1);
                            v___x_1079_ = l_Lake_Workspace_materializeDeps(
                                v_a_1068_,
                                v_val_1078_,
                                v_leanOpts_1061_,
                                v_reconfigure_1062_,
                                v_packageOverrides_1060_,
                                v_a_1055_,
                            );
                            leanh::lean_dec_ref(v_packageOverrides_1060_);
                            return v___x_1079_;
                        } else {
                            leanh::lean_dec(v_a_1077_);
                            leanh::lean_dec_ref(v_packageOverrides_1060_);
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
                        leanh::lean_dec(v_a_1068_);
                        leanh::lean_dec_ref(v_leanOpts_1061_);
                        leanh::lean_dec_ref(v_packageOverrides_1060_);
                        v_a_1082_ = leanh::lean_ctor_get(v___x_1076_, 0);
                        v_isSharedCheck_1094_ =
                            (!leanh::lean_is_exclusive(v___x_1076_)) as u8;
                        if v_isSharedCheck_1094_ == 0 {
                            v___x_1084_ = v___x_1076_;
                            v_isShared_1085_ = v_isSharedCheck_1094_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1082_);
                            leanh::lean_dec(v___x_1076_);
                            v___x_1084_ = leanh::lean_box(0);
                            v_isShared_1085_ = v_isSharedCheck_1094_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_packageOverrides_1060_);
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
                v___x_1088_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1088_, 0, v___x_1086_);
                leanh::lean_ctor_set_uint8(
                    v___x_1088_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1087_,
                );
                leanh::lean_inc_ref(v_a_1055_);
                v___x_1089_ =
                    leanh::lean_apply_2(v_a_1055_, v___x_1088_, leanh::lean_box(0));
                v___x_1090_ = leanh::lean_box(0);
                if v_isShared_1085_ == 0 {
                    leanh::lean_ctor_set(v___x_1084_, 0, v___x_1090_);
                    v___x_1092_ = v___x_1084_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
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
                    v_reuseFailAlloc_1110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
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
                    v_reuseFailAlloc_1121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
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
                    v_reuseFailAlloc_1139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
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
                    v_reuseFailAlloc_1150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
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
    mut v_config_1152_: *mut leanh::LeanObject,
    mut v_a_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lake_loadWorkspace(v_config_1152_, v_a_1153_);
    leanh::lean_dec_ref(v_a_1153_);
    return v_res_1155_;
}
pub unsafe fn l_Lake_updateManifest(
    mut v_config_1156_: *mut leanh::LeanObject,
    mut v_toUpdate_1157_: *mut leanh::LeanObject,
    mut v_a_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateToolchain_1164_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_unused_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: usize = 0;
    let mut v___x_1194_: usize = 0;
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: usize = 0;
    let mut v___x_1210_: usize = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_leanOpts_1163_ = leanh::lean_ctor_get(v_config_1156_, 13);
                leanh::lean_inc_ref(v_leanOpts_1163_);
                v_updateToolchain_1164_ = leanh::lean_ctor_get_uint8(
                    v_config_1156_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 16 + 2) as u32,
                );
                v___x_1165_ = leanh::lean_unsigned_to_nat(0);
                v___x_1166_ = l_Lake_loadWorkspace___closed__0;
                v___x_1167_ = l_Lake_loadWorkspaceRoot(v_config_1156_, v___x_1166_);
                if leanh::lean_obj_tag(v___x_1167_) == 0 {
                    v_a_1168_ = leanh::lean_ctor_get(v___x_1167_, 0);
                    leanh::lean_inc(v_a_1168_);
                    v_a_1169_ = leanh::lean_ctor_get(v___x_1167_, 1);
                    leanh::lean_inc(v_a_1169_);
                    leanh::lean_dec_ref_known(v___x_1167_, 2);
                    v___x_1189_ = lean_array_get_size(v_a_1169_);
                    v___x_1190_ = lean_nat_dec_lt(v___x_1165_, v___x_1189_);
                    if v___x_1190_ == 0 {
                        leanh::lean_dec(v_a_1169_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1191_ = leanh::lean_box(0);
                        v___x_1192_ = lean_nat_dec_le(v___x_1189_, v___x_1189_);
                        if v___x_1192_ == 0 {
                            if v___x_1190_ == 0 {
                                leanh::lean_dec(v_a_1169_);
                                state = 2;
                                continue;
                            } else {
                                v___x_1193_ = 0usize;
                                v___x_1194_ = lean_usize_of_nat(v___x_1189_);
                                v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1169_, v___x_1193_, v___x_1194_, v___x_1191_, v_a_1158_);
                                leanh::lean_dec(v_a_1169_);
                                if leanh::lean_obj_tag(v___x_1195_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1195_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_1168_);
                                    leanh::lean_dec_ref(v_leanOpts_1163_);
                                    return v___x_1195_;
                                }
                            }
                        } else {
                            v___x_1196_ = 0usize;
                            v___x_1197_ = lean_usize_of_nat(v___x_1189_);
                            v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1169_, v___x_1196_, v___x_1197_, v___x_1191_, v_a_1158_);
                            leanh::lean_dec(v_a_1169_);
                            if leanh::lean_obj_tag(v___x_1198_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1198_, 1);
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_1168_);
                                leanh::lean_dec_ref(v_leanOpts_1163_);
                                return v___x_1198_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_leanOpts_1163_);
                    v_a_1199_ = leanh::lean_ctor_get(v___x_1167_, 1);
                    leanh::lean_inc(v_a_1199_);
                    leanh::lean_dec_ref_known(v___x_1167_, 2);
                    v___x_1200_ = lean_array_get_size(v_a_1199_);
                    v___x_1201_ = lean_nat_dec_lt(v___x_1165_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        leanh::lean_dec(v_a_1199_);
                        v___x_1202_ = leanh::lean_box(0);
                        v___x_1203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1203_, 0, v___x_1202_);
                        return v___x_1203_;
                    } else {
                        v___x_1204_ = leanh::lean_box(0);
                        v___x_1205_ = lean_nat_dec_le(v___x_1200_, v___x_1200_);
                        if v___x_1205_ == 0 {
                            if v___x_1201_ == 0 {
                                leanh::lean_dec(v_a_1199_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1206_ = 0usize;
                                v___x_1207_ = lean_usize_of_nat(v___x_1200_);
                                v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_1199_, v___x_1206_, v___x_1207_, v___x_1204_, v_a_1158_);
                                leanh::lean_dec(v_a_1199_);
                                if leanh::lean_obj_tag(v___x_1208_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1208_, 1);
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
                            leanh::lean_dec(v_a_1199_);
                            if leanh::lean_obj_tag(v___x_1211_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1211_, 1);
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
                v___x_1161_ = leanh::lean_box(0);
                v___x_1162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
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
                if leanh::lean_obj_tag(v___x_1171_) == 0 {
                    v_isSharedCheck_1179_ = (!leanh::lean_is_exclusive(v___x_1171_)) as u8;
                    if v_isSharedCheck_1179_ == 0 {
                        v_unused_1180_ = leanh::lean_ctor_get(v___x_1171_, 0);
                        leanh::lean_dec(v_unused_1180_);
                        v___x_1173_ = v___x_1171_;
                        v_isShared_1174_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1171_);
                        v___x_1173_ = leanh::lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1181_ = leanh::lean_ctor_get(v___x_1171_, 0);
                    v_isSharedCheck_1188_ = (!leanh::lean_is_exclusive(v___x_1171_)) as u8;
                    if v_isSharedCheck_1188_ == 0 {
                        v___x_1183_ = v___x_1171_;
                        v_isShared_1184_ = v_isSharedCheck_1188_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1181_);
                        leanh::lean_dec(v___x_1171_);
                        v___x_1183_ = leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1188_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1175_ = leanh::lean_box(0);
                if v_isShared_1174_ == 0 {
                    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1175_);
                    v___x_1177_ = v___x_1173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
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
                    v_reuseFailAlloc_1187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
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
    mut v_config_1212_: *mut leanh::LeanObject,
    mut v_toUpdate_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Lake_updateManifest(v_config_1212_, v_toUpdate_1213_, v_a_1214_);
    leanh::lean_dec_ref(v_a_1214_);
    leanh::lean_dec(v_toUpdate_1213_);
    return v_res_1216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Workspace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Resolve(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Package(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Toml(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_InitFacets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Workspace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Workspace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Resolve(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Package(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Toml(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_InitFacets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Workspace(builtin);
}
// Lean compiler output
// Module: Lake.Build.Index
// Imports: Lake.Build.Fetch Lake.Config.Monad Lake.Build.Topological Lake.Util.StoreInsts
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_nat_mul, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_task_pure,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lake::Build::Fetch::{
    initialize_Lake_Build_Fetch, l_Lake_buildCycleError, runtime_initialize_Lake_Build_Fetch,
};
use crate::r#gen::Lake::Build::Info::l_Lake_BuildInfo_key;
use crate::r#gen::Lake::Build::Key::{
    l_Lake_BuildKey_quickCmp, l_Lake_BuildKey_toString, l_Lake_instDecidableEqBuildKey_decEq,
};
use crate::r#gen::Lake::Build::Topological::{
    initialize_Lake_Build_Topological, runtime_initialize_Lake_Build_Topological,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lake::Config::FacetConfig::l_Lake_FacetConfigMap_get_x3f;
use crate::r#gen::Lake::Config::Monad::{
    initialize_Lake_Config_Monad, runtime_initialize_Lake_Config_Monad,
};
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::r#gen::Lake::Util::StoreInsts::{
    initialize_Lake_Util_StoreInsts, runtime_initialize_Lake_Util_StoreInsts,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        39, 58, 32, 116, 97, 114, 103, 101, 116, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
        32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 0,
    ],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        39, 58, 32, 105, 110, 112, 117, 116, 32, 116, 97, 114, 103, 101, 116, 32, 105, 115, 32,
        111, 102, 32, 107, 105, 110, 100, 32, 39, 0,
    ],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        39, 44, 32, 98, 117, 116, 32, 102, 97, 99, 101, 116, 32, 101, 120, 112, 101, 99, 116, 115,
        32, 39, 0,
    ],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        39, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 102, 97, 99, 101, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_FetchT_run___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_FetchT_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_FetchT_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(
    mut v_k_660_: *mut leanh::LeanObject,
    mut v_v_661_: *mut leanh::LeanObject,
    mut v_t_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: u8 = 0;
    let mut v_impl_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v_size_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_702_: u8 = 0;
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_728_: u8 = 0;
    let mut v_unused_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v_unused_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_unused_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_773_: u8 = 0;
    let mut v_unused_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v_k_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_unused_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v_unused_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_830_: u8 = 0;
    let mut v_size_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_unused_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_880_: u8 = 0;
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_unused_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v_unused_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v_k_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_919_: u8 = 0;
    let mut v_unused_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v_unused_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_931_: u8 = 0;
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_939_: u8 = 0;
    let mut v_unused_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_662_) == 0 {
                    v_size_663_ = leanh::lean_ctor_get(v_t_662_, 0);
                    v_k_664_ = leanh::lean_ctor_get(v_t_662_, 1);
                    v_v_665_ = leanh::lean_ctor_get(v_t_662_, 2);
                    v_l_666_ = leanh::lean_ctor_get(v_t_662_, 3);
                    v_r_667_ = leanh::lean_ctor_get(v_t_662_, 4);
                    v_isSharedCheck_947_ = (!leanh::lean_is_exclusive(v_t_662_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_669_ = v_t_662_;
                        v_isShared_670_ = v_isSharedCheck_947_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_667_);
                        leanh::lean_inc(v_l_666_);
                        leanh::lean_inc(v_v_665_);
                        leanh::lean_inc(v_k_664_);
                        leanh::lean_inc(v_size_663_);
                        leanh::lean_dec(v_t_662_);
                        v___x_669_ = leanh::lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_947_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_948_ = leanh::lean_unsigned_to_nat(1);
                    v___x_949_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_949_, 0, v___x_948_);
                    leanh::lean_ctor_set(v___x_949_, 1, v_k_660_);
                    leanh::lean_ctor_set(v___x_949_, 2, v_v_661_);
                    leanh::lean_ctor_set(v___x_949_, 3, v_t_662_);
                    leanh::lean_ctor_set(v___x_949_, 4, v_t_662_);
                    return v___x_949_;
                }
            }
            1 => {
                v___x_671_ = l_Lake_BuildKey_quickCmp(v_k_660_, v_k_664_);
                match v___x_671_ {
                    0 => {
                        leanh::lean_dec(v_size_663_);
                        v_impl_672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_660_, v_v_661_, v_l_666_);
                        v___x_673_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_667_) == 0 {
                            v_size_674_ = leanh::lean_ctor_get(v_r_667_, 0);
                            v_size_675_ = leanh::lean_ctor_get(v_impl_672_, 0);
                            leanh::lean_inc(v_size_675_);
                            v_k_676_ = leanh::lean_ctor_get(v_impl_672_, 1);
                            leanh::lean_inc(v_k_676_);
                            v_v_677_ = leanh::lean_ctor_get(v_impl_672_, 2);
                            leanh::lean_inc(v_v_677_);
                            v_l_678_ = leanh::lean_ctor_get(v_impl_672_, 3);
                            leanh::lean_inc(v_l_678_);
                            v_r_679_ = leanh::lean_ctor_get(v_impl_672_, 4);
                            leanh::lean_inc(v_r_679_);
                            v___x_680_ = leanh::lean_unsigned_to_nat(3);
                            v___x_681_ = lean_nat_mul(v___x_680_, v_size_674_);
                            v___x_682_ = lean_nat_dec_lt(v___x_681_, v_size_675_);
                            leanh::lean_dec(v___x_681_);
                            if v___x_682_ == 0 {
                                leanh::lean_dec(v_r_679_);
                                leanh::lean_dec(v_l_678_);
                                leanh::lean_dec(v_v_677_);
                                leanh::lean_dec(v_k_676_);
                                v___x_683_ = lean_nat_add(v___x_673_, v_size_675_);
                                leanh::lean_dec(v_size_675_);
                                v___x_684_ = lean_nat_add(v___x_683_, v_size_674_);
                                leanh::lean_dec(v___x_683_);
                                if v_isShared_670_ == 0 {
                                    leanh::lean_ctor_set(v___x_669_, 3, v_impl_672_);
                                    leanh::lean_ctor_set(v___x_669_, 0, v___x_684_);
                                    v___x_686_ = v___x_669_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_687_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_687_,
                                        0,
                                        v___x_684_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_687_, 1, v_k_664_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_687_, 2, v_v_665_);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_687_,
                                        3,
                                        v_impl_672_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_687_, 4, v_r_667_);
                                    v___x_686_ = v_reuseFailAlloc_687_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_753_ =
                                    (!leanh::lean_is_exclusive(v_impl_672_)) as u8;
                                if v_isSharedCheck_753_ == 0 {
                                    v_unused_754_ = leanh::lean_ctor_get(v_impl_672_, 4);
                                    leanh::lean_dec(v_unused_754_);
                                    v_unused_755_ = leanh::lean_ctor_get(v_impl_672_, 3);
                                    leanh::lean_dec(v_unused_755_);
                                    v_unused_756_ = leanh::lean_ctor_get(v_impl_672_, 2);
                                    leanh::lean_dec(v_unused_756_);
                                    v_unused_757_ = leanh::lean_ctor_get(v_impl_672_, 1);
                                    leanh::lean_dec(v_unused_757_);
                                    v_unused_758_ = leanh::lean_ctor_get(v_impl_672_, 0);
                                    leanh::lean_dec(v_unused_758_);
                                    v___x_689_ = v_impl_672_;
                                    v_isShared_690_ = v_isSharedCheck_753_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_672_);
                                    v___x_689_ = leanh::lean_box(0);
                                    v_isShared_690_ = v_isSharedCheck_753_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_759_ = leanh::lean_ctor_get(v_impl_672_, 3);
                            leanh::lean_inc(v_l_759_);
                            if leanh::lean_obj_tag(v_l_759_) == 0 {
                                v_r_760_ = leanh::lean_ctor_get(v_impl_672_, 4);
                                v_k_761_ = leanh::lean_ctor_get(v_impl_672_, 1);
                                v_v_762_ = leanh::lean_ctor_get(v_impl_672_, 2);
                                v_isSharedCheck_773_ =
                                    (!leanh::lean_is_exclusive(v_impl_672_)) as u8;
                                if v_isSharedCheck_773_ == 0 {
                                    v_unused_774_ = leanh::lean_ctor_get(v_impl_672_, 3);
                                    leanh::lean_dec(v_unused_774_);
                                    v_unused_775_ = leanh::lean_ctor_get(v_impl_672_, 0);
                                    leanh::lean_dec(v_unused_775_);
                                    v___x_764_ = v_impl_672_;
                                    v_isShared_765_ = v_isSharedCheck_773_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_760_);
                                    leanh::lean_inc(v_v_762_);
                                    leanh::lean_inc(v_k_761_);
                                    leanh::lean_dec(v_impl_672_);
                                    v___x_764_ = leanh::lean_box(0);
                                    v_isShared_765_ = v_isSharedCheck_773_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_776_ = leanh::lean_ctor_get(v_impl_672_, 4);
                                leanh::lean_inc(v_r_776_);
                                if leanh::lean_obj_tag(v_r_776_) == 0 {
                                    v_k_777_ = leanh::lean_ctor_get(v_impl_672_, 1);
                                    v_v_778_ = leanh::lean_ctor_get(v_impl_672_, 2);
                                    v_isSharedCheck_801_ =
                                        (!leanh::lean_is_exclusive(v_impl_672_)) as u8;
                                    if v_isSharedCheck_801_ == 0 {
                                        v_unused_802_ = leanh::lean_ctor_get(v_impl_672_, 4);
                                        leanh::lean_dec(v_unused_802_);
                                        v_unused_803_ = leanh::lean_ctor_get(v_impl_672_, 3);
                                        leanh::lean_dec(v_unused_803_);
                                        v_unused_804_ = leanh::lean_ctor_get(v_impl_672_, 0);
                                        leanh::lean_dec(v_unused_804_);
                                        v___x_780_ = v_impl_672_;
                                        v_isShared_781_ = v_isSharedCheck_801_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_778_);
                                        leanh::lean_inc(v_k_777_);
                                        leanh::lean_dec(v_impl_672_);
                                        v___x_780_ = leanh::lean_box(0);
                                        v_isShared_781_ = v_isSharedCheck_801_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_805_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_670_ == 0 {
                                        leanh::lean_ctor_set(v___x_669_, 4, v_r_776_);
                                        leanh::lean_ctor_set(v___x_669_, 3, v_impl_672_);
                                        leanh::lean_ctor_set(v___x_669_, 0, v___x_805_);
                                        v___x_807_ = v___x_669_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_808_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_808_,
                                            0,
                                            v___x_805_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_808_,
                                            1,
                                            v_k_664_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_808_,
                                            2,
                                            v_v_665_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_808_,
                                            3,
                                            v_impl_672_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_808_,
                                            4,
                                            v_r_776_,
                                        );
                                        v___x_807_ = v_reuseFailAlloc_808_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_665_);
                        leanh::lean_dec(v_k_664_);
                        if v_isShared_670_ == 0 {
                            leanh::lean_ctor_set(v___x_669_, 2, v_v_661_);
                            leanh::lean_ctor_set(v___x_669_, 1, v_k_660_);
                            v___x_810_ = v___x_669_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_811_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_811_, 0, v_size_663_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_660_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_661_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_811_, 3, v_l_666_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_811_, 4, v_r_667_);
                            v___x_810_ = v_reuseFailAlloc_811_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_663_);
                        v_impl_812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_660_, v_v_661_, v_r_667_);
                        v___x_813_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_666_) == 0 {
                            v_size_814_ = leanh::lean_ctor_get(v_l_666_, 0);
                            v_size_815_ = leanh::lean_ctor_get(v_impl_812_, 0);
                            leanh::lean_inc(v_size_815_);
                            v_k_816_ = leanh::lean_ctor_get(v_impl_812_, 1);
                            leanh::lean_inc(v_k_816_);
                            v_v_817_ = leanh::lean_ctor_get(v_impl_812_, 2);
                            leanh::lean_inc(v_v_817_);
                            v_l_818_ = leanh::lean_ctor_get(v_impl_812_, 3);
                            leanh::lean_inc(v_l_818_);
                            v_r_819_ = leanh::lean_ctor_get(v_impl_812_, 4);
                            leanh::lean_inc(v_r_819_);
                            v___x_820_ = leanh::lean_unsigned_to_nat(3);
                            v___x_821_ = lean_nat_mul(v___x_820_, v_size_814_);
                            v___x_822_ = lean_nat_dec_lt(v___x_821_, v_size_815_);
                            leanh::lean_dec(v___x_821_);
                            if v___x_822_ == 0 {
                                leanh::lean_dec(v_r_819_);
                                leanh::lean_dec(v_l_818_);
                                leanh::lean_dec(v_v_817_);
                                leanh::lean_dec(v_k_816_);
                                v___x_823_ = lean_nat_add(v___x_813_, v_size_814_);
                                v___x_824_ = lean_nat_add(v___x_823_, v_size_815_);
                                leanh::lean_dec(v_size_815_);
                                leanh::lean_dec(v___x_823_);
                                if v_isShared_670_ == 0 {
                                    leanh::lean_ctor_set(v___x_669_, 4, v_impl_812_);
                                    leanh::lean_ctor_set(v___x_669_, 0, v___x_824_);
                                    v___x_826_ = v___x_669_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_827_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_827_,
                                        0,
                                        v___x_824_,
                                    );
                                    leanh::lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_664_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_665_);
                                    leanh::lean_ctor_set(v_reuseFailAlloc_827_, 3, v_l_666_);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_827_,
                                        4,
                                        v_impl_812_,
                                    );
                                    v___x_826_ = v_reuseFailAlloc_827_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_891_ =
                                    (!leanh::lean_is_exclusive(v_impl_812_)) as u8;
                                if v_isSharedCheck_891_ == 0 {
                                    v_unused_892_ = leanh::lean_ctor_get(v_impl_812_, 4);
                                    leanh::lean_dec(v_unused_892_);
                                    v_unused_893_ = leanh::lean_ctor_get(v_impl_812_, 3);
                                    leanh::lean_dec(v_unused_893_);
                                    v_unused_894_ = leanh::lean_ctor_get(v_impl_812_, 2);
                                    leanh::lean_dec(v_unused_894_);
                                    v_unused_895_ = leanh::lean_ctor_get(v_impl_812_, 1);
                                    leanh::lean_dec(v_unused_895_);
                                    v_unused_896_ = leanh::lean_ctor_get(v_impl_812_, 0);
                                    leanh::lean_dec(v_unused_896_);
                                    v___x_829_ = v_impl_812_;
                                    v_isShared_830_ = v_isSharedCheck_891_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_812_);
                                    v___x_829_ = leanh::lean_box(0);
                                    v_isShared_830_ = v_isSharedCheck_891_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_897_ = leanh::lean_ctor_get(v_impl_812_, 3);
                            leanh::lean_inc(v_l_897_);
                            if leanh::lean_obj_tag(v_l_897_) == 0 {
                                v_r_898_ = leanh::lean_ctor_get(v_impl_812_, 4);
                                v_k_899_ = leanh::lean_ctor_get(v_impl_812_, 1);
                                v_v_900_ = leanh::lean_ctor_get(v_impl_812_, 2);
                                v_isSharedCheck_923_ =
                                    (!leanh::lean_is_exclusive(v_impl_812_)) as u8;
                                if v_isSharedCheck_923_ == 0 {
                                    v_unused_924_ = leanh::lean_ctor_get(v_impl_812_, 3);
                                    leanh::lean_dec(v_unused_924_);
                                    v_unused_925_ = leanh::lean_ctor_get(v_impl_812_, 0);
                                    leanh::lean_dec(v_unused_925_);
                                    v___x_902_ = v_impl_812_;
                                    v_isShared_903_ = v_isSharedCheck_923_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_898_);
                                    leanh::lean_inc(v_v_900_);
                                    leanh::lean_inc(v_k_899_);
                                    leanh::lean_dec(v_impl_812_);
                                    v___x_902_ = leanh::lean_box(0);
                                    v_isShared_903_ = v_isSharedCheck_923_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_926_ = leanh::lean_ctor_get(v_impl_812_, 4);
                                leanh::lean_inc(v_r_926_);
                                if leanh::lean_obj_tag(v_r_926_) == 0 {
                                    v_k_927_ = leanh::lean_ctor_get(v_impl_812_, 1);
                                    v_v_928_ = leanh::lean_ctor_get(v_impl_812_, 2);
                                    v_isSharedCheck_939_ =
                                        (!leanh::lean_is_exclusive(v_impl_812_)) as u8;
                                    if v_isSharedCheck_939_ == 0 {
                                        v_unused_940_ = leanh::lean_ctor_get(v_impl_812_, 4);
                                        leanh::lean_dec(v_unused_940_);
                                        v_unused_941_ = leanh::lean_ctor_get(v_impl_812_, 3);
                                        leanh::lean_dec(v_unused_941_);
                                        v_unused_942_ = leanh::lean_ctor_get(v_impl_812_, 0);
                                        leanh::lean_dec(v_unused_942_);
                                        v___x_930_ = v_impl_812_;
                                        v_isShared_931_ = v_isSharedCheck_939_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_928_);
                                        leanh::lean_inc(v_k_927_);
                                        leanh::lean_dec(v_impl_812_);
                                        v___x_930_ = leanh::lean_box(0);
                                        v_isShared_931_ = v_isSharedCheck_939_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_943_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_670_ == 0 {
                                        leanh::lean_ctor_set(v___x_669_, 4, v_impl_812_);
                                        leanh::lean_ctor_set(v___x_669_, 3, v_r_926_);
                                        leanh::lean_ctor_set(v___x_669_, 0, v___x_943_);
                                        v___x_945_ = v___x_669_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_946_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_946_,
                                            0,
                                            v___x_943_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_946_,
                                            1,
                                            v_k_664_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_946_,
                                            2,
                                            v_v_665_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_946_,
                                            3,
                                            v_r_926_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_946_,
                                            4,
                                            v_impl_812_,
                                        );
                                        v___x_945_ = v_reuseFailAlloc_946_;
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
                return v___x_686_;
            }
            3 => {
                v_size_691_ = leanh::lean_ctor_get(v_l_678_, 0);
                v_size_692_ = leanh::lean_ctor_get(v_r_679_, 0);
                v_k_693_ = leanh::lean_ctor_get(v_r_679_, 1);
                v_v_694_ = leanh::lean_ctor_get(v_r_679_, 2);
                v_l_695_ = leanh::lean_ctor_get(v_r_679_, 3);
                v_r_696_ = leanh::lean_ctor_get(v_r_679_, 4);
                v___x_697_ = leanh::lean_unsigned_to_nat(2);
                v___x_698_ = lean_nat_mul(v___x_697_, v_size_691_);
                v___x_699_ = lean_nat_dec_lt(v_size_692_, v___x_698_);
                leanh::lean_dec(v___x_698_);
                if v___x_699_ == 0 {
                    leanh::lean_inc(v_r_696_);
                    leanh::lean_inc(v_l_695_);
                    leanh::lean_inc(v_v_694_);
                    leanh::lean_inc(v_k_693_);
                    v_isSharedCheck_728_ = (!leanh::lean_is_exclusive(v_r_679_)) as u8;
                    if v_isSharedCheck_728_ == 0 {
                        v_unused_729_ = leanh::lean_ctor_get(v_r_679_, 4);
                        leanh::lean_dec(v_unused_729_);
                        v_unused_730_ = leanh::lean_ctor_get(v_r_679_, 3);
                        leanh::lean_dec(v_unused_730_);
                        v_unused_731_ = leanh::lean_ctor_get(v_r_679_, 2);
                        leanh::lean_dec(v_unused_731_);
                        v_unused_732_ = leanh::lean_ctor_get(v_r_679_, 1);
                        leanh::lean_dec(v_unused_732_);
                        v_unused_733_ = leanh::lean_ctor_get(v_r_679_, 0);
                        leanh::lean_dec(v_unused_733_);
                        v___x_701_ = v_r_679_;
                        v_isShared_702_ = v_isSharedCheck_728_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_679_);
                        v___x_701_ = leanh::lean_box(0);
                        v_isShared_702_ = v_isSharedCheck_728_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_669_);
                    v___x_734_ = lean_nat_add(v___x_673_, v_size_675_);
                    leanh::lean_dec(v_size_675_);
                    v___x_735_ = lean_nat_add(v___x_734_, v_size_674_);
                    leanh::lean_dec(v___x_734_);
                    v___x_736_ = lean_nat_add(v___x_673_, v_size_674_);
                    v___x_737_ = lean_nat_add(v___x_736_, v_size_692_);
                    leanh::lean_dec(v___x_736_);
                    leanh::lean_inc_ref(v_r_667_);
                    if v_isShared_690_ == 0 {
                        leanh::lean_ctor_set(v___x_689_, 4, v_r_667_);
                        leanh::lean_ctor_set(v___x_689_, 3, v_r_679_);
                        leanh::lean_ctor_set(v___x_689_, 2, v_v_665_);
                        leanh::lean_ctor_set(v___x_689_, 1, v_k_664_);
                        leanh::lean_ctor_set(v___x_689_, 0, v___x_737_);
                        v___x_739_ = v___x_689_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_752_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_737_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_664_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_665_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 3, v_r_679_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 4, v_r_667_);
                        v___x_739_ = v_reuseFailAlloc_752_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_703_ = lean_nat_add(v___x_673_, v_size_675_);
                leanh::lean_dec(v_size_675_);
                v___x_704_ = lean_nat_add(v___x_703_, v_size_674_);
                leanh::lean_dec(v___x_703_);
                v___x_716_ = lean_nat_add(v___x_673_, v_size_691_);
                if leanh::lean_obj_tag(v_l_695_) == 0 {
                    v_size_726_ = leanh::lean_ctor_get(v_l_695_, 0);
                    leanh::lean_inc(v_size_726_);
                    v___y_718_ = v_size_726_;
                    state = 8;
                    continue;
                } else {
                    v___x_727_ = leanh::lean_unsigned_to_nat(0);
                    v___y_718_ = v___x_727_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_709_ = lean_nat_add(v___y_707_, v___y_708_);
                leanh::lean_dec(v___y_708_);
                leanh::lean_dec(v___y_707_);
                if v_isShared_702_ == 0 {
                    leanh::lean_ctor_set(v___x_701_, 4, v_r_667_);
                    leanh::lean_ctor_set(v___x_701_, 3, v_r_696_);
                    leanh::lean_ctor_set(v___x_701_, 2, v_v_665_);
                    leanh::lean_ctor_set(v___x_701_, 1, v_k_664_);
                    leanh::lean_ctor_set(v___x_701_, 0, v___x_709_);
                    v___x_711_ = v___x_701_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_715_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 3, v_r_696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 4, v_r_667_);
                    v___x_711_ = v_reuseFailAlloc_715_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_690_ == 0 {
                    leanh::lean_ctor_set(v___x_689_, 4, v___x_711_);
                    leanh::lean_ctor_set(v___x_689_, 3, v___y_706_);
                    leanh::lean_ctor_set(v___x_689_, 2, v_v_694_);
                    leanh::lean_ctor_set(v___x_689_, 1, v_k_693_);
                    leanh::lean_ctor_set(v___x_689_, 0, v___x_704_);
                    v___x_713_ = v___x_689_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 1, v_k_693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 2, v_v_694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 3, v___y_706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 4, v___x_711_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_713_;
            }
            8 => {
                v___x_719_ = lean_nat_add(v___x_716_, v___y_718_);
                leanh::lean_dec(v___y_718_);
                leanh::lean_dec(v___x_716_);
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v_l_695_);
                    leanh::lean_ctor_set(v___x_669_, 3, v_l_678_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_677_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_676_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_719_);
                    v___x_721_ = v___x_669_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 1, v_k_676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 2, v_v_677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 3, v_l_678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 4, v_l_695_);
                    v___x_721_ = v_reuseFailAlloc_725_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_722_ = lean_nat_add(v___x_673_, v_size_674_);
                if leanh::lean_obj_tag(v_r_696_) == 0 {
                    v_size_723_ = leanh::lean_ctor_get(v_r_696_, 0);
                    leanh::lean_inc(v_size_723_);
                    v___y_706_ = v___x_721_;
                    v___y_707_ = v___x_722_;
                    v___y_708_ = v_size_723_;
                    state = 5;
                    continue;
                } else {
                    v___x_724_ = leanh::lean_unsigned_to_nat(0);
                    v___y_706_ = v___x_721_;
                    v___y_707_ = v___x_722_;
                    v___y_708_ = v___x_724_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_746_ = (!leanh::lean_is_exclusive(v_r_667_)) as u8;
                if v_isSharedCheck_746_ == 0 {
                    v_unused_747_ = leanh::lean_ctor_get(v_r_667_, 4);
                    leanh::lean_dec(v_unused_747_);
                    v_unused_748_ = leanh::lean_ctor_get(v_r_667_, 3);
                    leanh::lean_dec(v_unused_748_);
                    v_unused_749_ = leanh::lean_ctor_get(v_r_667_, 2);
                    leanh::lean_dec(v_unused_749_);
                    v_unused_750_ = leanh::lean_ctor_get(v_r_667_, 1);
                    leanh::lean_dec(v_unused_750_);
                    v_unused_751_ = leanh::lean_ctor_get(v_r_667_, 0);
                    leanh::lean_dec(v_unused_751_);
                    v___x_741_ = v_r_667_;
                    v_isShared_742_ = v_isSharedCheck_746_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_667_);
                    v___x_741_ = leanh::lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_746_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_742_ == 0 {
                    leanh::lean_ctor_set(v___x_741_, 4, v___x_739_);
                    leanh::lean_ctor_set(v___x_741_, 3, v_l_678_);
                    leanh::lean_ctor_set(v___x_741_, 2, v_v_677_);
                    leanh::lean_ctor_set(v___x_741_, 1, v_k_676_);
                    leanh::lean_ctor_set(v___x_741_, 0, v___x_735_);
                    v___x_744_ = v___x_741_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 3, v_l_678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 4, v___x_739_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_744_;
            }
            13 => {
                v___x_766_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_760_);
                if v_isShared_765_ == 0 {
                    leanh::lean_ctor_set(v___x_764_, 3, v_r_760_);
                    leanh::lean_ctor_set(v___x_764_, 2, v_v_665_);
                    leanh::lean_ctor_set(v___x_764_, 1, v_k_664_);
                    leanh::lean_ctor_set(v___x_764_, 0, v___x_673_);
                    v___x_768_ = v___x_764_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_772_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 3, v_r_760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_760_);
                    v___x_768_ = v_reuseFailAlloc_772_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v___x_768_);
                    leanh::lean_ctor_set(v___x_669_, 3, v_l_759_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_762_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_761_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_766_);
                    v___x_770_ = v___x_669_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_771_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 4, v___x_768_);
                    v___x_770_ = v_reuseFailAlloc_771_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_770_;
            }
            16 => {
                v_k_782_ = leanh::lean_ctor_get(v_r_776_, 1);
                v_v_783_ = leanh::lean_ctor_get(v_r_776_, 2);
                v_isSharedCheck_797_ = (!leanh::lean_is_exclusive(v_r_776_)) as u8;
                if v_isSharedCheck_797_ == 0 {
                    v_unused_798_ = leanh::lean_ctor_get(v_r_776_, 4);
                    leanh::lean_dec(v_unused_798_);
                    v_unused_799_ = leanh::lean_ctor_get(v_r_776_, 3);
                    leanh::lean_dec(v_unused_799_);
                    v_unused_800_ = leanh::lean_ctor_get(v_r_776_, 0);
                    leanh::lean_dec(v_unused_800_);
                    v___x_785_ = v_r_776_;
                    v_isShared_786_ = v_isSharedCheck_797_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_783_);
                    leanh::lean_inc(v_k_782_);
                    leanh::lean_dec(v_r_776_);
                    v___x_785_ = leanh::lean_box(0);
                    v_isShared_786_ = v_isSharedCheck_797_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_787_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_786_ == 0 {
                    leanh::lean_ctor_set(v___x_785_, 4, v_l_759_);
                    leanh::lean_ctor_set(v___x_785_, 3, v_l_759_);
                    leanh::lean_ctor_set(v___x_785_, 2, v_v_778_);
                    leanh::lean_ctor_set(v___x_785_, 1, v_k_777_);
                    leanh::lean_ctor_set(v___x_785_, 0, v___x_673_);
                    v___x_789_ = v___x_785_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 3, v_l_759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 4, v_l_759_);
                    v___x_789_ = v_reuseFailAlloc_796_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_781_ == 0 {
                    leanh::lean_ctor_set(v___x_780_, 4, v_l_759_);
                    leanh::lean_ctor_set(v___x_780_, 2, v_v_665_);
                    leanh::lean_ctor_set(v___x_780_, 1, v_k_664_);
                    leanh::lean_ctor_set(v___x_780_, 0, v___x_673_);
                    v___x_791_ = v___x_780_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 3, v_l_759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 4, v_l_759_);
                    v___x_791_ = v_reuseFailAlloc_795_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v___x_791_);
                    leanh::lean_ctor_set(v___x_669_, 3, v___x_789_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_783_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_782_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_787_);
                    v___x_793_ = v___x_669_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_794_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_794_, 3, v___x_789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_794_, 4, v___x_791_);
                    v___x_793_ = v_reuseFailAlloc_794_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_793_;
            }
            21 => {
                return v___x_807_;
            }
            22 => {
                return v___x_810_;
            }
            23 => {
                return v___x_826_;
            }
            24 => {
                v_size_831_ = leanh::lean_ctor_get(v_l_818_, 0);
                v_k_832_ = leanh::lean_ctor_get(v_l_818_, 1);
                v_v_833_ = leanh::lean_ctor_get(v_l_818_, 2);
                v_l_834_ = leanh::lean_ctor_get(v_l_818_, 3);
                v_r_835_ = leanh::lean_ctor_get(v_l_818_, 4);
                v_size_836_ = leanh::lean_ctor_get(v_r_819_, 0);
                v___x_837_ = leanh::lean_unsigned_to_nat(2);
                v___x_838_ = lean_nat_mul(v___x_837_, v_size_836_);
                v___x_839_ = lean_nat_dec_lt(v_size_831_, v___x_838_);
                leanh::lean_dec(v___x_838_);
                if v___x_839_ == 0 {
                    leanh::lean_inc(v_r_835_);
                    leanh::lean_inc(v_l_834_);
                    leanh::lean_inc(v_v_833_);
                    leanh::lean_inc(v_k_832_);
                    v_isSharedCheck_867_ = (!leanh::lean_is_exclusive(v_l_818_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v_unused_868_ = leanh::lean_ctor_get(v_l_818_, 4);
                        leanh::lean_dec(v_unused_868_);
                        v_unused_869_ = leanh::lean_ctor_get(v_l_818_, 3);
                        leanh::lean_dec(v_unused_869_);
                        v_unused_870_ = leanh::lean_ctor_get(v_l_818_, 2);
                        leanh::lean_dec(v_unused_870_);
                        v_unused_871_ = leanh::lean_ctor_get(v_l_818_, 1);
                        leanh::lean_dec(v_unused_871_);
                        v_unused_872_ = leanh::lean_ctor_get(v_l_818_, 0);
                        leanh::lean_dec(v_unused_872_);
                        v___x_841_ = v_l_818_;
                        v_isShared_842_ = v_isSharedCheck_867_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_818_);
                        v___x_841_ = leanh::lean_box(0);
                        v_isShared_842_ = v_isSharedCheck_867_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_669_);
                    v___x_873_ = lean_nat_add(v___x_813_, v_size_814_);
                    v___x_874_ = lean_nat_add(v___x_873_, v_size_815_);
                    leanh::lean_dec(v_size_815_);
                    v___x_875_ = lean_nat_add(v___x_873_, v_size_831_);
                    leanh::lean_dec(v___x_873_);
                    leanh::lean_inc_ref(v_l_666_);
                    if v_isShared_830_ == 0 {
                        leanh::lean_ctor_set(v___x_829_, 4, v_l_818_);
                        leanh::lean_ctor_set(v___x_829_, 3, v_l_666_);
                        leanh::lean_ctor_set(v___x_829_, 2, v_v_665_);
                        leanh::lean_ctor_set(v___x_829_, 1, v_k_664_);
                        leanh::lean_ctor_set(v___x_829_, 0, v___x_875_);
                        v___x_877_ = v___x_829_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_890_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_875_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_664_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_665_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_890_, 3, v_l_666_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_890_, 4, v_l_818_);
                        v___x_877_ = v_reuseFailAlloc_890_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_843_ = lean_nat_add(v___x_813_, v_size_814_);
                v___x_844_ = lean_nat_add(v___x_843_, v_size_815_);
                leanh::lean_dec(v_size_815_);
                if leanh::lean_obj_tag(v_l_834_) == 0 {
                    v_size_865_ = leanh::lean_ctor_get(v_l_834_, 0);
                    leanh::lean_inc(v_size_865_);
                    v___y_857_ = v_size_865_;
                    state = 29;
                    continue;
                } else {
                    v___x_866_ = leanh::lean_unsigned_to_nat(0);
                    v___y_857_ = v___x_866_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_849_ = lean_nat_add(v___y_847_, v___y_848_);
                leanh::lean_dec(v___y_848_);
                leanh::lean_dec(v___y_847_);
                if v_isShared_842_ == 0 {
                    leanh::lean_ctor_set(v___x_841_, 4, v_r_819_);
                    leanh::lean_ctor_set(v___x_841_, 3, v_r_835_);
                    leanh::lean_ctor_set(v___x_841_, 2, v_v_817_);
                    leanh::lean_ctor_set(v___x_841_, 1, v_k_816_);
                    leanh::lean_ctor_set(v___x_841_, 0, v___x_849_);
                    v___x_851_ = v___x_841_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_855_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 3, v_r_835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 4, v_r_819_);
                    v___x_851_ = v_reuseFailAlloc_855_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_830_ == 0 {
                    leanh::lean_ctor_set(v___x_829_, 4, v___x_851_);
                    leanh::lean_ctor_set(v___x_829_, 3, v___y_846_);
                    leanh::lean_ctor_set(v___x_829_, 2, v_v_833_);
                    leanh::lean_ctor_set(v___x_829_, 1, v_k_832_);
                    leanh::lean_ctor_set(v___x_829_, 0, v___x_844_);
                    v___x_853_ = v___x_829_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_854_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_854_, 3, v___y_846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_854_, 4, v___x_851_);
                    v___x_853_ = v_reuseFailAlloc_854_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_853_;
            }
            29 => {
                v___x_858_ = lean_nat_add(v___x_843_, v___y_857_);
                leanh::lean_dec(v___y_857_);
                leanh::lean_dec(v___x_843_);
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v_l_834_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_858_);
                    v___x_860_ = v___x_669_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 3, v_l_666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 4, v_l_834_);
                    v___x_860_ = v_reuseFailAlloc_864_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_861_ = lean_nat_add(v___x_813_, v_size_836_);
                if leanh::lean_obj_tag(v_r_835_) == 0 {
                    v_size_862_ = leanh::lean_ctor_get(v_r_835_, 0);
                    leanh::lean_inc(v_size_862_);
                    v___y_846_ = v___x_860_;
                    v___y_847_ = v___x_861_;
                    v___y_848_ = v_size_862_;
                    state = 26;
                    continue;
                } else {
                    v___x_863_ = leanh::lean_unsigned_to_nat(0);
                    v___y_846_ = v___x_860_;
                    v___y_847_ = v___x_861_;
                    v___y_848_ = v___x_863_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_884_ = (!leanh::lean_is_exclusive(v_l_666_)) as u8;
                if v_isSharedCheck_884_ == 0 {
                    v_unused_885_ = leanh::lean_ctor_get(v_l_666_, 4);
                    leanh::lean_dec(v_unused_885_);
                    v_unused_886_ = leanh::lean_ctor_get(v_l_666_, 3);
                    leanh::lean_dec(v_unused_886_);
                    v_unused_887_ = leanh::lean_ctor_get(v_l_666_, 2);
                    leanh::lean_dec(v_unused_887_);
                    v_unused_888_ = leanh::lean_ctor_get(v_l_666_, 1);
                    leanh::lean_dec(v_unused_888_);
                    v_unused_889_ = leanh::lean_ctor_get(v_l_666_, 0);
                    leanh::lean_dec(v_unused_889_);
                    v___x_879_ = v_l_666_;
                    v_isShared_880_ = v_isSharedCheck_884_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_666_);
                    v___x_879_ = leanh::lean_box(0);
                    v_isShared_880_ = v_isSharedCheck_884_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_880_ == 0 {
                    leanh::lean_ctor_set(v___x_879_, 4, v_r_819_);
                    leanh::lean_ctor_set(v___x_879_, 3, v___x_877_);
                    leanh::lean_ctor_set(v___x_879_, 2, v_v_817_);
                    leanh::lean_ctor_set(v___x_879_, 1, v_k_816_);
                    leanh::lean_ctor_set(v___x_879_, 0, v___x_874_);
                    v___x_882_ = v___x_879_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 1, v_k_816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 2, v_v_817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 3, v___x_877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 4, v_r_819_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_882_;
            }
            34 => {
                v_k_904_ = leanh::lean_ctor_get(v_l_897_, 1);
                v_v_905_ = leanh::lean_ctor_get(v_l_897_, 2);
                v_isSharedCheck_919_ = (!leanh::lean_is_exclusive(v_l_897_)) as u8;
                if v_isSharedCheck_919_ == 0 {
                    v_unused_920_ = leanh::lean_ctor_get(v_l_897_, 4);
                    leanh::lean_dec(v_unused_920_);
                    v_unused_921_ = leanh::lean_ctor_get(v_l_897_, 3);
                    leanh::lean_dec(v_unused_921_);
                    v_unused_922_ = leanh::lean_ctor_get(v_l_897_, 0);
                    leanh::lean_dec(v_unused_922_);
                    v___x_907_ = v_l_897_;
                    v_isShared_908_ = v_isSharedCheck_919_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_905_);
                    leanh::lean_inc(v_k_904_);
                    leanh::lean_dec(v_l_897_);
                    v___x_907_ = leanh::lean_box(0);
                    v_isShared_908_ = v_isSharedCheck_919_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_909_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_898_, 2);
                if v_isShared_908_ == 0 {
                    leanh::lean_ctor_set(v___x_907_, 4, v_r_898_);
                    leanh::lean_ctor_set(v___x_907_, 3, v_r_898_);
                    leanh::lean_ctor_set(v___x_907_, 2, v_v_665_);
                    leanh::lean_ctor_set(v___x_907_, 1, v_k_664_);
                    leanh::lean_ctor_set(v___x_907_, 0, v___x_813_);
                    v___x_911_ = v___x_907_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_918_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 3, v_r_898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 4, v_r_898_);
                    v___x_911_ = v_reuseFailAlloc_918_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_898_);
                if v_isShared_903_ == 0 {
                    leanh::lean_ctor_set(v___x_902_, 3, v_r_898_);
                    leanh::lean_ctor_set(v___x_902_, 0, v___x_813_);
                    v___x_913_ = v___x_902_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_917_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_917_, 3, v_r_898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_917_, 4, v_r_898_);
                    v___x_913_ = v_reuseFailAlloc_917_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v___x_913_);
                    leanh::lean_ctor_set(v___x_669_, 3, v___x_911_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_905_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_904_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_909_);
                    v___x_915_ = v___x_669_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_916_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_916_, 3, v___x_911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_916_, 4, v___x_913_);
                    v___x_915_ = v_reuseFailAlloc_916_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_915_;
            }
            39 => {
                v___x_932_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_931_ == 0 {
                    leanh::lean_ctor_set(v___x_930_, 4, v_l_897_);
                    leanh::lean_ctor_set(v___x_930_, 2, v_v_665_);
                    leanh::lean_ctor_set(v___x_930_, 1, v_k_664_);
                    leanh::lean_ctor_set(v___x_930_, 0, v___x_813_);
                    v___x_934_ = v___x_930_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 3, v_l_897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 4, v_l_897_);
                    v___x_934_ = v_reuseFailAlloc_938_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_670_ == 0 {
                    leanh::lean_ctor_set(v___x_669_, 4, v_r_926_);
                    leanh::lean_ctor_set(v___x_669_, 3, v___x_934_);
                    leanh::lean_ctor_set(v___x_669_, 2, v_v_928_);
                    leanh::lean_ctor_set(v___x_669_, 1, v_k_927_);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_932_);
                    v___x_936_ = v___x_669_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_937_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_937_, 1, v_k_927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_937_, 2, v_v_928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_937_, 3, v___x_934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_937_, 4, v_r_926_);
                    v___x_936_ = v_reuseFailAlloc_937_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_936_;
            }
            42 => {
                return v___x_945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(
    mut v_t_950_: *mut leanh::LeanObject,
    mut v_k_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_950_) == 0 {
                    v_k_952_ = leanh::lean_ctor_get(v_t_950_, 1);
                    v_v_953_ = leanh::lean_ctor_get(v_t_950_, 2);
                    v_l_954_ = leanh::lean_ctor_get(v_t_950_, 3);
                    v_r_955_ = leanh::lean_ctor_get(v_t_950_, 4);
                    v___x_956_ = l_Lake_BuildKey_quickCmp(v_k_951_, v_k_952_);
                    match v___x_956_ {
                        0 => {
                            v_t_950_ = v_l_954_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_953_);
                            v___x_958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_958_, 0, v_v_953_);
                            return v___x_958_;
                        }
                        _ => {
                            v_t_950_ = v_r_955_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_960_ = leanh::lean_box(0);
                    return v___x_960_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(
    mut v_t_961_: *mut leanh::LeanObject,
    mut v_k_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_961_, v_k_962_);
    leanh::lean_dec_ref(v_k_962_);
    leanh::lean_dec(v_t_961_);
    return v_res_963_;
}
pub unsafe fn _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2;
    v___x_969_ = l_Lake_BuildTrace_nil(v___x_968_);
    return v___x_969_;
}
pub unsafe fn l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(
    mut v_info_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
    mut v_a_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
    mut v_a_982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_package_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_989_: u8 = 0;
    let mut v_val_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_job_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetchFn_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_unused_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetchFn_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_memoize_1047_: u8 = 0;
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: u8 = 0;
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_info_976_) == 0 {
                    v_package_984_ = leanh::lean_ctor_get(v_info_976_, 0);
                    v_target_985_ = leanh::lean_ctor_get(v_info_976_, 1);
                    v___x_986_ = l_Lake_Package_findTargetDecl_x3f(v_target_985_, v_package_984_);
                    if leanh::lean_obj_tag(v___x_986_) == 1 {
                        leanh::lean_inc(v_target_985_);
                        leanh::lean_inc_ref(v_package_984_);
                        v_isSharedCheck_1023_ =
                            (!leanh::lean_is_exclusive(v_info_976_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v_unused_1024_ = leanh::lean_ctor_get(v_info_976_, 1);
                            leanh::lean_dec(v_unused_1024_);
                            v_unused_1025_ = leanh::lean_ctor_get(v_info_976_, 0);
                            leanh::lean_dec(v_unused_1025_);
                            v___x_988_ = v_info_976_;
                            v_isShared_989_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_info_976_);
                            v___x_988_ = leanh::lean_box(0);
                            v_isShared_989_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_986_);
                        leanh::lean_dec_ref(v_a_977_);
                        v___x_1026_ =
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4;
                        v___x_1027_ = l_Lake_BuildInfo_key(v_info_976_);
                        v___x_1028_ = l_Lake_BuildKey_toString(v___x_1027_);
                        v___x_1029_ = lean_string_append(v___x_1026_, v___x_1028_);
                        leanh::lean_dec_ref(v___x_1028_);
                        v___x_1030_ =
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5;
                        v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
                        v___x_1032_ = 3;
                        v___x_1033_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1033_, 0, v___x_1031_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1033_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1032_,
                        );
                        v___x_1034_ = lean_array_get_size(v_a_982_);
                        v___x_1035_ = lean_array_push(v_a_982_, v___x_1033_);
                        v___x_1036_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1036_, 0, v___x_1034_);
                        leanh::lean_ctor_set(v___x_1036_, 1, v___x_1035_);
                        return v___x_1036_;
                    }
                } else {
                    v_toContext_1037_ = leanh::lean_ctor_get(v_a_981_, 1);
                    v_target_1038_ = leanh::lean_ctor_get(v_info_976_, 0);
                    v_kind_1039_ = leanh::lean_ctor_get(v_info_976_, 1);
                    v_data_1040_ = leanh::lean_ctor_get(v_info_976_, 2);
                    v_facet_1041_ = leanh::lean_ctor_get(v_info_976_, 3);
                    v_facetConfigs_1042_ = leanh::lean_ctor_get(v_toContext_1037_, 6);
                    v___x_1043_ =
                        l_Lake_FacetConfigMap_get_x3f(v_facet_1041_, v_facetConfigs_1042_);
                    if leanh::lean_obj_tag(v___x_1043_) == 1 {
                        leanh::lean_inc(v_kind_1039_);
                        v_val_1044_ = leanh::lean_ctor_get(v___x_1043_, 0);
                        leanh::lean_inc(v_val_1044_);
                        leanh::lean_dec_ref_known(v___x_1043_, 1);
                        v_kind_1045_ = leanh::lean_ctor_get(v_val_1044_, 0);
                        leanh::lean_inc(v_kind_1045_);
                        v_fetchFn_1046_ = leanh::lean_ctor_get(v_val_1044_, 1);
                        leanh::lean_inc_ref(v_fetchFn_1046_);
                        v_memoize_1047_ = leanh::lean_ctor_get_uint8(
                            v_val_1044_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        leanh::lean_dec(v_val_1044_);
                        v___x_1048_ = lean_name_eq(v_kind_1045_, v_kind_1039_);
                        if v___x_1048_ == 0 {
                            leanh::lean_dec_ref(v_fetchFn_1046_);
                            leanh::lean_dec_ref(v_a_977_);
                            v___x_1049_ =
                                l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4;
                            v___x_1050_ = l_Lake_BuildInfo_key(v_info_976_);
                            v___x_1051_ = l_Lake_BuildKey_toString(v___x_1050_);
                            v___x_1052_ = lean_string_append(v___x_1049_, v___x_1051_);
                            leanh::lean_dec_ref(v___x_1051_);
                            v___x_1053_ =
                                l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6;
                            v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
                            v___x_1055_ = 1;
                            v___x_1056_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_kind_1039_,
                                    v___x_1055_,
                                );
                            v___x_1057_ = lean_string_append(v___x_1054_, v___x_1056_);
                            leanh::lean_dec_ref(v___x_1056_);
                            v___x_1058_ =
                                l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7;
                            v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
                            v___x_1060_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_kind_1045_,
                                    v___x_1055_,
                                );
                            v___x_1061_ = lean_string_append(v___x_1059_, v___x_1060_);
                            leanh::lean_dec_ref(v___x_1060_);
                            v___x_1062_ =
                                l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8;
                            v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
                            v___x_1064_ = 3;
                            v___x_1065_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_1065_, 0, v___x_1063_);
                            leanh::lean_ctor_set_uint8(
                                v___x_1065_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_1064_,
                            );
                            v___x_1066_ = lean_array_get_size(v_a_982_);
                            v___x_1067_ = lean_array_push(v_a_982_, v___x_1065_);
                            v___x_1068_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1068_, 0, v___x_1066_);
                            leanh::lean_ctor_set(v___x_1068_, 1, v___x_1067_);
                            return v___x_1068_;
                        } else {
                            leanh::lean_inc(v_facet_1041_);
                            leanh::lean_inc(v_data_1040_);
                            leanh::lean_inc_ref(v_target_1038_);
                            leanh::lean_dec(v_kind_1045_);
                            leanh::lean_dec(v_kind_1039_);
                            leanh::lean_dec_ref_known(v_info_976_, 4);
                            if v_memoize_1047_ == 0 {
                                leanh::lean_dec(v_facet_1041_);
                                leanh::lean_dec_ref(v_target_1038_);
                                leanh::lean_inc_ref(v_a_981_);
                                leanh::lean_inc(v_a_980_);
                                leanh::lean_inc(v_a_979_);
                                leanh::lean_inc(v_a_978_);
                                v___x_1069_ = leanh::lean_apply_8(
                                    v_fetchFn_1046_,
                                    v_data_1040_,
                                    v_a_977_,
                                    v_a_978_,
                                    v_a_979_,
                                    v_a_980_,
                                    v_a_981_,
                                    v_a_982_,
                                    leanh::lean_box(0),
                                );
                                return v___x_1069_;
                            } else {
                                v___x_1070_ = lean_st_ref_take(v_a_980_);
                                leanh::lean_inc(v___x_1070_);
                                v___x_1071_ = lean_st_ref_set(v_a_980_, v___x_1070_);
                                v___x_1072_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1072_, 0, v_target_1038_);
                                leanh::lean_ctor_set(v___x_1072_, 1, v_facet_1041_);
                                v___x_1073_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_1070_, v___x_1072_);
                                leanh::lean_dec(v___x_1070_);
                                if leanh::lean_obj_tag(v___x_1073_) == 0 {
                                    leanh::lean_inc_ref(v_a_981_);
                                    leanh::lean_inc(v_a_980_);
                                    leanh::lean_inc(v_a_979_);
                                    leanh::lean_inc(v_a_978_);
                                    v___x_1074_ = leanh::lean_apply_8(
                                        v_fetchFn_1046_,
                                        v_data_1040_,
                                        v_a_977_,
                                        v_a_978_,
                                        v_a_979_,
                                        v_a_980_,
                                        v_a_981_,
                                        v_a_982_,
                                        leanh::lean_box(0),
                                    );
                                    if leanh::lean_obj_tag(v___x_1074_) == 0 {
                                        v_a_1075_ = leanh::lean_ctor_get(v___x_1074_, 0);
                                        leanh::lean_inc(v_a_1075_);
                                        v___x_1076_ = lean_st_ref_take(v_a_980_);
                                        v___x_1077_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v___x_1072_, v_a_1075_, v___x_1076_);
                                        v___x_1078_ = lean_st_ref_set(v_a_980_, v___x_1077_);
                                        return v___x_1074_;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_1072_, 2);
                                        return v___x_1074_;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v___x_1072_, 2);
                                    leanh::lean_dec_ref(v_fetchFn_1046_);
                                    leanh::lean_dec(v_data_1040_);
                                    leanh::lean_dec_ref(v_a_977_);
                                    v_val_1079_ = leanh::lean_ctor_get(v___x_1073_, 0);
                                    leanh::lean_inc(v_val_1079_);
                                    leanh::lean_dec_ref_known(v___x_1073_, 1);
                                    v___x_1080_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1080_, 0, v_val_1079_);
                                    leanh::lean_ctor_set(v___x_1080_, 1, v_a_982_);
                                    return v___x_1080_;
                                }
                            }
                        }
                    } else {
                        leanh::lean_inc(v_facet_1041_);
                        leanh::lean_dec(v___x_1043_);
                        leanh::lean_dec_ref(v_a_977_);
                        v___x_1081_ =
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4;
                        v___x_1082_ = l_Lake_BuildInfo_key(v_info_976_);
                        v___x_1083_ = l_Lake_BuildKey_toString(v___x_1082_);
                        v___x_1084_ = lean_string_append(v___x_1081_, v___x_1083_);
                        leanh::lean_dec_ref(v___x_1083_);
                        v___x_1085_ =
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9;
                        v___x_1086_ = lean_string_append(v___x_1084_, v___x_1085_);
                        v___x_1087_ = 1;
                        v___x_1088_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_facet_1041_,
                                v___x_1087_,
                            );
                        v___x_1089_ = lean_string_append(v___x_1086_, v___x_1088_);
                        leanh::lean_dec_ref(v___x_1088_);
                        v___x_1090_ =
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8;
                        v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
                        v___x_1092_ = 3;
                        v___x_1093_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1093_, 0, v___x_1091_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1093_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1092_,
                        );
                        v___x_1094_ = lean_array_get_size(v_a_982_);
                        v___x_1095_ = lean_array_push(v_a_982_, v___x_1093_);
                        v___x_1096_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1096_, 0, v___x_1094_);
                        leanh::lean_ctor_set(v___x_1096_, 1, v___x_1095_);
                        return v___x_1096_;
                    }
                }
            }
            1 => {
                v_val_990_ = leanh::lean_ctor_get(v___x_986_, 0);
                leanh::lean_inc(v_val_990_);
                leanh::lean_dec_ref_known(v___x_986_, 1);
                v_name_991_ = leanh::lean_ctor_get(v_val_990_, 1);
                leanh::lean_inc(v_name_991_);
                v_kind_992_ = leanh::lean_ctor_get(v_val_990_, 2);
                leanh::lean_inc(v_kind_992_);
                v_config_993_ = leanh::lean_ctor_get(v_val_990_, 3);
                leanh::lean_inc(v_config_993_);
                leanh::lean_dec(v_val_990_);
                v___x_994_ = l_Lean_Name_isAnonymous(v_kind_992_);
                if v___x_994_ == 0 {
                    leanh::lean_dec(v_target_985_);
                    leanh::lean_dec_ref(v_a_977_);
                    v___x_995_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_995_, 0, v_package_984_);
                    leanh::lean_ctor_set(v___x_995_, 1, v_name_991_);
                    leanh::lean_ctor_set(v___x_995_, 2, v_config_993_);
                    v___x_996_ = leanh::lean_unsigned_to_nat(0);
                    v___x_997_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0;
                    v___x_998_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1;
                    v___x_999_ = 0;
                    v___x_1000_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once
                        ),
                        _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3,
                    );
                    v___x_1001_ = leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    leanh::lean_ctor_set(v___x_1001_, 0, v___x_997_);
                    leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
                    leanh::lean_ctor_set(v___x_1001_, 2, v___x_996_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_999_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v___x_994_,
                    );
                    if v_isShared_989_ == 0 {
                        leanh::lean_ctor_set(v___x_988_, 1, v___x_1001_);
                        leanh::lean_ctor_set(v___x_988_, 0, v___x_995_);
                        v___x_1003_ = v___x_988_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_995_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1001_);
                        v___x_1003_ = v_reuseFailAlloc_1007_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_kind_992_);
                    leanh::lean_dec(v_name_991_);
                    v_keyName_1008_ = leanh::lean_ctor_get(v_package_984_, 2);
                    v___x_1009_ = lean_st_ref_take(v_a_980_);
                    leanh::lean_inc(v___x_1009_);
                    v___x_1010_ = lean_st_ref_set(v_a_980_, v___x_1009_);
                    leanh::lean_inc(v_keyName_1008_);
                    if v_isShared_989_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_988_, 3);
                        leanh::lean_ctor_set(v___x_988_, 0, v_keyName_1008_);
                        v_key_1012_ = v___x_988_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1022_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_keyName_1008_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_target_985_);
                        v_key_1012_ = v_reuseFailAlloc_1022_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1004_ = lean_task_pure(v___x_1003_);
                v_job_1005_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v_job_1005_, 0, v___x_1004_);
                leanh::lean_ctor_set(v_job_1005_, 1, v_kind_992_);
                leanh::lean_ctor_set(v_job_1005_, 2, v___x_998_);
                leanh::lean_ctor_set_uint8(
                    v_job_1005_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_994_,
                );
                v___x_1006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1006_, 0, v_job_1005_);
                leanh::lean_ctor_set(v___x_1006_, 1, v_a_982_);
                return v___x_1006_;
            }
            3 => {
                v___x_1013_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_1009_, v_key_1012_);
                leanh::lean_dec(v___x_1009_);
                if leanh::lean_obj_tag(v___x_1013_) == 0 {
                    v_fetchFn_1014_ = leanh::lean_ctor_get(v_config_993_, 0);
                    leanh::lean_inc_ref(v_fetchFn_1014_);
                    leanh::lean_dec(v_config_993_);
                    leanh::lean_inc_ref(v_a_981_);
                    leanh::lean_inc(v_a_980_);
                    leanh::lean_inc(v_a_979_);
                    leanh::lean_inc(v_a_978_);
                    v___x_1015_ = leanh::lean_apply_8(
                        v_fetchFn_1014_,
                        v_package_984_,
                        v_a_977_,
                        v_a_978_,
                        v_a_979_,
                        v_a_980_,
                        v_a_981_,
                        v_a_982_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1015_) == 0 {
                        v_a_1016_ = leanh::lean_ctor_get(v___x_1015_, 0);
                        leanh::lean_inc(v_a_1016_);
                        v___x_1017_ = lean_st_ref_take(v_a_980_);
                        v___x_1018_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_key_1012_, v_a_1016_, v___x_1017_);
                        v___x_1019_ = lean_st_ref_set(v_a_980_, v___x_1018_);
                        return v___x_1015_;
                    } else {
                        leanh::lean_dec_ref(v_key_1012_);
                        return v___x_1015_;
                    }
                } else {
                    leanh::lean_dec_ref(v_key_1012_);
                    leanh::lean_dec(v_config_993_);
                    leanh::lean_dec_ref(v_package_984_);
                    leanh::lean_dec_ref(v_a_977_);
                    v_val_1020_ = leanh::lean_ctor_get(v___x_1013_, 0);
                    leanh::lean_inc(v_val_1020_);
                    leanh::lean_dec_ref_known(v___x_1013_, 1);
                    v___x_1021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1021_, 0, v_val_1020_);
                    leanh::lean_ctor_set(v___x_1021_, 1, v_a_982_);
                    return v___x_1021_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(
    mut v_info_1097_: *mut leanh::LeanObject,
    mut v_a_1098_: *mut leanh::LeanObject,
    mut v_a_1099_: *mut leanh::LeanObject,
    mut v_a_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_a_1102_: *mut leanh::LeanObject,
    mut v_a_1103_: *mut leanh::LeanObject,
    mut v_a_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(
        v_info_1097_,
        v_a_1098_,
        v_a_1099_,
        v_a_1100_,
        v_a_1101_,
        v_a_1102_,
        v_a_1103_,
    );
    leanh::lean_dec_ref(v_a_1102_);
    leanh::lean_dec(v_a_1101_);
    leanh::lean_dec(v_a_1100_);
    leanh::lean_dec(v_a_1099_);
    return v_res_1105_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(
    mut v_00_u03b2_1106_: *mut leanh::LeanObject,
    mut v_inst_1107_: *mut leanh::LeanObject,
    mut v_t_1108_: *mut leanh::LeanObject,
    mut v_k_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_1108_, v_k_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(
    mut v_00_u03b2_1111_: *mut leanh::LeanObject,
    mut v_inst_1112_: *mut leanh::LeanObject,
    mut v_t_1113_: *mut leanh::LeanObject,
    mut v_k_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(v_00_u03b2_1111_, v_inst_1112_, v_t_1113_, v_k_1114_);
    leanh::lean_dec_ref(v_k_1114_);
    leanh::lean_dec(v_t_1113_);
    return v_res_1115_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(
    mut v_00_u03b2_1116_: *mut leanh::LeanObject,
    mut v_k_1117_: *mut leanh::LeanObject,
    mut v_v_1118_: *mut leanh::LeanObject,
    mut v_t_1119_: *mut leanh::LeanObject,
    mut v_hl_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_1117_, v_v_1118_, v_t_1119_);
    return v___x_1121_;
}
pub unsafe fn l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(
    mut v_a_1122_: *mut leanh::LeanObject,
    mut v_x_1123_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1124_: u8 = 0;
    let mut v_head_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1123_) == 0 {
                    v___x_1124_ = 0;
                    return v___x_1124_;
                } else {
                    v_head_1125_ = leanh::lean_ctor_get(v_x_1123_, 0);
                    v_tail_1126_ = leanh::lean_ctor_get(v_x_1123_, 1);
                    v___x_1127_ = l_Lake_instDecidableEqBuildKey_decEq(v_a_1122_, v_head_1125_);
                    if v___x_1127_ == 0 {
                        v_x_1123_ = v_tail_1126_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1127_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(
    mut v_a_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1131_: u8 = 0;
    let mut v_r_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_1129_, v_x_1130_);
    leanh::lean_dec(v_x_1130_);
    leanh::lean_dec_ref(v_a_1129_);
    v_r_1132_ = leanh::lean_box((v_res_1131_) as usize);
    return v_r_1132_;
}
pub unsafe fn l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(
    mut v___x_1133_: *mut leanh::LeanObject,
    mut v___x_1134_: u8,
    mut v_a_1135_: *mut leanh::LeanObject,
    mut v_a_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1141_: u8 = 0;
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_head_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v_fst_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1135_) == 0 {
                    v_fst_1137_ = leanh::lean_ctor_get(v_a_1136_, 0);
                    v_snd_1138_ = leanh::lean_ctor_get(v_a_1136_, 1);
                    v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v_a_1136_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1140_ = v_a_1136_;
                        v_isShared_1141_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1138_);
                        leanh::lean_inc(v_fst_1137_);
                        leanh::lean_dec(v_a_1136_);
                        v___x_1140_ = leanh::lean_box(0);
                        v_isShared_1141_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_1148_ = leanh::lean_ctor_get(v_a_1135_, 0);
                    v_tail_1149_ = leanh::lean_ctor_get(v_a_1135_, 1);
                    v_isSharedCheck_1171_ = (!leanh::lean_is_exclusive(v_a_1135_)) as u8;
                    if v_isSharedCheck_1171_ == 0 {
                        v___x_1151_ = v_a_1135_;
                        v_isShared_1152_ = v_isSharedCheck_1171_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1149_);
                        leanh::lean_inc(v_head_1148_);
                        leanh::lean_dec(v_a_1135_);
                        v___x_1151_ = leanh::lean_box(0);
                        v_isShared_1152_ = v_isSharedCheck_1171_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1142_ = l_List_reverse___redArg(v_fst_1137_);
                v___x_1143_ = l_List_reverse___redArg(v_snd_1138_);
                if v_isShared_1141_ == 0 {
                    leanh::lean_ctor_set(v___x_1140_, 1, v___x_1143_);
                    leanh::lean_ctor_set(v___x_1140_, 0, v___x_1142_);
                    v___x_1145_ = v___x_1140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1143_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1145_;
            }
            3 => {
                v_fst_1153_ = leanh::lean_ctor_get(v_a_1136_, 0);
                v_snd_1154_ = leanh::lean_ctor_get(v_a_1136_, 1);
                v_isSharedCheck_1170_ = (!leanh::lean_is_exclusive(v_a_1136_)) as u8;
                if v_isSharedCheck_1170_ == 0 {
                    v___x_1156_ = v_a_1136_;
                    v_isShared_1157_ = v_isSharedCheck_1170_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1154_);
                    leanh::lean_inc(v_fst_1153_);
                    leanh::lean_dec(v_a_1136_);
                    v___x_1156_ = leanh::lean_box(0);
                    v_isShared_1157_ = v_isSharedCheck_1170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1166_ = l_Lake_instDecidableEqBuildKey_decEq(v_head_1148_, v___x_1133_);
                if v___x_1166_ == 0 {
                    if v___x_1134_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_1156_);
                        leanh::lean_del_object(v___x_1151_);
                        v___x_1167_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1167_, 0, v_head_1148_);
                        leanh::lean_ctor_set(v___x_1167_, 1, v_fst_1153_);
                        v___x_1168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1168_, 0, v___x_1167_);
                        leanh::lean_ctor_set(v___x_1168_, 1, v_snd_1154_);
                        v_a_1135_ = v_tail_1149_;
                        v_a_1136_ = v___x_1168_;
                        state = 0;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1152_ == 0 {
                    leanh::lean_ctor_set(v___x_1151_, 1, v_snd_1154_);
                    v___x_1160_ = v___x_1151_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1165_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_head_1148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_snd_1154_);
                    v___x_1160_ = v_reuseFailAlloc_1165_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1157_ == 0 {
                    leanh::lean_ctor_set(v___x_1156_, 1, v___x_1160_);
                    v___x_1162_ = v___x_1156_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1164_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_fst_1153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1160_);
                    v___x_1162_ = v_reuseFailAlloc_1164_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_1135_ = v_tail_1149_;
                v_a_1136_ = v___x_1162_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(
    mut v___x_1172_: *mut leanh::LeanObject,
    mut v___x_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
    mut v_a_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3055__boxed_1176_: u8 = 0;
    let mut v_res_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3055__boxed_1176_ = (leanh::lean_unbox(v___x_1173_) as u8);
    v_res_1177_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_1172_, v___x_3055__boxed_1176_, v_a_1174_, v_a_1175_);
    leanh::lean_dec_ref(v___x_1172_);
    return v_res_1177_;
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(
    mut v___x_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_1178_, v_a_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
    leanh::lean_dec_ref(v___y_1183_);
    leanh::lean_dec(v___y_1182_);
    leanh::lean_dec(v___y_1181_);
    leanh::lean_dec(v___y_1180_);
    leanh::lean_dec(v___x_1178_);
    return v_res_1186_;
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(
    mut v_a_1189_: *mut leanh::LeanObject,
    mut v___y_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_unused_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_1189_);
                v___x_1196_ = l_Lake_BuildInfo_key(v_a_1189_);
                v___x_1197_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v___x_1196_, v___y_1191_);
                if v___x_1197_ == 0 {
                    leanh::lean_inc(v___y_1191_);
                    v___x_1198_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1198_, 0, v___x_1196_);
                    leanh::lean_ctor_set(v___x_1198_, 1, v___y_1191_);
                    leanh::lean_inc_ref(v___x_1198_);
                    v___f_1199_ = leanh::lean_alloc_closure(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    leanh::lean_closure_set(v___f_1199_, 0, v___x_1198_);
                    v___x_1200_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(
                        v_a_1189_,
                        v___f_1199_,
                        v___y_1190_,
                        v___x_1198_,
                        v___y_1192_,
                        v___y_1193_,
                        v___y_1194_,
                    );
                    leanh::lean_dec_ref_known(v___x_1198_, 2);
                    return v___x_1200_;
                } else {
                    leanh::lean_dec_ref(v_a_1189_);
                    v___x_1201_ = leanh::lean_box(0);
                    v___x_1202_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0;
                    leanh::lean_inc(v___y_1191_);
                    v___x_1203_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_1196_, v___x_1197_, v___y_1191_, v___x_1202_);
                    v_fst_1204_ = leanh::lean_ctor_get(v___x_1203_, 0);
                    v_isSharedCheck_1219_ = (!leanh::lean_is_exclusive(v___x_1203_)) as u8;
                    if v_isSharedCheck_1219_ == 0 {
                        v_unused_1220_ = leanh::lean_ctor_get(v___x_1203_, 1);
                        leanh::lean_dec(v_unused_1220_);
                        v___x_1206_ = v___x_1203_;
                        v_isShared_1207_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_1204_);
                        leanh::lean_dec(v___x_1203_);
                        v___x_1206_ = leanh::lean_box(0);
                        v_isShared_1207_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___x_1196_);
                if v_isShared_1207_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1206_, 1);
                    leanh::lean_ctor_set(v___x_1206_, 1, v_fst_1204_);
                    leanh::lean_ctor_set(v___x_1206_, 0, v___x_1196_);
                    v___x_1209_ = v___x_1206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1218_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_fst_1204_);
                    v___x_1209_ = v_reuseFailAlloc_1218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1210_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1210_, 0, v___x_1196_);
                leanh::lean_ctor_set(v___x_1210_, 1, v___x_1201_);
                v___x_1211_ = l_List_appendTR___redArg(v___x_1209_, v___x_1210_);
                v___x_1212_ = l_Lake_buildCycleError(v___x_1211_);
                v___x_1213_ = 3;
                v___x_1214_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1214_, 0, v___x_1212_);
                leanh::lean_ctor_set_uint8(
                    v___x_1214_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1213_,
                );
                v___x_1215_ = lean_array_get_size(v___y_1194_);
                v___x_1216_ = lean_array_push(v___y_1194_, v___x_1214_);
                v___x_1217_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1217_, 0, v___x_1215_);
                leanh::lean_ctor_set(v___x_1217_, 1, v___x_1216_);
                return v___x_1217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(
    mut v___x_1221_: *mut leanh::LeanObject,
    mut v_a_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_1222_, v___y_1223_, v___x_1221_, v___y_1225_, v___y_1226_, v___y_1227_);
    return v___x_1229_;
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(
    mut v_a_1230_: *mut leanh::LeanObject,
    mut v___y_1231_: *mut leanh::LeanObject,
    mut v___y_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
    leanh::lean_dec_ref(v___y_1234_);
    leanh::lean_dec(v___y_1233_);
    leanh::lean_dec(v___y_1232_);
    leanh::lean_dec(v___y_1231_);
    return v_res_1237_;
}
pub unsafe fn l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(
    mut v_info_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
    mut v_a_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_info_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
    return v___x_1245_;
}
pub unsafe fn l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(
    mut v_info_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1253_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(
        v_info_1246_,
        v_a_1247_,
        v_a_1248_,
        v_a_1249_,
        v_a_1250_,
        v_a_1251_,
    );
    leanh::lean_dec_ref(v_a_1250_);
    leanh::lean_dec(v_a_1249_);
    leanh::lean_dec(v_a_1248_);
    leanh::lean_dec(v_a_1247_);
    return v_res_1253_;
}
pub unsafe fn l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
    return v___x_1261_;
}
pub unsafe fn l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(
    mut v_a_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1269_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    leanh::lean_dec_ref(v___y_1266_);
    leanh::lean_dec(v___y_1265_);
    leanh::lean_dec(v___y_1264_);
    leanh::lean_dec(v___y_1263_);
    return v_res_1269_;
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(
    mut v_inst_1270_: *mut leanh::LeanObject,
    mut v_a_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
    return v___x_1278_;
}
pub unsafe fn l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(
    mut v_inst_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1287_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(v_inst_1279_, v_a_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
    leanh::lean_dec_ref(v___y_1284_);
    leanh::lean_dec(v___y_1283_);
    leanh::lean_dec(v___y_1282_);
    leanh::lean_dec(v___y_1281_);
    return v_res_1287_;
}
pub unsafe fn l_Lake_FetchT_run___redArg(
    mut v_x_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = l_Lake_FetchT_run___redArg___closed__0;
    leanh::lean_inc_ref(v_a_1293_);
    leanh::lean_inc(v_a_1292_);
    leanh::lean_inc(v_a_1291_);
    leanh::lean_inc(v_a_1290_);
    v___x_1295_ = leanh::lean_apply_5(
        v_x_1289_,
        v___x_1294_,
        v_a_1290_,
        v_a_1291_,
        v_a_1292_,
        v_a_1293_,
    );
    return v___x_1295_;
}
pub unsafe fn l_Lake_FetchT_run___redArg___boxed(
    mut v_x_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_Lake_FetchT_run___redArg(v_x_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
    leanh::lean_dec_ref(v_a_1300_);
    leanh::lean_dec(v_a_1299_);
    leanh::lean_dec(v_a_1298_);
    leanh::lean_dec(v_a_1297_);
    return v_res_1301_;
}
pub unsafe fn l_Lake_FetchT_run(
    mut v_m_1302_: *mut leanh::LeanObject,
    mut v_00_u03b1_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
    mut v_a_1306_: *mut leanh::LeanObject,
    mut v_a_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1309_ = l_Lake_FetchT_run___redArg___closed__0;
    leanh::lean_inc_ref(v_a_1308_);
    leanh::lean_inc(v_a_1307_);
    leanh::lean_inc(v_a_1306_);
    leanh::lean_inc(v_a_1305_);
    v___x_1310_ = leanh::lean_apply_5(
        v_x_1304_,
        v___x_1309_,
        v_a_1305_,
        v_a_1306_,
        v_a_1307_,
        v_a_1308_,
    );
    return v___x_1310_;
}
pub unsafe fn l_Lake_FetchT_run___boxed(
    mut v_m_1311_: *mut leanh::LeanObject,
    mut v_00_u03b1_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_a_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1318_ = l_Lake_FetchT_run(
        v_m_1311_,
        v_00_u03b1_1312_,
        v_x_1313_,
        v_a_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
    );
    leanh::lean_dec_ref(v_a_1317_);
    leanh::lean_dec(v_a_1316_);
    leanh::lean_dec(v_a_1315_);
    leanh::lean_dec(v_a_1314_);
    return v_res_1318_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Index(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Topological(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_StoreInsts(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Index(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Index(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Topological(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_StoreInsts(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Index(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Index(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Index(builtin);
}
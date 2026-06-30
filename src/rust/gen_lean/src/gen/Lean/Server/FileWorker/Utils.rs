// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: Lean.Language.Lean.Types Lean.Server.Snapshots Lean.Server.AsyncList Std.Sync.Mutex
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_io_get_random_bytes,
    lean_io_mono_ms_now, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_task_pure, lean_usize_add, lean_usize_dec_eq,
    lean_usize_land, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::ByteArray::Extra::l_ByteArray_toUInt64LE_x21;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Language::Lean::Types::{
    initialize_Lean_Language_Lean_Types, runtime_initialize_Lean_Language_Lean_Types,
};
use crate::r#gen::Lean::Server::AsyncList::{
    initialize_Lean_Server_AsyncList, runtime_initialize_Lean_Server_AsyncList,
};
use crate::r#gen::Lean::Server::ServerTask::{
    l_Lean_Server_ServerTask_bindCheap___redArg, l_Lean_Server_ServerTask_mapCheap___redArg,
};
use crate::r#gen::Lean::Server::Snapshots::{
    initialize_Lean_Server_Snapshots, runtime_initialize_Lean_Server_Snapshots,
};
use crate::r#gen::Lean::Server::Utils::l_Lean_Server_mkPublishDiagnosticsNotification;
use crate::r#gen::Lean::Widget::InteractiveDiagnostic::l_Lean_Widget_InteractiveDiagnostic_toDiagnostic;
use crate::r#gen::Lean::Widget::TaggedText::l_Lean_Widget_TaggedText_stripTags___redArg;
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
pub static l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_RpcSession_new___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_FileWorker_RpcSession_new___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_FileWorker_RpcSession_new___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_FileWorker_RpcSession_new___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(
    mut v_stx_797_: *mut leanh::LeanObject,
    mut v_parserState_798_: *mut leanh::LeanObject,
    mut v_nextCmdSnap_x3f_799_: *mut leanh::LeanObject,
    mut v_result_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cmdState_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v_task_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut v_unused_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cmdState_801_ = leanh::lean_ctor_get(v_result_800_, 1);
                v_isSharedCheck_824_ = (!leanh::lean_is_exclusive(v_result_800_)) as u8;
                if v_isSharedCheck_824_ == 0 {
                    v_unused_825_ = leanh::lean_ctor_get(v_result_800_, 0);
                    leanh::lean_dec(v_unused_825_);
                    v___x_803_ = v_result_800_;
                    v_isShared_804_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cmdState_801_);
                    leanh::lean_dec(v_result_800_);
                    v___x_803_ = leanh::lean_box(0);
                    v_isShared_804_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_805_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_805_, 0, v_stx_797_);
                leanh::lean_ctor_set(v___x_805_, 1, v_parserState_798_);
                leanh::lean_ctor_set(v___x_805_, 2, v_cmdState_801_);
                if leanh::lean_obj_tag(v_nextCmdSnap_x3f_799_) == 0 {
                    v___x_812_ = leanh::lean_box(2);
                    v___y_807_ = v___x_812_;
                    state = 2;
                    continue;
                } else {
                    v_val_813_ = leanh::lean_ctor_get(v_nextCmdSnap_x3f_799_, 0);
                    v_isSharedCheck_823_ =
                        (!leanh::lean_is_exclusive(v_nextCmdSnap_x3f_799_)) as u8;
                    if v_isSharedCheck_823_ == 0 {
                        v___x_815_ = v_nextCmdSnap_x3f_799_;
                        v_isShared_816_ = v_isSharedCheck_823_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_813_);
                        leanh::lean_dec(v_nextCmdSnap_x3f_799_);
                        v___x_815_ = leanh::lean_box(0);
                        v_isShared_816_ = v_isSharedCheck_823_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_804_ == 0 {
                    leanh::lean_ctor_set(v___x_803_, 1, v___y_807_);
                    leanh::lean_ctor_set(v___x_803_, 0, v___x_805_);
                    v___x_809_ = v___x_803_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_811_, 1, v___y_807_);
                    v___x_809_ = v_reuseFailAlloc_811_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_810_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_810_, 0, v___x_809_);
                return v___x_810_;
            }
            4 => {
                v_task_817_ = leanh::lean_ctor_get(v_val_813_, 3);
                leanh::lean_inc_ref(v_task_817_);
                leanh::lean_dec(v_val_813_);
                v___x_818_ = leanh::lean_alloc_closure(
                    l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go
                        as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_819_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_817_, v___x_818_);
                if v_isShared_816_ == 0 {
                    leanh::lean_ctor_set(v___x_815_, 0, v___x_819_);
                    v___x_821_ = v___x_815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
                    v___x_821_ = v_reuseFailAlloc_822_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_807_ = v___x_821_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(
    mut v_cmdParsed_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elabSnap_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultSnap_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCmdSnap_x3f_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_elabSnap_827_ = leanh::lean_ctor_get(v_cmdParsed_826_, 3);
    v_resultSnap_828_ = leanh::lean_ctor_get(v_elabSnap_827_, 2);
    leanh::lean_inc_ref(v_resultSnap_828_);
    v_stx_829_ = leanh::lean_ctor_get(v_cmdParsed_826_, 1);
    leanh::lean_inc(v_stx_829_);
    v_parserState_830_ = leanh::lean_ctor_get(v_cmdParsed_826_, 2);
    leanh::lean_inc_ref(v_parserState_830_);
    v_nextCmdSnap_x3f_831_ = leanh::lean_ctor_get(v_cmdParsed_826_, 4);
    leanh::lean_inc(v_nextCmdSnap_x3f_831_);
    leanh::lean_dec_ref(v_cmdParsed_826_);
    v_task_832_ = leanh::lean_ctor_get(v_resultSnap_828_, 3);
    leanh::lean_inc_ref(v_task_832_);
    leanh::lean_dec_ref(v_resultSnap_828_);
    v___f_833_ = leanh::lean_alloc_closure(
        l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_833_, 0, v_stx_829_);
    leanh::lean_closure_set(v___f_833_, 1, v_parserState_830_);
    leanh::lean_closure_set(v___f_833_, 2, v_nextCmdSnap_x3f_831_);
    v___x_834_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_833_, v_task_832_);
    return v___x_834_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1;
    v___x_839_ = lean_task_pure(v___x_838_);
    return v___x_839_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(
    mut v_stx_840_: *mut leanh::LeanObject,
    mut v_parserState_841_: *mut leanh::LeanObject,
    mut v_headerProcessed_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_846_: u8 = 0;
    let mut v_val_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v_firstCmdSnap_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdState_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_855_: u8 = 0;
    let mut v_task_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut v_unused_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_x3f_843_ = leanh::lean_ctor_get(v_headerProcessed_842_, 2);
                v_isSharedCheck_873_ =
                    (!leanh::lean_is_exclusive(v_headerProcessed_842_)) as u8;
                if v_isSharedCheck_873_ == 0 {
                    v_unused_874_ = leanh::lean_ctor_get(v_headerProcessed_842_, 1);
                    leanh::lean_dec(v_unused_874_);
                    v_unused_875_ = leanh::lean_ctor_get(v_headerProcessed_842_, 0);
                    leanh::lean_dec(v_unused_875_);
                    v___x_845_ = v_headerProcessed_842_;
                    v_isShared_846_ = v_isSharedCheck_873_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_result_x3f_843_);
                    leanh::lean_dec(v_headerProcessed_842_);
                    v___x_845_ = leanh::lean_box(0);
                    v_isShared_846_ = v_isSharedCheck_873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_result_x3f_843_) == 1 {
                    v_val_847_ = leanh::lean_ctor_get(v_result_x3f_843_, 0);
                    v_isSharedCheck_871_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_843_)) as u8;
                    if v_isSharedCheck_871_ == 0 {
                        v___x_849_ = v_result_x3f_843_;
                        v_isShared_850_ = v_isSharedCheck_871_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_847_);
                        leanh::lean_dec(v_result_x3f_843_);
                        v___x_849_ = leanh::lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_871_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_845_);
                    leanh::lean_dec(v_result_x3f_843_);
                    leanh::lean_dec_ref(v_parserState_841_);
                    leanh::lean_dec(v_stx_840_);
                    v___x_872_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once), _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2);
                    return v___x_872_;
                }
            }
            2 => {
                v_firstCmdSnap_851_ = leanh::lean_ctor_get(v_val_847_, 1);
                v_cmdState_852_ = leanh::lean_ctor_get(v_val_847_, 0);
                v_isSharedCheck_870_ = (!leanh::lean_is_exclusive(v_val_847_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_854_ = v_val_847_;
                    v_isShared_855_ = v_isSharedCheck_870_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_firstCmdSnap_851_);
                    leanh::lean_inc(v_cmdState_852_);
                    leanh::lean_dec(v_val_847_);
                    v___x_854_ = leanh::lean_box(0);
                    v_isShared_855_ = v_isSharedCheck_870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_task_856_ = leanh::lean_ctor_get(v_firstCmdSnap_851_, 3);
                leanh::lean_inc_ref(v_task_856_);
                leanh::lean_dec_ref(v_firstCmdSnap_851_);
                if v_isShared_846_ == 0 {
                    leanh::lean_ctor_set(v___x_845_, 2, v_cmdState_852_);
                    leanh::lean_ctor_set(v___x_845_, 1, v_parserState_841_);
                    leanh::lean_ctor_set(v___x_845_, 0, v_stx_840_);
                    v___x_858_ = v___x_845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_stx_840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v_parserState_841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 2, v_cmdState_852_);
                    v___x_858_ = v_reuseFailAlloc_869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_859_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0;
                v___x_860_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_856_, v___x_859_);
                if v_isShared_850_ == 0 {
                    leanh::lean_ctor_set(v___x_849_, 0, v___x_860_);
                    v___x_862_ = v___x_849_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_868_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_855_ == 0 {
                    leanh::lean_ctor_set(v___x_854_, 1, v___x_862_);
                    leanh::lean_ctor_set(v___x_854_, 0, v___x_858_);
                    v___x_864_ = v___x_854_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_862_);
                    v___x_864_ = v_reuseFailAlloc_867_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_865_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_865_, 0, v___x_864_);
                v___x_866_ = lean_task_pure(v___x_865_);
                return v___x_866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(
    mut v_initSnap_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_x3f_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v_processedSnap_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserState_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_x3f_877_ = leanh::lean_ctor_get(v_initSnap_876_, 4);
                leanh::lean_inc(v_result_x3f_877_);
                if leanh::lean_obj_tag(v_result_x3f_877_) == 1 {
                    v_val_878_ = leanh::lean_ctor_get(v_result_x3f_877_, 0);
                    v_isSharedCheck_891_ =
                        (!leanh::lean_is_exclusive(v_result_x3f_877_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_880_ = v_result_x3f_877_;
                        v_isShared_881_ = v_isSharedCheck_891_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_878_);
                        leanh::lean_dec(v_result_x3f_877_);
                        v___x_880_ = leanh::lean_box(0);
                        v_isShared_881_ = v_isSharedCheck_891_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_result_x3f_877_);
                    leanh::lean_dec_ref(v_initSnap_876_);
                    v___x_892_ = leanh::lean_box(2);
                    return v___x_892_;
                }
            }
            1 => {
                v_processedSnap_882_ = leanh::lean_ctor_get(v_val_878_, 1);
                leanh::lean_inc_ref(v_processedSnap_882_);
                v_stx_883_ = leanh::lean_ctor_get(v_initSnap_876_, 3);
                leanh::lean_inc(v_stx_883_);
                leanh::lean_dec_ref(v_initSnap_876_);
                v_parserState_884_ = leanh::lean_ctor_get(v_val_878_, 0);
                leanh::lean_inc_ref(v_parserState_884_);
                leanh::lean_dec(v_val_878_);
                v_task_885_ = leanh::lean_ctor_get(v_processedSnap_882_, 3);
                leanh::lean_inc_ref(v_task_885_);
                leanh::lean_dec_ref(v_processedSnap_882_);
                v___f_886_ = leanh::lean_alloc_closure(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_886_, 0, v_stx_883_);
                leanh::lean_closure_set(v___f_886_, 1, v_parserState_884_);
                v___x_887_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_885_, v___f_886_);
                if v_isShared_881_ == 0 {
                    leanh::lean_ctor_set(v___x_880_, 0, v___x_887_);
                    v___x_889_ = v___x_880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore___private__1(
    mut v_initSnap_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(
        v_initSnap_893_,
    );
    return v___x_894_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(
    mut v_mutex_895_: *mut leanh::LeanObject,
    mut v_k_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_898_ = leanh::lean_ctor_get(v_mutex_895_, 0);
    leanh::lean_inc(v_ref_898_);
    v_mutex_899_ = leanh::lean_ctor_get(v_mutex_895_, 1);
    leanh::lean_inc(v_mutex_899_);
    leanh::lean_dec_ref(v_mutex_895_);
    v___x_900_ = lean_io_basemutex_lock(v_mutex_899_);
    v___x_901_ = leanh::lean_apply_2(v_k_896_, v_ref_898_, leanh::lean_box(0));
    v___x_902_ = lean_io_basemutex_unlock(v_mutex_899_);
    leanh::lean_dec(v_mutex_899_);
    return v___x_901_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg___boxed(
    mut v_mutex_903_: *mut leanh::LeanObject,
    mut v_k_904_: *mut leanh::LeanObject,
    mut v___y_905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_903_, v_k_904_);
    return v_res_906_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(
    mut v_00_u03b1_907_: *mut leanh::LeanObject,
    mut v_00_u03b2_908_: *mut leanh::LeanObject,
    mut v_mutex_909_: *mut leanh::LeanObject,
    mut v_k_910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_909_, v_k_910_);
    return v___x_912_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___boxed(
    mut v_00_u03b1_913_: *mut leanh::LeanObject,
    mut v_00_u03b2_914_: *mut leanh::LeanObject,
    mut v_mutex_915_: *mut leanh::LeanObject,
    mut v_k_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(v_00_u03b1_913_, v_00_u03b2_914_, v_mutex_915_, v_k_916_);
    return v_res_918_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(
    mut v_as_919_: *mut leanh::LeanObject,
    mut v_i_920_: usize,
    mut v_stop_921_: usize,
    mut v_b_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_923_: u8 = 0;
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_923_ = lean_usize_dec_eq(v_i_920_, v_stop_921_);
                if v___x_923_ == 0 {
                    v___x_924_ = lean_array_uget_borrowed(v_as_919_, v_i_920_);
                    leanh::lean_inc(v___x_924_);
                    v___x_925_ = l_Lean_PersistentArray_push___redArg(v_b_922_, v___x_924_);
                    v___x_926_ = 1usize;
                    v___x_927_ = lean_usize_add(v_i_920_, v___x_926_);
                    v_i_920_ = v___x_927_;
                    v_b_922_ = v___x_925_;
                    state = 0;
                    continue;
                } else {
                    return v_b_922_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0___boxed(
    mut v_as_929_: *mut leanh::LeanObject,
    mut v_i_930_: *mut leanh::LeanObject,
    mut v_stop_931_: *mut leanh::LeanObject,
    mut v_b_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_933_: usize = 0;
    let mut v_stop_boxed_934_: usize = 0;
    let mut v_res_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_933_ = leanh::lean_unbox_usize(v_i_930_);
    leanh::lean_dec(v_i_930_);
    v_stop_boxed_934_ = leanh::lean_unbox_usize(v_stop_931_);
    leanh::lean_dec(v_stop_931_);
    v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_as_929_, v_i_boxed_933_, v_stop_boxed_934_, v_b_932_);
    leanh::lean_dec_ref(v_as_929_);
    return v_res_935_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(
    mut v_diags_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stickyDiagsRef_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diags_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_942_: u8 = 0;
    let mut v_publishedDiagsAmount_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_939_ = lean_st_ref_take(v___y_937_);
                v_stickyDiagsRef_940_ = leanh::lean_ctor_get(v___x_939_, 0);
                v_diags_941_ = leanh::lean_ctor_get(v___x_939_, 1);
                v_isIncremental_942_ = leanh::lean_ctor_get_uint8(
                    v___x_939_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_publishedDiagsAmount_943_ = leanh::lean_ctor_get(v___x_939_, 2);
                v_isSharedCheck_964_ = (!leanh::lean_is_exclusive(v___x_939_)) as u8;
                if v_isSharedCheck_964_ == 0 {
                    v___x_945_ = v___x_939_;
                    v_isShared_946_ = v_isSharedCheck_964_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_publishedDiagsAmount_943_);
                    leanh::lean_inc(v_diags_941_);
                    leanh::lean_inc(v_stickyDiagsRef_940_);
                    leanh::lean_dec(v___x_939_);
                    v___x_945_ = leanh::lean_box(0);
                    v_isShared_946_ = v_isSharedCheck_964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_947_ = leanh::lean_box(0);
                v___x_954_ = leanh::lean_unsigned_to_nat(0);
                v___x_955_ = lean_array_get_size(v_diags_936_);
                v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
                if v___x_956_ == 0 {
                    v___y_949_ = v_diags_941_;
                    state = 2;
                    continue;
                } else {
                    v___x_957_ = lean_nat_dec_le(v___x_955_, v___x_955_);
                    if v___x_957_ == 0 {
                        if v___x_956_ == 0 {
                            v___y_949_ = v_diags_941_;
                            state = 2;
                            continue;
                        } else {
                            v___x_958_ = 0usize;
                            v___x_959_ = lean_usize_of_nat(v___x_955_);
                            v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_936_, v___x_958_, v___x_959_, v_diags_941_);
                            v___y_949_ = v___x_960_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_961_ = 0usize;
                        v___x_962_ = lean_usize_of_nat(v___x_955_);
                        v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_936_, v___x_961_, v___x_962_, v_diags_941_);
                        v___y_949_ = v___x_963_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_946_ == 0 {
                    leanh::lean_ctor_set(v___x_945_, 1, v___y_949_);
                    v___x_951_ = v___x_945_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v_stickyDiagsRef_940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 1, v___y_949_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_953_,
                        2,
                        v_publishedDiagsAmount_943_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_953_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_isIncremental_942_,
                    );
                    v___x_951_ = v_reuseFailAlloc_953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_952_ = lean_st_ref_set(v___y_937_, v___x_951_);
                return v___x_947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(
    mut v_diags_965_: *mut leanh::LeanObject,
    mut v___y_966_: *mut leanh::LeanObject,
    mut v___y_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(
        v_diags_965_,
        v___y_966_,
    );
    leanh::lean_dec(v___y_966_);
    leanh::lean_dec_ref(v_diags_965_);
    return v_res_968_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(
    mut v_doc_969_: *mut leanh::LeanObject,
    mut v_diags_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diagnosticsMutex_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_diagnosticsMutex_972_ = leanh::lean_ctor_get(v_doc_969_, 3);
    leanh::lean_inc_ref(v_diagnosticsMutex_972_);
    leanh::lean_dec_ref(v_doc_969_);
    v___f_973_ = leanh::lean_alloc_closure(
        l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_973_, 0, v_diags_970_);
    v___x_974_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_972_, v___f_973_);
    return v___x_974_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(
    mut v_doc_975_: *mut leanh::LeanObject,
    mut v_diags_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ =
        l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_975_, v_diags_976_);
    return v_res_978_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(
    mut v_diagnostic_979_: *mut leanh::LeanObject,
    mut v_as_980_: *mut leanh::LeanObject,
    mut v_i_981_: usize,
    mut v_stop_982_: usize,
    mut v_b_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_989_ = lean_usize_dec_eq(v_i_981_, v_stop_982_);
                if v___x_989_ == 0 {
                    v___x_990_ = lean_array_uget_borrowed(v_as_980_, v_i_981_);
                    v_message_991_ = leanh::lean_ctor_get(v___x_990_, 6);
                    v_message_992_ = leanh::lean_ctor_get(v_diagnostic_979_, 6);
                    leanh::lean_inc(v_message_991_);
                    v___x_993_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_991_);
                    leanh::lean_inc(v_message_992_);
                    v___x_994_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_992_);
                    v___x_995_ = lean_string_dec_eq(v___x_993_, v___x_994_);
                    leanh::lean_dec_ref(v___x_994_);
                    leanh::lean_dec_ref(v___x_993_);
                    if v___x_995_ == 0 {
                        leanh::lean_inc(v___x_990_);
                        v___x_996_ = l_Lean_PersistentArray_push___redArg(v_b_983_, v___x_990_);
                        v___y_985_ = v___x_996_;
                        state = 1;
                        continue;
                    } else {
                        v___y_985_ = v_b_983_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_diagnostic_979_);
                    return v_b_983_;
                }
            }
            1 => {
                v___x_986_ = 1usize;
                v___x_987_ = lean_usize_add(v_i_981_, v___x_986_);
                v_i_981_ = v___x_987_;
                v_b_983_ = v___y_985_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(
    mut v_diagnostic_997_: *mut leanh::LeanObject,
    mut v_as_998_: *mut leanh::LeanObject,
    mut v_i_999_: *mut leanh::LeanObject,
    mut v_stop_1000_: *mut leanh::LeanObject,
    mut v_b_1001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1002_: usize = 0;
    let mut v_stop_boxed_1003_: usize = 0;
    let mut v_res_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1002_ = leanh::lean_unbox_usize(v_i_999_);
    leanh::lean_dec(v_i_999_);
    v_stop_boxed_1003_ = leanh::lean_unbox_usize(v_stop_1000_);
    leanh::lean_dec(v_stop_1000_);
    v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_997_, v_as_998_, v_i_boxed_1002_, v_stop_boxed_1003_, v_b_1001_);
    leanh::lean_dec_ref(v_as_998_);
    return v_res_1004_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(
    mut v_diagnostic_1005_: *mut leanh::LeanObject,
    mut v_x_1006_: *mut leanh::LeanObject,
    mut v_x_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1006_) == 0 {
        let mut v_cs_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1011_: u8 = 0;
        v_cs_1008_ = leanh::lean_ctor_get(v_x_1006_, 0);
        v___x_1009_ = leanh::lean_unsigned_to_nat(0);
        v___x_1010_ = lean_array_get_size(v_cs_1008_);
        v___x_1011_ = lean_nat_dec_lt(v___x_1009_, v___x_1010_);
        if v___x_1011_ == 0 {
            leanh::lean_dec_ref(v_diagnostic_1005_);
            return v_x_1007_;
        } else {
            let mut v___x_1012_: u8 = 0;
            v___x_1012_ = lean_nat_dec_le(v___x_1010_, v___x_1010_);
            if v___x_1012_ == 0 {
                if v___x_1011_ == 0 {
                    leanh::lean_dec_ref(v_diagnostic_1005_);
                    return v_x_1007_;
                } else {
                    let mut v___x_1013_: usize = 0;
                    let mut v___x_1014_: usize = 0;
                    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1013_ = 0usize;
                    v___x_1014_ = lean_usize_of_nat(v___x_1010_);
                    v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_1005_, v_cs_1008_, v___x_1013_, v___x_1014_, v_x_1007_);
                    return v___x_1015_;
                }
            } else {
                let mut v___x_1016_: usize = 0;
                let mut v___x_1017_: usize = 0;
                let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1016_ = 0usize;
                v___x_1017_ = lean_usize_of_nat(v___x_1010_);
                v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_1005_, v_cs_1008_, v___x_1016_, v___x_1017_, v_x_1007_);
                return v___x_1018_;
            }
        }
    } else {
        let mut v_vs_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: u8 = 0;
        v_vs_1019_ = leanh::lean_ctor_get(v_x_1006_, 0);
        v___x_1020_ = leanh::lean_unsigned_to_nat(0);
        v___x_1021_ = lean_array_get_size(v_vs_1019_);
        v___x_1022_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
        if v___x_1022_ == 0 {
            leanh::lean_dec_ref(v_diagnostic_1005_);
            return v_x_1007_;
        } else {
            let mut v___x_1023_: u8 = 0;
            v___x_1023_ = lean_nat_dec_le(v___x_1021_, v___x_1021_);
            if v___x_1023_ == 0 {
                if v___x_1022_ == 0 {
                    leanh::lean_dec_ref(v_diagnostic_1005_);
                    return v_x_1007_;
                } else {
                    let mut v___x_1024_: usize = 0;
                    let mut v___x_1025_: usize = 0;
                    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1024_ = 0usize;
                    v___x_1025_ = lean_usize_of_nat(v___x_1021_);
                    v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1005_, v_vs_1019_, v___x_1024_, v___x_1025_, v_x_1007_);
                    return v___x_1026_;
                }
            } else {
                let mut v___x_1027_: usize = 0;
                let mut v___x_1028_: usize = 0;
                let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1027_ = 0usize;
                v___x_1028_ = lean_usize_of_nat(v___x_1021_);
                v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1005_, v_vs_1019_, v___x_1027_, v___x_1028_, v_x_1007_);
                return v___x_1029_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(
    mut v_diagnostic_1030_: *mut leanh::LeanObject,
    mut v_as_1031_: *mut leanh::LeanObject,
    mut v_i_1032_: usize,
    mut v_stop_1033_: usize,
    mut v_b_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: usize = 0;
    let mut v___x_1039_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1035_ = lean_usize_dec_eq(v_i_1032_, v_stop_1033_);
                if v___x_1035_ == 0 {
                    v___x_1036_ = lean_array_uget_borrowed(v_as_1031_, v_i_1032_);
                    leanh::lean_inc_ref(v_diagnostic_1030_);
                    v___x_1037_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_1030_, v___x_1036_, v_b_1034_);
                    v___x_1038_ = 1usize;
                    v___x_1039_ = lean_usize_add(v_i_1032_, v___x_1038_);
                    v_i_1032_ = v___x_1039_;
                    v_b_1034_ = v___x_1037_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_diagnostic_1030_);
                    return v_b_1034_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(
    mut v_diagnostic_1041_: *mut leanh::LeanObject,
    mut v_as_1042_: *mut leanh::LeanObject,
    mut v_i_1043_: *mut leanh::LeanObject,
    mut v_stop_1044_: *mut leanh::LeanObject,
    mut v_b_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1046_: usize = 0;
    let mut v_stop_boxed_1047_: usize = 0;
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1046_ = leanh::lean_unbox_usize(v_i_1043_);
    leanh::lean_dec(v_i_1043_);
    v_stop_boxed_1047_ = leanh::lean_unbox_usize(v_stop_1044_);
    leanh::lean_dec(v_stop_1044_);
    v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_1041_, v_as_1042_, v_i_boxed_1046_, v_stop_boxed_1047_, v_b_1045_);
    leanh::lean_dec_ref(v_as_1042_);
    return v_res_1048_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(
    mut v_diagnostic_1049_: *mut leanh::LeanObject,
    mut v_x_1050_: *mut leanh::LeanObject,
    mut v_x_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1052_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_1049_, v_x_1050_, v_x_1051_);
    leanh::lean_dec_ref(v_x_1050_);
    return v_res_1052_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_1053_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(
    mut v_diagnostic_1054_: *mut leanh::LeanObject,
    mut v_x_1055_: *mut leanh::LeanObject,
    mut v_x_1056_: usize,
    mut v_x_1057_: usize,
    mut v_x_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1055_) == 0 {
        let mut v_cs_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: usize = 0;
        let mut v_j_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: usize = 0;
        let mut v___x_1065_: usize = 0;
        let mut v___x_1066_: usize = 0;
        let mut v___x_1067_: usize = 0;
        let mut v___x_1068_: usize = 0;
        let mut v___x_1069_: usize = 0;
        let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: u8 = 0;
        v_cs_1059_ = leanh::lean_ctor_get(v_x_1055_, 0);
        v___x_1060_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
        v___x_1061_ = lean_usize_shift_right(v_x_1056_, v_x_1057_);
        v_j_1062_ = lean_usize_to_nat(v___x_1061_);
        v___x_1063_ = lean_array_get_borrowed(v___x_1060_, v_cs_1059_, v_j_1062_);
        v___x_1064_ = 1usize;
        v___x_1065_ = lean_usize_shift_left(v___x_1064_, v_x_1057_);
        v___x_1066_ = lean_usize_sub(v___x_1065_, v___x_1064_);
        v___x_1067_ = lean_usize_land(v_x_1056_, v___x_1066_);
        v___x_1068_ = 5usize;
        v___x_1069_ = lean_usize_sub(v_x_1057_, v___x_1068_);
        leanh::lean_inc_ref(v_diagnostic_1054_);
        v___x_1070_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_1054_, v___x_1063_, v___x_1067_, v___x_1069_, v_x_1058_);
        v___x_1071_ = leanh::lean_unsigned_to_nat(1);
        v___x_1072_ = lean_nat_add(v_j_1062_, v___x_1071_);
        leanh::lean_dec(v_j_1062_);
        v___x_1073_ = lean_array_get_size(v_cs_1059_);
        v___x_1074_ = lean_nat_dec_lt(v___x_1072_, v___x_1073_);
        if v___x_1074_ == 0 {
            leanh::lean_dec(v___x_1072_);
            leanh::lean_dec_ref(v_diagnostic_1054_);
            return v___x_1070_;
        } else {
            let mut v___x_1075_: u8 = 0;
            v___x_1075_ = lean_nat_dec_le(v___x_1073_, v___x_1073_);
            if v___x_1075_ == 0 {
                if v___x_1074_ == 0 {
                    leanh::lean_dec(v___x_1072_);
                    leanh::lean_dec_ref(v_diagnostic_1054_);
                    return v___x_1070_;
                } else {
                    let mut v___x_1076_: usize = 0;
                    let mut v___x_1077_: usize = 0;
                    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1076_ = lean_usize_of_nat(v___x_1072_);
                    leanh::lean_dec(v___x_1072_);
                    v___x_1077_ = lean_usize_of_nat(v___x_1073_);
                    v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_1054_, v_cs_1059_, v___x_1076_, v___x_1077_, v___x_1070_);
                    return v___x_1078_;
                }
            } else {
                let mut v___x_1079_: usize = 0;
                let mut v___x_1080_: usize = 0;
                let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1079_ = lean_usize_of_nat(v___x_1072_);
                leanh::lean_dec(v___x_1072_);
                v___x_1080_ = lean_usize_of_nat(v___x_1073_);
                v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_1054_, v_cs_1059_, v___x_1079_, v___x_1080_, v___x_1070_);
                return v___x_1081_;
            }
        }
    } else {
        let mut v_vs_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1085_: u8 = 0;
        v_vs_1082_ = leanh::lean_ctor_get(v_x_1055_, 0);
        v___x_1083_ = lean_usize_to_nat(v_x_1056_);
        v___x_1084_ = lean_array_get_size(v_vs_1082_);
        v___x_1085_ = lean_nat_dec_lt(v___x_1083_, v___x_1084_);
        if v___x_1085_ == 0 {
            leanh::lean_dec(v___x_1083_);
            leanh::lean_dec_ref(v_diagnostic_1054_);
            return v_x_1058_;
        } else {
            let mut v___x_1086_: u8 = 0;
            v___x_1086_ = lean_nat_dec_le(v___x_1084_, v___x_1084_);
            if v___x_1086_ == 0 {
                if v___x_1085_ == 0 {
                    leanh::lean_dec(v___x_1083_);
                    leanh::lean_dec_ref(v_diagnostic_1054_);
                    return v_x_1058_;
                } else {
                    let mut v___x_1087_: usize = 0;
                    let mut v___x_1088_: usize = 0;
                    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1087_ = lean_usize_of_nat(v___x_1083_);
                    leanh::lean_dec(v___x_1083_);
                    v___x_1088_ = lean_usize_of_nat(v___x_1084_);
                    v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1054_, v_vs_1082_, v___x_1087_, v___x_1088_, v_x_1058_);
                    return v___x_1089_;
                }
            } else {
                let mut v___x_1090_: usize = 0;
                let mut v___x_1091_: usize = 0;
                let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1090_ = lean_usize_of_nat(v___x_1083_);
                leanh::lean_dec(v___x_1083_);
                v___x_1091_ = lean_usize_of_nat(v___x_1084_);
                v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1054_, v_vs_1082_, v___x_1090_, v___x_1091_, v_x_1058_);
                return v___x_1092_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(
    mut v_diagnostic_1093_: *mut leanh::LeanObject,
    mut v_x_1094_: *mut leanh::LeanObject,
    mut v_x_1095_: *mut leanh::LeanObject,
    mut v_x_1096_: *mut leanh::LeanObject,
    mut v_x_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1899__boxed_1098_: usize = 0;
    let mut v_x_1900__boxed_1099_: usize = 0;
    let mut v_res_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1899__boxed_1098_ = leanh::lean_unbox_usize(v_x_1095_);
    leanh::lean_dec(v_x_1095_);
    v_x_1900__boxed_1099_ = leanh::lean_unbox_usize(v_x_1096_);
    leanh::lean_dec(v_x_1096_);
    v_res_1100_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_1093_, v_x_1094_, v_x_1899__boxed_1098_, v_x_1900__boxed_1099_, v_x_1097_);
    leanh::lean_dec_ref(v_x_1094_);
    return v_res_1100_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(
    mut v_diagnostic_1101_: *mut leanh::LeanObject,
    mut v_t_1102_: *mut leanh::LeanObject,
    mut v_init_1103_: *mut leanh::LeanObject,
    mut v_start_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: u8 = 0;
    v___x_1105_ = leanh::lean_unsigned_to_nat(0);
    v___x_1106_ = lean_nat_dec_eq(v_start_1104_, v___x_1105_);
    if v___x_1106_ == 0 {
        let mut v_root_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_1109_: usize = 0;
        let mut v_tailOff_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1111_: u8 = 0;
        v_root_1107_ = leanh::lean_ctor_get(v_t_1102_, 0);
        v_tail_1108_ = leanh::lean_ctor_get(v_t_1102_, 1);
        v_shift_1109_ = leanh::lean_ctor_get_usize(v_t_1102_, 4);
        v_tailOff_1110_ = leanh::lean_ctor_get(v_t_1102_, 3);
        v___x_1111_ = lean_nat_dec_le(v_tailOff_1110_, v_start_1104_);
        if v___x_1111_ == 0 {
            let mut v___x_1112_: usize = 0;
            let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1115_: u8 = 0;
            v___x_1112_ = lean_usize_of_nat(v_start_1104_);
            leanh::lean_inc_ref(v_diagnostic_1101_);
            v___x_1113_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_1101_, v_root_1107_, v___x_1112_, v_shift_1109_, v_init_1103_);
            v___x_1114_ = lean_array_get_size(v_tail_1108_);
            v___x_1115_ = lean_nat_dec_lt(v___x_1105_, v___x_1114_);
            if v___x_1115_ == 0 {
                leanh::lean_dec_ref(v_diagnostic_1101_);
                return v___x_1113_;
            } else {
                let mut v___x_1116_: u8 = 0;
                v___x_1116_ = lean_nat_dec_le(v___x_1114_, v___x_1114_);
                if v___x_1116_ == 0 {
                    if v___x_1115_ == 0 {
                        leanh::lean_dec_ref(v_diagnostic_1101_);
                        return v___x_1113_;
                    } else {
                        let mut v___x_1117_: usize = 0;
                        let mut v___x_1118_: usize = 0;
                        let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1117_ = 0usize;
                        v___x_1118_ = lean_usize_of_nat(v___x_1114_);
                        v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1108_, v___x_1117_, v___x_1118_, v___x_1113_);
                        return v___x_1119_;
                    }
                } else {
                    let mut v___x_1120_: usize = 0;
                    let mut v___x_1121_: usize = 0;
                    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1120_ = 0usize;
                    v___x_1121_ = lean_usize_of_nat(v___x_1114_);
                    v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1108_, v___x_1120_, v___x_1121_, v___x_1113_);
                    return v___x_1122_;
                }
            }
        } else {
            let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1125_: u8 = 0;
            v___x_1123_ = lean_nat_sub(v_start_1104_, v_tailOff_1110_);
            v___x_1124_ = lean_array_get_size(v_tail_1108_);
            v___x_1125_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
            if v___x_1125_ == 0 {
                leanh::lean_dec(v___x_1123_);
                leanh::lean_dec_ref(v_diagnostic_1101_);
                return v_init_1103_;
            } else {
                let mut v___x_1126_: u8 = 0;
                v___x_1126_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
                if v___x_1126_ == 0 {
                    if v___x_1125_ == 0 {
                        leanh::lean_dec(v___x_1123_);
                        leanh::lean_dec_ref(v_diagnostic_1101_);
                        return v_init_1103_;
                    } else {
                        let mut v___x_1127_: usize = 0;
                        let mut v___x_1128_: usize = 0;
                        let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1127_ = lean_usize_of_nat(v___x_1123_);
                        leanh::lean_dec(v___x_1123_);
                        v___x_1128_ = lean_usize_of_nat(v___x_1124_);
                        v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1108_, v___x_1127_, v___x_1128_, v_init_1103_);
                        return v___x_1129_;
                    }
                } else {
                    let mut v___x_1130_: usize = 0;
                    let mut v___x_1131_: usize = 0;
                    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1130_ = lean_usize_of_nat(v___x_1123_);
                    leanh::lean_dec(v___x_1123_);
                    v___x_1131_ = lean_usize_of_nat(v___x_1124_);
                    v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1108_, v___x_1130_, v___x_1131_, v_init_1103_);
                    return v___x_1132_;
                }
            }
        }
    } else {
        let mut v_root_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: u8 = 0;
        v_root_1133_ = leanh::lean_ctor_get(v_t_1102_, 0);
        v_tail_1134_ = leanh::lean_ctor_get(v_t_1102_, 1);
        leanh::lean_inc_ref(v_diagnostic_1101_);
        v___x_1135_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_1101_, v_root_1133_, v_init_1103_);
        v___x_1136_ = lean_array_get_size(v_tail_1134_);
        v___x_1137_ = lean_nat_dec_lt(v___x_1105_, v___x_1136_);
        if v___x_1137_ == 0 {
            leanh::lean_dec_ref(v_diagnostic_1101_);
            return v___x_1135_;
        } else {
            let mut v___x_1138_: u8 = 0;
            v___x_1138_ = lean_nat_dec_le(v___x_1136_, v___x_1136_);
            if v___x_1138_ == 0 {
                if v___x_1137_ == 0 {
                    leanh::lean_dec_ref(v_diagnostic_1101_);
                    return v___x_1135_;
                } else {
                    let mut v___x_1139_: usize = 0;
                    let mut v___x_1140_: usize = 0;
                    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1139_ = 0usize;
                    v___x_1140_ = lean_usize_of_nat(v___x_1136_);
                    v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1134_, v___x_1139_, v___x_1140_, v___x_1135_);
                    return v___x_1141_;
                }
            } else {
                let mut v___x_1142_: usize = 0;
                let mut v___x_1143_: usize = 0;
                let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1142_ = 0usize;
                v___x_1143_ = lean_usize_of_nat(v___x_1136_);
                v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_1101_, v_tail_1134_, v___x_1142_, v___x_1143_, v___x_1135_);
                return v___x_1144_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(
    mut v_diagnostic_1145_: *mut leanh::LeanObject,
    mut v_t_1146_: *mut leanh::LeanObject,
    mut v_init_1147_: *mut leanh::LeanObject,
    mut v_start_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_1145_, v_t_1146_, v_init_1147_, v_start_1148_);
    leanh::lean_dec(v_start_1148_);
    leanh::lean_dec_ref(v_t_1146_);
    return v_res_1149_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = leanh::lean_unsigned_to_nat(32);
    v___x_1151_ = lean_mk_empty_array_with_capacity(v___x_1150_);
    v___x_1152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1153_: usize = 0;
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = 5usize;
    v___x_1154_ = leanh::lean_unsigned_to_nat(0);
    v___x_1155_ = leanh::lean_unsigned_to_nat(32);
    v___x_1156_ = lean_mk_empty_array_with_capacity(v___x_1155_);
    v___x_1157_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once), _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
    v___x_1158_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 1, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 2, v___x_1154_);
    leanh::lean_ctor_set(v___x_1158_, 3, v___x_1154_);
    leanh::lean_ctor_set_usize(v___x_1158_, 4, v___x_1153_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(
    mut v_diagnostic_1159_: *mut leanh::LeanObject,
    mut v___y_1160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stickyDiagsRef_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diags_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_publishedDiagsAmount_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stickyDiags_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = lean_st_ref_get(v___y_1160_);
                v_stickyDiagsRef_1163_ = leanh::lean_ctor_get(v___x_1162_, 0);
                v_diags_1164_ = leanh::lean_ctor_get(v___x_1162_, 1);
                v_publishedDiagsAmount_1165_ = leanh::lean_ctor_get(v___x_1162_, 2);
                v_isSharedCheck_1180_ = (!leanh::lean_is_exclusive(v___x_1162_)) as u8;
                if v_isSharedCheck_1180_ == 0 {
                    v___x_1167_ = v___x_1162_;
                    v_isShared_1168_ = v_isSharedCheck_1180_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_publishedDiagsAmount_1165_);
                    leanh::lean_inc(v_diags_1164_);
                    leanh::lean_inc(v_stickyDiagsRef_1163_);
                    leanh::lean_dec(v___x_1162_);
                    v___x_1167_ = leanh::lean_box(0);
                    v_isShared_1168_ = v_isSharedCheck_1180_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1169_ = lean_st_ref_take(v_stickyDiagsRef_1163_);
                v___x_1170_ = leanh::lean_unsigned_to_nat(0);
                v___x_1171_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once), _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
                leanh::lean_inc_ref(v_diagnostic_1159_);
                v_stickyDiags_1172_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_1159_, v___x_1169_, v___x_1171_, v___x_1170_);
                leanh::lean_dec(v___x_1169_);
                v___x_1173_ =
                    l_Lean_PersistentArray_push___redArg(v_stickyDiags_1172_, v_diagnostic_1159_);
                v___x_1174_ = lean_st_ref_set(v_stickyDiagsRef_1163_, v___x_1173_);
                v___x_1175_ = 0;
                if v_isShared_1168_ == 0 {
                    v___x_1177_ = v___x_1167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_stickyDiagsRef_1163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_diags_1164_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1179_,
                        2,
                        v_publishedDiagsAmount_1165_,
                    );
                    v___x_1177_ = v_reuseFailAlloc_1179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1177_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1175_,
                );
                v___x_1178_ = lean_st_ref_set(v___y_1160_, v___x_1177_);
                return v___x_1178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(
    mut v_diagnostic_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(
        v_diagnostic_1181_,
        v___y_1182_,
    );
    leanh::lean_dec(v___y_1182_);
    return v_res_1184_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(
    mut v_doc_1185_: *mut leanh::LeanObject,
    mut v_diagnostic_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diagnosticsMutex_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_diagnosticsMutex_1188_ = leanh::lean_ctor_get(v_doc_1185_, 3);
    leanh::lean_inc_ref(v_diagnosticsMutex_1188_);
    leanh::lean_dec_ref(v_doc_1185_);
    v___f_1189_ = leanh::lean_alloc_closure(
        l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1189_, 0, v_diagnostic_1186_);
    v___x_1190_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_1188_, v___f_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(
    mut v_doc_1191_: *mut leanh::LeanObject,
    mut v_diagnostic_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(
        v_doc_1191_,
        v_diagnostic_1192_,
    );
    return v_res_1194_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(
    mut v___y_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stickyDiagsRef_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diags_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = lean_st_ref_get(v___y_1195_);
    v_stickyDiagsRef_1198_ = leanh::lean_ctor_get(v___x_1197_, 0);
    leanh::lean_inc(v_stickyDiagsRef_1198_);
    v_diags_1199_ = leanh::lean_ctor_get(v___x_1197_, 1);
    leanh::lean_inc_ref(v_diags_1199_);
    leanh::lean_dec(v___x_1197_);
    v___x_1200_ = lean_st_ref_get(v_stickyDiagsRef_1198_);
    leanh::lean_dec(v_stickyDiagsRef_1198_);
    v___x_1201_ = l_Lean_PersistentArray_append___redArg(v___x_1200_, v_diags_1199_);
    leanh::lean_dec_ref(v_diags_1199_);
    return v___x_1201_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(
    mut v___y_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(
        v___y_1202_,
    );
    leanh::lean_dec(v___y_1202_);
    return v_res_1204_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(
    mut v_doc_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diagnosticsMutex_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_diagnosticsMutex_1208_ = leanh::lean_ctor_get(v_doc_1206_, 3);
    leanh::lean_inc_ref(v_diagnosticsMutex_1208_);
    leanh::lean_dec_ref(v_doc_1206_);
    v___f_1209_ =
        l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0;
    v___x_1210_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_1208_, v___f_1209_);
    return v___x_1210_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(
    mut v_doc_1211_: *mut leanh::LeanObject,
    mut v_a_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1213_ =
        l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_1211_);
    return v_res_1213_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(
    mut v___y_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stickyDiagsRef_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = lean_st_ref_get(v___y_1214_);
    v_stickyDiagsRef_1217_ = leanh::lean_ctor_get(v___x_1216_, 0);
    leanh::lean_inc(v_stickyDiagsRef_1217_);
    leanh::lean_dec(v___x_1216_);
    return v_stickyDiagsRef_1217_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_1218_);
    leanh::lean_dec(v___y_1218_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_update(
    mut v_doc_1222_: *mut leanh::LeanObject,
    mut v_newMeta_1223_: *mut leanh::LeanObject,
    mut v_newInitSnap_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diagnosticsMutex_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___f_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: u8 = 0;
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v_unused_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_diagnosticsMutex_1226_ = leanh::lean_ctor_get(v_doc_1222_, 3);
                v_isSharedCheck_1241_ = (!leanh::lean_is_exclusive(v_doc_1222_)) as u8;
                if v_isSharedCheck_1241_ == 0 {
                    v_unused_1242_ = leanh::lean_ctor_get(v_doc_1222_, 2);
                    leanh::lean_dec(v_unused_1242_);
                    v_unused_1243_ = leanh::lean_ctor_get(v_doc_1222_, 1);
                    leanh::lean_dec(v_unused_1243_);
                    v_unused_1244_ = leanh::lean_ctor_get(v_doc_1222_, 0);
                    leanh::lean_dec(v_unused_1244_);
                    v___x_1228_ = v_doc_1222_;
                    v_isShared_1229_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diagnosticsMutex_1226_);
                    leanh::lean_dec(v_doc_1222_);
                    v___x_1228_ = leanh::lean_box(0);
                    v_isShared_1229_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1230_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0;
                v___x_1231_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_1226_, v___f_1230_);
                v___x_1232_ = leanh::lean_unsigned_to_nat(0);
                v___x_1233_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once), _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
                v___x_1234_ = 0;
                v___x_1235_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_1235_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1235_, 1, v___x_1233_);
                leanh::lean_ctor_set(v___x_1235_, 2, v___x_1232_);
                leanh::lean_ctor_set_uint8(
                    v___x_1235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1234_,
                );
                v___x_1236_ = l_Std_Mutex_new___redArg(v___x_1235_);
                leanh::lean_inc_ref(v_newInitSnap_1224_);
                v___x_1237_ =
                    l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(
                        v_newInitSnap_1224_,
                    );
                if v_isShared_1229_ == 0 {
                    leanh::lean_ctor_set(v___x_1228_, 3, v___x_1236_);
                    leanh::lean_ctor_set(v___x_1228_, 2, v___x_1237_);
                    leanh::lean_ctor_set(v___x_1228_, 1, v_newInitSnap_1224_);
                    leanh::lean_ctor_set(v___x_1228_, 0, v_newMeta_1223_);
                    v___x_1239_ = v___x_1228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_newMeta_1223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_newInitSnap_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 3, v___x_1236_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(
    mut v_doc_1245_: *mut leanh::LeanObject,
    mut v_newMeta_1246_: *mut leanh::LeanObject,
    mut v_newInitSnap_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(
        v_doc_1245_,
        v_newMeta_1246_,
        v_newInitSnap_1247_,
    );
    return v_res_1249_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(
    mut v_as_1250_: *mut leanh::LeanObject,
    mut v_i_1251_: usize,
    mut v_stop_1252_: usize,
    mut v_b_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: usize = 0;
    let mut v___x_1259_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1254_ = lean_usize_dec_eq(v_i_1251_, v_stop_1252_);
                if v___x_1254_ == 0 {
                    v___x_1255_ = lean_array_uget_borrowed(v_as_1250_, v_i_1251_);
                    leanh::lean_inc(v___x_1255_);
                    v___x_1256_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_1255_);
                    v___x_1257_ = lean_array_push(v_b_1253_, v___x_1256_);
                    v___x_1258_ = 1usize;
                    v___x_1259_ = lean_usize_add(v_i_1251_, v___x_1258_);
                    v_i_1251_ = v___x_1259_;
                    v_b_1253_ = v___x_1257_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1253_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(
    mut v_as_1261_: *mut leanh::LeanObject,
    mut v_i_1262_: *mut leanh::LeanObject,
    mut v_stop_1263_: *mut leanh::LeanObject,
    mut v_b_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1265_: usize = 0;
    let mut v_stop_boxed_1266_: usize = 0;
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1265_ = leanh::lean_unbox_usize(v_i_1262_);
    leanh::lean_dec(v_i_1262_);
    v_stop_boxed_1266_ = leanh::lean_unbox_usize(v_stop_1263_);
    leanh::lean_dec(v_stop_1263_);
    v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_1261_, v_i_boxed_1265_, v_stop_boxed_1266_, v_b_1264_);
    leanh::lean_dec_ref(v_as_1261_);
    return v_res_1267_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(
    mut v_x_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1268_) == 0 {
        let mut v_cs_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: u8 = 0;
        v_cs_1270_ = leanh::lean_ctor_get(v_x_1268_, 0);
        v___x_1271_ = leanh::lean_unsigned_to_nat(0);
        v___x_1272_ = lean_array_get_size(v_cs_1270_);
        v___x_1273_ = lean_nat_dec_lt(v___x_1271_, v___x_1272_);
        if v___x_1273_ == 0 {
            return v_x_1269_;
        } else {
            let mut v___x_1274_: u8 = 0;
            v___x_1274_ = lean_nat_dec_le(v___x_1272_, v___x_1272_);
            if v___x_1274_ == 0 {
                if v___x_1273_ == 0 {
                    return v_x_1269_;
                } else {
                    let mut v___x_1275_: usize = 0;
                    let mut v___x_1276_: usize = 0;
                    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1275_ = 0usize;
                    v___x_1276_ = lean_usize_of_nat(v___x_1272_);
                    v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_1270_, v___x_1275_, v___x_1276_, v_x_1269_);
                    return v___x_1277_;
                }
            } else {
                let mut v___x_1278_: usize = 0;
                let mut v___x_1279_: usize = 0;
                let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1278_ = 0usize;
                v___x_1279_ = lean_usize_of_nat(v___x_1272_);
                v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_1270_, v___x_1278_, v___x_1279_, v_x_1269_);
                return v___x_1280_;
            }
        }
    } else {
        let mut v_vs_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: u8 = 0;
        v_vs_1281_ = leanh::lean_ctor_get(v_x_1268_, 0);
        v___x_1282_ = leanh::lean_unsigned_to_nat(0);
        v___x_1283_ = lean_array_get_size(v_vs_1281_);
        v___x_1284_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
        if v___x_1284_ == 0 {
            return v_x_1269_;
        } else {
            let mut v___x_1285_: u8 = 0;
            v___x_1285_ = lean_nat_dec_le(v___x_1283_, v___x_1283_);
            if v___x_1285_ == 0 {
                if v___x_1284_ == 0 {
                    return v_x_1269_;
                } else {
                    let mut v___x_1286_: usize = 0;
                    let mut v___x_1287_: usize = 0;
                    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1286_ = 0usize;
                    v___x_1287_ = lean_usize_of_nat(v___x_1283_);
                    v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_1281_, v___x_1286_, v___x_1287_, v_x_1269_);
                    return v___x_1288_;
                }
            } else {
                let mut v___x_1289_: usize = 0;
                let mut v___x_1290_: usize = 0;
                let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1289_ = 0usize;
                v___x_1290_ = lean_usize_of_nat(v___x_1283_);
                v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_1281_, v___x_1289_, v___x_1290_, v_x_1269_);
                return v___x_1291_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(
    mut v_as_1292_: *mut leanh::LeanObject,
    mut v_i_1293_: usize,
    mut v_stop_1294_: usize,
    mut v_b_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = lean_usize_dec_eq(v_i_1293_, v_stop_1294_);
                if v___x_1296_ == 0 {
                    v___x_1297_ = lean_array_uget_borrowed(v_as_1292_, v_i_1293_);
                    v___x_1298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_1297_, v_b_1295_);
                    v___x_1299_ = 1usize;
                    v___x_1300_ = lean_usize_add(v_i_1293_, v___x_1299_);
                    v_i_1293_ = v___x_1300_;
                    v_b_1295_ = v___x_1298_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1295_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(
    mut v_as_1302_: *mut leanh::LeanObject,
    mut v_i_1303_: *mut leanh::LeanObject,
    mut v_stop_1304_: *mut leanh::LeanObject,
    mut v_b_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1306_: usize = 0;
    let mut v_stop_boxed_1307_: usize = 0;
    let mut v_res_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1306_ = leanh::lean_unbox_usize(v_i_1303_);
    leanh::lean_dec(v_i_1303_);
    v_stop_boxed_1307_ = leanh::lean_unbox_usize(v_stop_1304_);
    leanh::lean_dec(v_stop_1304_);
    v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_1302_, v_i_boxed_1306_, v_stop_boxed_1307_, v_b_1305_);
    leanh::lean_dec_ref(v_as_1302_);
    return v_res_1308_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(
    mut v_x_1309_: *mut leanh::LeanObject,
    mut v_x_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_1309_, v_x_1310_);
    leanh::lean_dec_ref(v_x_1309_);
    return v_res_1311_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(
    mut v_x_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: usize,
    mut v_x_1314_: usize,
    mut v_x_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1312_) == 0 {
        let mut v_cs_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: usize = 0;
        let mut v_j_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: usize = 0;
        let mut v___x_1322_: usize = 0;
        let mut v___x_1323_: usize = 0;
        let mut v___x_1324_: usize = 0;
        let mut v___x_1325_: usize = 0;
        let mut v___x_1326_: usize = 0;
        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: u8 = 0;
        v_cs_1316_ = leanh::lean_ctor_get(v_x_1312_, 0);
        v___x_1317_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
        v___x_1318_ = lean_usize_shift_right(v_x_1313_, v_x_1314_);
        v_j_1319_ = lean_usize_to_nat(v___x_1318_);
        v___x_1320_ = lean_array_get_borrowed(v___x_1317_, v_cs_1316_, v_j_1319_);
        v___x_1321_ = 1usize;
        v___x_1322_ = lean_usize_shift_left(v___x_1321_, v_x_1314_);
        v___x_1323_ = lean_usize_sub(v___x_1322_, v___x_1321_);
        v___x_1324_ = lean_usize_land(v_x_1313_, v___x_1323_);
        v___x_1325_ = 5usize;
        v___x_1326_ = lean_usize_sub(v_x_1314_, v___x_1325_);
        v___x_1327_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_1320_, v___x_1324_, v___x_1326_, v_x_1315_);
        v___x_1328_ = leanh::lean_unsigned_to_nat(1);
        v___x_1329_ = lean_nat_add(v_j_1319_, v___x_1328_);
        leanh::lean_dec(v_j_1319_);
        v___x_1330_ = lean_array_get_size(v_cs_1316_);
        v___x_1331_ = lean_nat_dec_lt(v___x_1329_, v___x_1330_);
        if v___x_1331_ == 0 {
            leanh::lean_dec(v___x_1329_);
            return v___x_1327_;
        } else {
            let mut v___x_1332_: u8 = 0;
            v___x_1332_ = lean_nat_dec_le(v___x_1330_, v___x_1330_);
            if v___x_1332_ == 0 {
                if v___x_1331_ == 0 {
                    leanh::lean_dec(v___x_1329_);
                    return v___x_1327_;
                } else {
                    let mut v___x_1333_: usize = 0;
                    let mut v___x_1334_: usize = 0;
                    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1333_ = lean_usize_of_nat(v___x_1329_);
                    leanh::lean_dec(v___x_1329_);
                    v___x_1334_ = lean_usize_of_nat(v___x_1330_);
                    v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_1316_, v___x_1333_, v___x_1334_, v___x_1327_);
                    return v___x_1335_;
                }
            } else {
                let mut v___x_1336_: usize = 0;
                let mut v___x_1337_: usize = 0;
                let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1336_ = lean_usize_of_nat(v___x_1329_);
                leanh::lean_dec(v___x_1329_);
                v___x_1337_ = lean_usize_of_nat(v___x_1330_);
                v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_1316_, v___x_1336_, v___x_1337_, v___x_1327_);
                return v___x_1338_;
            }
        }
    } else {
        let mut v_vs_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: u8 = 0;
        v_vs_1339_ = leanh::lean_ctor_get(v_x_1312_, 0);
        v___x_1340_ = lean_usize_to_nat(v_x_1313_);
        v___x_1341_ = lean_array_get_size(v_vs_1339_);
        v___x_1342_ = lean_nat_dec_lt(v___x_1340_, v___x_1341_);
        if v___x_1342_ == 0 {
            leanh::lean_dec(v___x_1340_);
            return v_x_1315_;
        } else {
            let mut v___x_1343_: u8 = 0;
            v___x_1343_ = lean_nat_dec_le(v___x_1341_, v___x_1341_);
            if v___x_1343_ == 0 {
                if v___x_1342_ == 0 {
                    leanh::lean_dec(v___x_1340_);
                    return v_x_1315_;
                } else {
                    let mut v___x_1344_: usize = 0;
                    let mut v___x_1345_: usize = 0;
                    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1344_ = lean_usize_of_nat(v___x_1340_);
                    leanh::lean_dec(v___x_1340_);
                    v___x_1345_ = lean_usize_of_nat(v___x_1341_);
                    v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_1339_, v___x_1344_, v___x_1345_, v_x_1315_);
                    return v___x_1346_;
                }
            } else {
                let mut v___x_1347_: usize = 0;
                let mut v___x_1348_: usize = 0;
                let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1347_ = lean_usize_of_nat(v___x_1340_);
                leanh::lean_dec(v___x_1340_);
                v___x_1348_ = lean_usize_of_nat(v___x_1341_);
                v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_1339_, v___x_1347_, v___x_1348_, v_x_1315_);
                return v___x_1349_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(
    mut v_x_1350_: *mut leanh::LeanObject,
    mut v_x_1351_: *mut leanh::LeanObject,
    mut v_x_1352_: *mut leanh::LeanObject,
    mut v_x_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3065__boxed_1354_: usize = 0;
    let mut v_x_3066__boxed_1355_: usize = 0;
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3065__boxed_1354_ = leanh::lean_unbox_usize(v_x_1351_);
    leanh::lean_dec(v_x_1351_);
    v_x_3066__boxed_1355_ = leanh::lean_unbox_usize(v_x_1352_);
    leanh::lean_dec(v_x_1352_);
    v_res_1356_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_1350_, v_x_3065__boxed_1354_, v_x_3066__boxed_1355_, v_x_1353_);
    leanh::lean_dec_ref(v_x_1350_);
    return v_res_1356_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(
    mut v_t_1357_: *mut leanh::LeanObject,
    mut v_init_1358_: *mut leanh::LeanObject,
    mut v_start_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    v___x_1360_ = leanh::lean_unsigned_to_nat(0);
    v___x_1361_ = lean_nat_dec_eq(v_start_1359_, v___x_1360_);
    if v___x_1361_ == 0 {
        let mut v_root_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_1364_: usize = 0;
        let mut v_tailOff_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: u8 = 0;
        v_root_1362_ = leanh::lean_ctor_get(v_t_1357_, 0);
        v_tail_1363_ = leanh::lean_ctor_get(v_t_1357_, 1);
        v_shift_1364_ = leanh::lean_ctor_get_usize(v_t_1357_, 4);
        v_tailOff_1365_ = leanh::lean_ctor_get(v_t_1357_, 3);
        v___x_1366_ = lean_nat_dec_le(v_tailOff_1365_, v_start_1359_);
        if v___x_1366_ == 0 {
            let mut v___x_1367_: usize = 0;
            let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1370_: u8 = 0;
            v___x_1367_ = lean_usize_of_nat(v_start_1359_);
            v___x_1368_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_1362_, v___x_1367_, v_shift_1364_, v_init_1358_);
            v___x_1369_ = lean_array_get_size(v_tail_1363_);
            v___x_1370_ = lean_nat_dec_lt(v___x_1360_, v___x_1369_);
            if v___x_1370_ == 0 {
                return v___x_1368_;
            } else {
                let mut v___x_1371_: u8 = 0;
                v___x_1371_ = lean_nat_dec_le(v___x_1369_, v___x_1369_);
                if v___x_1371_ == 0 {
                    if v___x_1370_ == 0 {
                        return v___x_1368_;
                    } else {
                        let mut v___x_1372_: usize = 0;
                        let mut v___x_1373_: usize = 0;
                        let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1372_ = 0usize;
                        v___x_1373_ = lean_usize_of_nat(v___x_1369_);
                        v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1363_, v___x_1372_, v___x_1373_, v___x_1368_);
                        return v___x_1374_;
                    }
                } else {
                    let mut v___x_1375_: usize = 0;
                    let mut v___x_1376_: usize = 0;
                    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1375_ = 0usize;
                    v___x_1376_ = lean_usize_of_nat(v___x_1369_);
                    v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1363_, v___x_1375_, v___x_1376_, v___x_1368_);
                    return v___x_1377_;
                }
            }
        } else {
            let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: u8 = 0;
            v___x_1378_ = lean_nat_sub(v_start_1359_, v_tailOff_1365_);
            v___x_1379_ = lean_array_get_size(v_tail_1363_);
            v___x_1380_ = lean_nat_dec_lt(v___x_1378_, v___x_1379_);
            if v___x_1380_ == 0 {
                leanh::lean_dec(v___x_1378_);
                return v_init_1358_;
            } else {
                let mut v___x_1381_: u8 = 0;
                v___x_1381_ = lean_nat_dec_le(v___x_1379_, v___x_1379_);
                if v___x_1381_ == 0 {
                    if v___x_1380_ == 0 {
                        leanh::lean_dec(v___x_1378_);
                        return v_init_1358_;
                    } else {
                        let mut v___x_1382_: usize = 0;
                        let mut v___x_1383_: usize = 0;
                        let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1382_ = lean_usize_of_nat(v___x_1378_);
                        leanh::lean_dec(v___x_1378_);
                        v___x_1383_ = lean_usize_of_nat(v___x_1379_);
                        v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1363_, v___x_1382_, v___x_1383_, v_init_1358_);
                        return v___x_1384_;
                    }
                } else {
                    let mut v___x_1385_: usize = 0;
                    let mut v___x_1386_: usize = 0;
                    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1385_ = lean_usize_of_nat(v___x_1378_);
                    leanh::lean_dec(v___x_1378_);
                    v___x_1386_ = lean_usize_of_nat(v___x_1379_);
                    v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1363_, v___x_1385_, v___x_1386_, v_init_1358_);
                    return v___x_1387_;
                }
            }
        }
    } else {
        let mut v_root_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: u8 = 0;
        v_root_1388_ = leanh::lean_ctor_get(v_t_1357_, 0);
        v_tail_1389_ = leanh::lean_ctor_get(v_t_1357_, 1);
        v___x_1390_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_1388_, v_init_1358_);
        v___x_1391_ = lean_array_get_size(v_tail_1389_);
        v___x_1392_ = lean_nat_dec_lt(v___x_1360_, v___x_1391_);
        if v___x_1392_ == 0 {
            return v___x_1390_;
        } else {
            let mut v___x_1393_: u8 = 0;
            v___x_1393_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
            if v___x_1393_ == 0 {
                if v___x_1392_ == 0 {
                    return v___x_1390_;
                } else {
                    let mut v___x_1394_: usize = 0;
                    let mut v___x_1395_: usize = 0;
                    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1394_ = 0usize;
                    v___x_1395_ = lean_usize_of_nat(v___x_1391_);
                    v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1389_, v___x_1394_, v___x_1395_, v___x_1390_);
                    return v___x_1396_;
                }
            } else {
                let mut v___x_1397_: usize = 0;
                let mut v___x_1398_: usize = 0;
                let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1397_ = 0usize;
                v___x_1398_ = lean_usize_of_nat(v___x_1391_);
                v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1389_, v___x_1397_, v___x_1398_, v___x_1390_);
                return v___x_1399_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(
    mut v_t_1400_: *mut leanh::LeanObject,
    mut v_init_1401_: *mut leanh::LeanObject,
    mut v_start_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_1400_, v_init_1401_, v_start_1402_);
    leanh::lean_dec(v_start_1402_);
    leanh::lean_dec_ref(v_t_1400_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(
    mut v_t_1404_: *mut leanh::LeanObject,
    mut v_init_1405_: *mut leanh::LeanObject,
    mut v_start_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    v___x_1407_ = leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = lean_nat_dec_eq(v_start_1406_, v___x_1407_);
    if v___x_1408_ == 0 {
        let mut v_root_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_1411_: usize = 0;
        let mut v_tailOff_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: u8 = 0;
        v_root_1409_ = leanh::lean_ctor_get(v_t_1404_, 0);
        v_tail_1410_ = leanh::lean_ctor_get(v_t_1404_, 1);
        v_shift_1411_ = leanh::lean_ctor_get_usize(v_t_1404_, 4);
        v_tailOff_1412_ = leanh::lean_ctor_get(v_t_1404_, 3);
        v___x_1413_ = lean_nat_dec_le(v_tailOff_1412_, v_start_1406_);
        if v___x_1413_ == 0 {
            let mut v___x_1414_: usize = 0;
            let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1417_: u8 = 0;
            v___x_1414_ = lean_usize_of_nat(v_start_1406_);
            v___x_1415_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_1409_, v___x_1414_, v_shift_1411_, v_init_1405_);
            v___x_1416_ = lean_array_get_size(v_tail_1410_);
            v___x_1417_ = lean_nat_dec_lt(v___x_1407_, v___x_1416_);
            if v___x_1417_ == 0 {
                return v___x_1415_;
            } else {
                let mut v___x_1418_: u8 = 0;
                v___x_1418_ = lean_nat_dec_le(v___x_1416_, v___x_1416_);
                if v___x_1418_ == 0 {
                    if v___x_1417_ == 0 {
                        return v___x_1415_;
                    } else {
                        let mut v___x_1419_: usize = 0;
                        let mut v___x_1420_: usize = 0;
                        let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1419_ = 0usize;
                        v___x_1420_ = lean_usize_of_nat(v___x_1416_);
                        v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1410_, v___x_1419_, v___x_1420_, v___x_1415_);
                        return v___x_1421_;
                    }
                } else {
                    let mut v___x_1422_: usize = 0;
                    let mut v___x_1423_: usize = 0;
                    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1422_ = 0usize;
                    v___x_1423_ = lean_usize_of_nat(v___x_1416_);
                    v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1410_, v___x_1422_, v___x_1423_, v___x_1415_);
                    return v___x_1424_;
                }
            }
        } else {
            let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1427_: u8 = 0;
            v___x_1425_ = lean_nat_sub(v_start_1406_, v_tailOff_1412_);
            v___x_1426_ = lean_array_get_size(v_tail_1410_);
            v___x_1427_ = lean_nat_dec_lt(v___x_1425_, v___x_1426_);
            if v___x_1427_ == 0 {
                leanh::lean_dec(v___x_1425_);
                return v_init_1405_;
            } else {
                let mut v___x_1428_: u8 = 0;
                v___x_1428_ = lean_nat_dec_le(v___x_1426_, v___x_1426_);
                if v___x_1428_ == 0 {
                    if v___x_1427_ == 0 {
                        leanh::lean_dec(v___x_1425_);
                        return v_init_1405_;
                    } else {
                        let mut v___x_1429_: usize = 0;
                        let mut v___x_1430_: usize = 0;
                        let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1429_ = lean_usize_of_nat(v___x_1425_);
                        leanh::lean_dec(v___x_1425_);
                        v___x_1430_ = lean_usize_of_nat(v___x_1426_);
                        v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1410_, v___x_1429_, v___x_1430_, v_init_1405_);
                        return v___x_1431_;
                    }
                } else {
                    let mut v___x_1432_: usize = 0;
                    let mut v___x_1433_: usize = 0;
                    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1432_ = lean_usize_of_nat(v___x_1425_);
                    leanh::lean_dec(v___x_1425_);
                    v___x_1433_ = lean_usize_of_nat(v___x_1426_);
                    v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1410_, v___x_1432_, v___x_1433_, v_init_1405_);
                    return v___x_1434_;
                }
            }
        }
    } else {
        let mut v_root_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: u8 = 0;
        v_root_1435_ = leanh::lean_ctor_get(v_t_1404_, 0);
        v_tail_1436_ = leanh::lean_ctor_get(v_t_1404_, 1);
        v___x_1437_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_1435_, v_init_1405_);
        v___x_1438_ = lean_array_get_size(v_tail_1436_);
        v___x_1439_ = lean_nat_dec_lt(v___x_1407_, v___x_1438_);
        if v___x_1439_ == 0 {
            return v___x_1437_;
        } else {
            let mut v___x_1440_: u8 = 0;
            v___x_1440_ = lean_nat_dec_le(v___x_1438_, v___x_1438_);
            if v___x_1440_ == 0 {
                if v___x_1439_ == 0 {
                    return v___x_1437_;
                } else {
                    let mut v___x_1441_: usize = 0;
                    let mut v___x_1442_: usize = 0;
                    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1441_ = 0usize;
                    v___x_1442_ = lean_usize_of_nat(v___x_1438_);
                    v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1436_, v___x_1441_, v___x_1442_, v___x_1437_);
                    return v___x_1443_;
                }
            } else {
                let mut v___x_1444_: usize = 0;
                let mut v___x_1445_: usize = 0;
                let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1444_ = 0usize;
                v___x_1445_ = lean_usize_of_nat(v___x_1438_);
                v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_1436_, v___x_1444_, v___x_1445_, v___x_1437_);
                return v___x_1446_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(
    mut v_t_1447_: *mut leanh::LeanObject,
    mut v_init_1448_: *mut leanh::LeanObject,
    mut v_start_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_1447_, v_init_1448_, v_start_1449_);
    leanh::lean_dec(v_start_1449_);
    leanh::lean_dec_ref(v_t_1447_);
    return v_res_1450_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(
    mut v_meta_1453_: *mut leanh::LeanObject,
    mut v_writeDiagnostics_1454_: *mut leanh::LeanObject,
    mut v_incrementalDiagnosticSupport_1455_: u8,
    mut v___y_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: u8 = 0;
    let mut v_stickyDiagsRef_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diags_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_publishedDiagsAmount_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_isIncremental_1492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1469_ = lean_st_ref_get(v___y_1456_);
                if v_incrementalDiagnosticSupport_1455_ == 0 {
                    v___y_1471_ = v_incrementalDiagnosticSupport_1455_;
                    state = 3;
                    continue;
                } else {
                    v_isIncremental_1492_ = leanh::lean_ctor_get_uint8(
                        v___x_1469_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_1471_ = v_isIncremental_1492_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1461_ = l_Lean_Server_mkPublishDiagnosticsNotification(
                    v_meta_1453_,
                    v___y_1459_,
                    v___y_1460_,
                );
                v___x_1462_ = leanh::lean_apply_2(
                    v_writeDiagnostics_1454_,
                    v___x_1461_,
                    leanh::lean_box(0),
                );
                return v___x_1462_;
            }
            2 => {
                if v_incrementalDiagnosticSupport_1455_ == 0 {
                    v___x_1466_ = leanh::lean_box(0);
                    v___y_1459_ = v_fst_1464_;
                    v___y_1460_ = v___x_1466_;
                    state = 1;
                    continue;
                } else {
                    v___x_1467_ = leanh::lean_box((v_snd_1465_) as usize);
                    v___x_1468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
                    v___y_1459_ = v_fst_1464_;
                    v___y_1460_ = v___x_1468_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_stickyDiagsRef_1472_ = leanh::lean_ctor_get(v___x_1469_, 0);
                v_diags_1473_ = leanh::lean_ctor_get(v___x_1469_, 1);
                v_publishedDiagsAmount_1474_ = leanh::lean_ctor_get(v___x_1469_, 2);
                v_isSharedCheck_1491_ = (!leanh::lean_is_exclusive(v___x_1469_)) as u8;
                if v_isSharedCheck_1491_ == 0 {
                    v___x_1476_ = v___x_1469_;
                    v_isShared_1477_ = v_isSharedCheck_1491_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_publishedDiagsAmount_1474_);
                    leanh::lean_inc(v_diags_1473_);
                    leanh::lean_inc(v_stickyDiagsRef_1472_);
                    leanh::lean_dec(v___x_1469_);
                    v___x_1476_ = leanh::lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1491_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1478_ = lean_st_ref_get(v_stickyDiagsRef_1472_);
                v_size_1479_ = leanh::lean_ctor_get(v_diags_1473_, 2);
                v___x_1480_ = 1;
                leanh::lean_inc(v_size_1479_);
                leanh::lean_inc_ref(v_diags_1473_);
                if v_isShared_1477_ == 0 {
                    leanh::lean_ctor_set(v___x_1476_, 2, v_size_1479_);
                    v___x_1482_ = v___x_1476_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_stickyDiagsRef_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_diags_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_size_1479_);
                    v___x_1482_ = v_reuseFailAlloc_1490_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1482_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1480_,
                );
                v___x_1483_ = lean_st_ref_set(v___y_1456_, v___x_1482_);
                if v___y_1471_ == 0 {
                    leanh::lean_dec(v_publishedDiagsAmount_1474_);
                    v___x_1484_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1485_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0;
                    v___x_1486_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_1478_, v___x_1485_, v___x_1484_);
                    leanh::lean_dec(v___x_1478_);
                    v___x_1487_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_1473_, v___x_1486_, v___x_1484_);
                    leanh::lean_dec_ref(v_diags_1473_);
                    v_fst_1464_ = v___x_1487_;
                    v_snd_1465_ = v___y_1471_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1478_);
                    v___x_1488_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0;
                    v___x_1489_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_1473_, v___x_1488_, v_publishedDiagsAmount_1474_);
                    leanh::lean_dec(v_publishedDiagsAmount_1474_);
                    leanh::lean_dec_ref(v_diags_1473_);
                    v_fst_1464_ = v___x_1489_;
                    v_snd_1465_ = v___x_1480_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(
    mut v_meta_1493_: *mut leanh::LeanObject,
    mut v_writeDiagnostics_1494_: *mut leanh::LeanObject,
    mut v_incrementalDiagnosticSupport_1495_: *mut leanh::LeanObject,
    mut v___y_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_incrementalDiagnosticSupport_boxed_1498_: u8 = 0;
    let mut v_res_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_incrementalDiagnosticSupport_boxed_1498_ =
        (leanh::lean_unbox(v_incrementalDiagnosticSupport_1495_) as u8);
    v_res_1499_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(
        v_meta_1493_,
        v_writeDiagnostics_1494_,
        v_incrementalDiagnosticSupport_boxed_1498_,
        v___y_1496_,
    );
    leanh::lean_dec(v___y_1496_);
    return v_res_1499_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(
    mut v_doc_1500_: *mut leanh::LeanObject,
    mut v_incrementalDiagnosticSupport_1501_: u8,
    mut v_writeDiagnostics_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_meta_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnosticsMutex_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_meta_1504_ = leanh::lean_ctor_get(v_doc_1500_, 0);
    leanh::lean_inc_ref(v_meta_1504_);
    v_diagnosticsMutex_1505_ = leanh::lean_ctor_get(v_doc_1500_, 3);
    leanh::lean_inc_ref(v_diagnosticsMutex_1505_);
    leanh::lean_dec_ref(v_doc_1500_);
    v___x_1506_ = leanh::lean_box((v_incrementalDiagnosticSupport_1501_) as usize);
    v___f_1507_ = leanh::lean_alloc_closure(
        l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_1507_, 0, v_meta_1504_);
    leanh::lean_closure_set(v___f_1507_, 1, v_writeDiagnostics_1502_);
    leanh::lean_closure_set(v___f_1507_, 2, v___x_1506_);
    v___x_1508_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_1505_, v___f_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(
    mut v_doc_1509_: *mut leanh::LeanObject,
    mut v_incrementalDiagnosticSupport_1510_: *mut leanh::LeanObject,
    mut v_writeDiagnostics_1511_: *mut leanh::LeanObject,
    mut v_a_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_incrementalDiagnosticSupport_boxed_1513_: u8 = 0;
    let mut v_res_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_incrementalDiagnosticSupport_boxed_1513_ =
        (leanh::lean_unbox(v_incrementalDiagnosticSupport_1510_) as u8);
    v_res_1514_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(
        v_doc_1509_,
        v_incrementalDiagnosticSupport_boxed_1513_,
        v_writeDiagnostics_1511_,
    );
    return v_res_1514_;
}
pub unsafe fn l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(
    mut v_ed_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toEditableDocumentCore_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v_meta_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut v_unused_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toEditableDocumentCore_1516_ = leanh::lean_ctor_get(v_ed_1515_, 0);
                v_isSharedCheck_1527_ = (!leanh::lean_is_exclusive(v_ed_1515_)) as u8;
                if v_isSharedCheck_1527_ == 0 {
                    v_unused_1528_ = leanh::lean_ctor_get(v_ed_1515_, 1);
                    leanh::lean_dec(v_unused_1528_);
                    v___x_1518_ = v_ed_1515_;
                    v_isShared_1519_ = v_isSharedCheck_1527_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toEditableDocumentCore_1516_);
                    leanh::lean_dec(v_ed_1515_);
                    v___x_1518_ = leanh::lean_box(0);
                    v_isShared_1519_ = v_isSharedCheck_1527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_meta_1520_ = leanh::lean_ctor_get(v_toEditableDocumentCore_1516_, 0);
                leanh::lean_inc_ref(v_meta_1520_);
                leanh::lean_dec_ref(v_toEditableDocumentCore_1516_);
                v_uri_1521_ = leanh::lean_ctor_get(v_meta_1520_, 0);
                leanh::lean_inc_ref(v_uri_1521_);
                v_version_1522_ = leanh::lean_ctor_get(v_meta_1520_, 2);
                leanh::lean_inc(v_version_1522_);
                leanh::lean_dec_ref(v_meta_1520_);
                v___x_1523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1523_, 0, v_version_1522_);
                if v_isShared_1519_ == 0 {
                    leanh::lean_ctor_set(v___x_1518_, 1, v___x_1523_);
                    leanh::lean_ctor_set(v___x_1518_, 0, v_uri_1521_);
                    v___x_1525_ = v___x_1518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_uri_1521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs()
-> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = leanh::lean_unsigned_to_nat(30000);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1530_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_RpcSession_new___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_RpcSession_new___closed__0_once),
        _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0,
    );
    v___x_1532_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_new(
    mut v_wireFormat_1533_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1535_: usize = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u64 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: usize = 0;
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_a_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1535_ = 8usize;
                v___x_1536_ = lean_io_get_random_bytes(v___x_1535_);
                if leanh::lean_obj_tag(v___x_1536_) == 0 {
                    v_a_1537_ = leanh::lean_ctor_get(v___x_1536_, 0);
                    v_isSharedCheck_1554_ = (!leanh::lean_is_exclusive(v___x_1536_)) as u8;
                    if v_isSharedCheck_1554_ == 0 {
                        v___x_1539_ = v___x_1536_;
                        v_isShared_1540_ = v_isSharedCheck_1554_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1537_);
                        leanh::lean_dec(v___x_1536_);
                        v___x_1539_ = leanh::lean_box(0);
                        v_isShared_1540_ = v_isSharedCheck_1554_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1555_ = leanh::lean_ctor_get(v___x_1536_, 0);
                    v_isSharedCheck_1562_ = (!leanh::lean_is_exclusive(v___x_1536_)) as u8;
                    if v_isSharedCheck_1562_ == 0 {
                        v___x_1557_ = v___x_1536_;
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1555_);
                        leanh::lean_dec(v___x_1536_);
                        v___x_1557_ = leanh::lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1541_ = lean_io_mono_ms_now();
                v___x_1542_ = l_ByteArray_toUInt64LE_x21(v_a_1537_);
                leanh::lean_dec(v_a_1537_);
                v___x_1543_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_RpcSession_new___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_FileWorker_RpcSession_new___closed__1_once
                    ),
                    _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1,
                );
                v___x_1544_ = 0usize;
                v___x_1545_ = leanh::lean_alloc_ctor(
                    0,
                    2,
                    (core::mem::size_of::<usize>() * 1 + 1) as u32,
                );
                leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                leanh::lean_ctor_set(v___x_1545_, 1, v___x_1543_);
                leanh::lean_ctor_set_usize(v___x_1545_, 2, v___x_1544_);
                leanh::lean_ctor_set_uint8(
                    v___x_1545_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_wireFormat_1533_,
                );
                v___x_1546_ = leanh::lean_unsigned_to_nat(30000);
                v___x_1547_ = lean_nat_add(v___x_1541_, v___x_1546_);
                leanh::lean_dec(v___x_1541_);
                v___x_1548_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1548_, 0, v___x_1545_);
                leanh::lean_ctor_set(v___x_1548_, 1, v___x_1547_);
                v___x_1549_ = leanh::lean_box_uint64(v___x_1542_);
                v___x_1550_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1550_, 0, v___x_1549_);
                leanh::lean_ctor_set(v___x_1550_, 1, v___x_1548_);
                if v_isShared_1540_ == 0 {
                    leanh::lean_ctor_set(v___x_1539_, 0, v___x_1550_);
                    v___x_1552_ = v___x_1539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
                    v___x_1552_ = v_reuseFailAlloc_1553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1552_;
            }
            3 => {
                if v_isShared_1558_ == 0 {
                    v___x_1560_ = v___x_1557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_new___boxed(
    mut v_wireFormat_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_wireFormat_boxed_1565_: u8 = 0;
    let mut v_res_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_wireFormat_boxed_1565_ = (leanh::lean_unbox(v_wireFormat_1563_) as u8);
    v_res_1566_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_1565_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_keptAlive(
    mut v_monoMsNow_1567_: *mut leanh::LeanObject,
    mut v_s_1568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_objects_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v_unused_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_objects_1569_ = leanh::lean_ctor_get(v_s_1568_, 0);
                v_isSharedCheck_1578_ = (!leanh::lean_is_exclusive(v_s_1568_)) as u8;
                if v_isSharedCheck_1578_ == 0 {
                    v_unused_1579_ = leanh::lean_ctor_get(v_s_1568_, 1);
                    leanh::lean_dec(v_unused_1579_);
                    v___x_1571_ = v_s_1568_;
                    v_isShared_1572_ = v_isSharedCheck_1578_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_objects_1569_);
                    leanh::lean_dec(v_s_1568_);
                    v___x_1571_ = leanh::lean_box(0);
                    v_isShared_1572_ = v_isSharedCheck_1578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1573_ = leanh::lean_unsigned_to_nat(30000);
                v___x_1574_ = lean_nat_add(v_monoMsNow_1567_, v___x_1573_);
                if v_isShared_1572_ == 0 {
                    leanh::lean_ctor_set(v___x_1571_, 1, v___x_1574_);
                    v___x_1576_ = v___x_1571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_objects_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v___x_1574_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(
    mut v_monoMsNow_1580_: *mut leanh::LeanObject,
    mut v_s_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1582_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_1580_, v_s_1581_);
    leanh::lean_dec(v_monoMsNow_1580_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_hasExpired(
    mut v_s_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expireTime_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = lean_io_mono_ms_now();
    v_expireTime_1586_ = leanh::lean_ctor_get(v_s_1583_, 1);
    v___x_1587_ = lean_nat_dec_le(v_expireTime_1586_, v___x_1585_);
    leanh::lean_dec(v___x_1585_);
    v___x_1588_ = leanh::lean_box((v___x_1587_) as usize);
    v___x_1589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1589_, 0, v___x_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(
    mut v_s_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_1590_);
    leanh::lean_dec_ref(v_s_1590_);
    return v_res_1592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_Utils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Snapshots(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_AsyncList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs =
        _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
    leanh::lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_Utils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_FileWorker_Utils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Language_Lean_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_Snapshots(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_AsyncList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_Utils(builtin);
}
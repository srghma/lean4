// Lean compiler output
// Module: Lean.Elab.Parallel
// Imports: Lean.Elab.Task
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_st_ref_get, lean_st_ref_set, lean_task_get_own,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_reverse___redArg, l_List_unzipTR___redArg};
use crate::r#gen::Init::System::IO::l_IO_waitAny_x27___redArg;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_saveState___redArg, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_saveState___redArg,
};
use crate::r#gen::Lean::Elab::Task::{
    initialize_Lean_Elab_Task, l_Lean_Core_CoreM_asTask___redArg,
    l_Lean_Core_CoreM_asTask_x27___redArg, l_Lean_Elab_Tactic_TacticM_asTask___redArg,
    l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg, l_Lean_Elab_Term_TermElabM_asTask___redArg,
    l_Lean_Elab_Term_TermElabM_asTask_x27___redArg, l_Lean_Meta_MetaM_asTask___redArg,
    l_Lean_Meta_MetaM_asTask_x27___redArg, runtime_initialize_Lean_Elab_Task,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_saveState___redArg;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_saveState___redArg;
pub static l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Core_CoreM_parFirst___redArg___closed__0_value: crate::leanh::LeanStringObject<
    26,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        65, 108, 108, 32, 112, 97, 114, 97, 108, 108, 101, 108, 32, 116, 97, 115, 107, 115, 32,
        102, 97, 105, 108, 101, 100, 0,
    ],
};
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_CoreM_parFirst___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(
    mut v_it_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_3593_) == 0 {
                    v___x_3595_ = crate::leanh::lean_box(2);
                    return v___x_3595_;
                } else {
                    v___x_3596_ = l_IO_waitAny_x27___redArg(v_it_3593_);
                    v_fst_3597_ = crate::leanh::lean_ctor_get(v___x_3596_, 0);
                    v_snd_3598_ = crate::leanh::lean_ctor_get(v___x_3596_, 1);
                    v_isSharedCheck_3605_ = (!crate::leanh::lean_is_exclusive(v___x_3596_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3596_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3598_);
                        crate::leanh::lean_inc(v_fst_3597_);
                        crate::leanh::lean_dec(v___x_3596_);
                        v___x_3600_ = crate::leanh::lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3600_, 1, v_fst_3597_);
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v_snd_3598_);
                    v___x_3603_ = v___x_3600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_snd_3598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_fst_3597_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed(
    mut v_it_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(v_it_3606_);
    return v_res_3608_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO(
    mut v_00_u03b1_3610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3611_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0;
    return v___f_3611_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(
    mut v_tasks_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_tasks_3612_);
    return v_tasks_3612_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(
    mut v_tasks_3613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3614_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(v_tasks_3613_);
    crate::leanh::lean_dec(v_tasks_3613_);
    return v_res_3614_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks(
    mut v_00_u03b1_3615_: *mut crate::leanh::LeanObject,
    mut v_tasks_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_tasks_3616_);
    return v_tasks_3616_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(
    mut v_00_u03b1_3617_: *mut crate::leanh::LeanObject,
    mut v_tasks_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3619_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks(v_00_u03b1_3617_, v_tasks_3618_);
    crate::leanh::lean_dec(v_tasks_3618_);
    return v_res_3619_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
    mut v_x_3620_: *mut crate::leanh::LeanObject,
    mut v_x_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3620_) == 0 {
                    v___x_3625_ = l_List_reverse___redArg(v_x_3621_);
                    v___x_3626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3625_);
                    return v___x_3626_;
                } else {
                    v_head_3627_ = crate::leanh::lean_ctor_get(v_x_3620_, 0);
                    v_tail_3628_ = crate::leanh::lean_ctor_get(v_x_3620_, 1);
                    v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v_x_3620_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3630_ = v_x_3620_;
                        v_isShared_3631_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3628_);
                        crate::leanh::lean_inc(v_head_3627_);
                        crate::leanh::lean_dec(v_x_3620_);
                        v___x_3630_ = crate::leanh::lean_box(0);
                        v_isShared_3631_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3632_ =
                    l_Lean_Core_CoreM_asTask___redArg(v_head_3627_, v___y_3622_, v___y_3623_);
                if crate::leanh::lean_obj_tag(v___x_3632_) == 0 {
                    v_a_3633_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                    crate::leanh::lean_inc(v_a_3633_);
                    crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
                    if v_isShared_3631_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3630_, 1, v_x_3621_);
                        crate::leanh::lean_ctor_set(v___x_3630_, 0, v_a_3633_);
                        v___x_3635_ = v___x_3630_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_x_3621_);
                        v___x_3635_ = v_reuseFailAlloc_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3630_);
                    crate::leanh::lean_dec(v_tail_3628_);
                    crate::leanh::lean_dec(v_x_3621_);
                    v_a_3638_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                    v_isSharedCheck_3645_ = (!crate::leanh::lean_is_exclusive(v___x_3632_)) as u8;
                    if v_isSharedCheck_3645_ == 0 {
                        v___x_3640_ = v___x_3632_;
                        v_isShared_3641_ = v_isSharedCheck_3645_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3638_);
                        crate::leanh::lean_dec(v___x_3632_);
                        v___x_3640_ = crate::leanh::lean_box(0);
                        v_isShared_3641_ = v_isSharedCheck_3645_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3620_ = v_tail_3628_;
                v_x_3621_ = v___x_3635_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3641_ == 0 {
                    v___x_3643_ = v___x_3640_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg___boxed(
    mut v_x_3647_: *mut crate::leanh::LeanObject,
    mut v_x_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
    mut v___y_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
        v_x_3647_,
        v_x_3648_,
        v___y_3649_,
        v___y_3650_,
    );
    crate::leanh::lean_dec(v___y_3650_);
    crate::leanh::lean_dec_ref(v___y_3649_);
    return v_res_3652_;
}
pub unsafe fn l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(
    mut v_as_3653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_3653_) == 0 {
                    v___x_3655_ = crate::leanh::lean_box(0);
                    return v___x_3655_;
                } else {
                    v_head_3656_ = crate::leanh::lean_ctor_get(v_as_3653_, 0);
                    crate::leanh::lean_inc(v_head_3656_);
                    v_tail_3657_ = crate::leanh::lean_ctor_get(v_as_3653_, 1);
                    crate::leanh::lean_inc(v_tail_3657_);
                    crate::leanh::lean_dec_ref_known(v_as_3653_, 2);
                    v___x_3658_ =
                        crate::leanh::lean_apply_1(v_head_3656_, crate::leanh::lean_box(0));
                    v_as_3653_ = v_tail_3657_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed(
    mut v_as_3660_: *mut crate::leanh::LeanObject,
    mut v___y_3661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3662_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_3660_);
    return v_res_3662_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel___redArg(
    mut v_jobs_3663_: *mut crate::leanh::LeanObject,
    mut v_a_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_a_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3691_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3667_ = crate::leanh::lean_box(0);
                v___x_3668_ =
                    l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
                        v_jobs_3663_,
                        v___x_3667_,
                        v_a_3664_,
                        v_a_3665_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3668_) == 0 {
                    v_a_3669_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3687_ = (!crate::leanh::lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3671_ = v___x_3668_;
                        v_isShared_3672_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3669_);
                        crate::leanh::lean_dec(v___x_3668_);
                        v___x_3671_ = crate::leanh::lean_box(0);
                        v_isShared_3672_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3688_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3690_ = v___x_3668_;
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3688_);
                        crate::leanh::lean_dec(v___x_3668_);
                        v___x_3690_ = crate::leanh::lean_box(0);
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3673_ = l_List_unzipTR___redArg(v_a_3669_);
                v_fst_3674_ = crate::leanh::lean_ctor_get(v___x_3673_, 0);
                v_snd_3675_ = crate::leanh::lean_ctor_get(v___x_3673_, 1);
                v_isSharedCheck_3686_ = (!crate::leanh::lean_is_exclusive(v___x_3673_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v___x_3677_ = v___x_3673_;
                    v_isShared_3678_ = v_isSharedCheck_3686_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3675_);
                    crate::leanh::lean_inc(v_fst_3674_);
                    crate::leanh::lean_dec(v___x_3673_);
                    v___x_3677_ = crate::leanh::lean_box(0);
                    v_isShared_3678_ = v_isSharedCheck_3686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3679_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3679_, 0, v_fst_3674_);
                if v_isShared_3678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3677_, 0, v___x_3679_);
                    v___x_3681_ = v___x_3677_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_snd_3675_);
                    v___x_3681_ = v_reuseFailAlloc_3685_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3671_, 0, v___x_3681_);
                    v___x_3683_ = v___x_3671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3683_;
            }
            5 => {
                if v_isShared_3691_ == 0 {
                    v___x_3693_ = v___x_3690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel___redArg___boxed(
    mut v_jobs_3696_: *mut crate::leanh::LeanObject,
    mut v_a_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3700_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_3696_, v_a_3697_, v_a_3698_);
    crate::leanh::lean_dec(v_a_3698_);
    crate::leanh::lean_dec_ref(v_a_3697_);
    return v_res_3700_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel(
    mut v_00_u03b1_3701_: *mut crate::leanh::LeanObject,
    mut v_jobs_3702_: *mut crate::leanh::LeanObject,
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_a_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_3702_, v_a_3703_, v_a_3704_);
    return v___x_3706_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel___boxed(
    mut v_00_u03b1_3707_: *mut crate::leanh::LeanObject,
    mut v_jobs_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ =
        l_Lean_Core_CoreM_parIterWithCancel(v_00_u03b1_3707_, v_jobs_3708_, v_a_3709_, v_a_3710_);
    crate::leanh::lean_dec(v_a_3710_);
    crate::leanh::lean_dec_ref(v_a_3709_);
    return v_res_3712_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(
    mut v_00_u03b1_3713_: *mut crate::leanh::LeanObject,
    mut v_x_3714_: *mut crate::leanh::LeanObject,
    mut v_x_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3719_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
        v_x_3714_,
        v_x_3715_,
        v___y_3716_,
        v___y_3717_,
    );
    return v___x_3719_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(
    mut v_00_u03b1_3720_: *mut crate::leanh::LeanObject,
    mut v_x_3721_: *mut crate::leanh::LeanObject,
    mut v_x_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3726_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(
        v_00_u03b1_3720_,
        v_x_3721_,
        v_x_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    crate::leanh::lean_dec(v___y_3724_);
    crate::leanh::lean_dec_ref(v___y_3723_);
    return v_res_3726_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter___redArg(
    mut v_jobs_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v_snd_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_a_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3744_: u8 = 0;
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3731_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(
                    v_jobs_3727_,
                    v_a_3728_,
                    v_a_3729_,
                );
                if crate::leanh::lean_obj_tag(v___x_3731_) == 0 {
                    v_a_3732_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3740_ = (!crate::leanh::lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3734_ = v___x_3731_;
                        v_isShared_3735_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3732_);
                        crate::leanh::lean_dec(v___x_3731_);
                        v___x_3734_ = crate::leanh::lean_box(0);
                        v_isShared_3735_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3741_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3748_ = (!crate::leanh::lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v___x_3743_ = v___x_3731_;
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3741_);
                        crate::leanh::lean_dec(v___x_3731_);
                        v___x_3743_ = crate::leanh::lean_box(0);
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3736_ = crate::leanh::lean_ctor_get(v_a_3732_, 1);
                crate::leanh::lean_inc(v_snd_3736_);
                crate::leanh::lean_dec(v_a_3732_);
                if v_isShared_3735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3734_, 0, v_snd_3736_);
                    v___x_3738_ = v___x_3734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_snd_3736_);
                    v___x_3738_ = v_reuseFailAlloc_3739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3738_;
            }
            3 => {
                if v_isShared_3744_ == 0 {
                    v___x_3746_ = v___x_3743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
                    v___x_3746_ = v_reuseFailAlloc_3747_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_parIter___redArg___boxed(
    mut v_jobs_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3753_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_3749_, v_a_3750_, v_a_3751_);
    crate::leanh::lean_dec(v_a_3751_);
    crate::leanh::lean_dec_ref(v_a_3750_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter(
    mut v_00_u03b1_3754_: *mut crate::leanh::LeanObject,
    mut v_jobs_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_3755_, v_a_3756_, v_a_3757_);
    return v___x_3759_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter___boxed(
    mut v_00_u03b1_3760_: *mut crate::leanh::LeanObject,
    mut v_jobs_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_Core_CoreM_parIter(v_00_u03b1_3760_, v_jobs_3761_, v_a_3762_, v_a_3763_);
    crate::leanh::lean_dec(v_a_3763_);
    crate::leanh::lean_dec_ref(v_a_3762_);
    return v_res_3765_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(
    mut v_jobs_3766_: *mut crate::leanh::LeanObject,
    mut v_a_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_a_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = crate::leanh::lean_box(0);
                v___x_3771_ =
                    l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
                        v_jobs_3766_,
                        v___x_3770_,
                        v_a_3767_,
                        v_a_3768_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3771_) == 0 {
                    v_a_3772_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                    v_isSharedCheck_3790_ = (!crate::leanh::lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3774_ = v___x_3771_;
                        v_isShared_3775_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3772_);
                        crate::leanh::lean_dec(v___x_3771_);
                        v___x_3774_ = crate::leanh::lean_box(0);
                        v_isShared_3775_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3791_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                    v_isSharedCheck_3798_ = (!crate::leanh::lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3798_ == 0 {
                        v___x_3793_ = v___x_3771_;
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3791_);
                        crate::leanh::lean_dec(v___x_3771_);
                        v___x_3793_ = crate::leanh::lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3776_ = l_List_unzipTR___redArg(v_a_3772_);
                v_fst_3777_ = crate::leanh::lean_ctor_get(v___x_3776_, 0);
                v_snd_3778_ = crate::leanh::lean_ctor_get(v___x_3776_, 1);
                v_isSharedCheck_3789_ = (!crate::leanh::lean_is_exclusive(v___x_3776_)) as u8;
                if v_isSharedCheck_3789_ == 0 {
                    v___x_3780_ = v___x_3776_;
                    v_isShared_3781_ = v_isSharedCheck_3789_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3778_);
                    crate::leanh::lean_inc(v_fst_3777_);
                    crate::leanh::lean_dec(v___x_3776_);
                    v___x_3780_ = crate::leanh::lean_box(0);
                    v_isShared_3781_ = v_isSharedCheck_3789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3782_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3782_, 0, v_fst_3777_);
                if v_isShared_3781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3780_, 0, v___x_3782_);
                    v___x_3784_ = v___x_3780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_snd_3778_);
                    v___x_3784_ = v_reuseFailAlloc_3788_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3774_, 0, v___x_3784_);
                    v___x_3786_ = v___x_3774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
                    v___x_3786_ = v_reuseFailAlloc_3787_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3786_;
            }
            5 => {
                if v_isShared_3794_ == 0 {
                    v___x_3796_ = v___x_3793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
                    v___x_3796_ = v_reuseFailAlloc_3797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg___boxed(
    mut v_jobs_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ =
        l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_3799_, v_a_3800_, v_a_3801_);
    crate::leanh::lean_dec(v_a_3801_);
    crate::leanh::lean_dec_ref(v_a_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel(
    mut v_00_u03b1_3804_: *mut crate::leanh::LeanObject,
    mut v_jobs_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ =
        l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_3805_, v_a_3806_, v_a_3807_);
    return v___x_3809_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(
    mut v_00_u03b1_3810_: *mut crate::leanh::LeanObject,
    mut v_jobs_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(
        v_00_u03b1_3810_,
        v_jobs_3811_,
        v_a_3812_,
        v_a_3813_,
    );
    crate::leanh::lean_dec(v_a_3813_);
    crate::leanh::lean_dec_ref(v_a_3812_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy___redArg(
    mut v_jobs_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v_snd_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_a_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3820_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(
                    v_jobs_3816_,
                    v_a_3817_,
                    v_a_3818_,
                );
                if crate::leanh::lean_obj_tag(v___x_3820_) == 0 {
                    v_a_3821_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3829_ = (!crate::leanh::lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3829_ == 0 {
                        v___x_3823_ = v___x_3820_;
                        v_isShared_3824_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3821_);
                        crate::leanh::lean_dec(v___x_3820_);
                        v___x_3823_ = crate::leanh::lean_box(0);
                        v_isShared_3824_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3830_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3837_ = (!crate::leanh::lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3837_ == 0 {
                        v___x_3832_ = v___x_3820_;
                        v_isShared_3833_ = v_isSharedCheck_3837_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3830_);
                        crate::leanh::lean_dec(v___x_3820_);
                        v___x_3832_ = crate::leanh::lean_box(0);
                        v_isShared_3833_ = v_isSharedCheck_3837_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3825_ = crate::leanh::lean_ctor_get(v_a_3821_, 1);
                crate::leanh::lean_inc(v_snd_3825_);
                crate::leanh::lean_dec(v_a_3821_);
                if v_isShared_3824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3823_, 0, v_snd_3825_);
                    v___x_3827_ = v___x_3823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_snd_3825_);
                    v___x_3827_ = v_reuseFailAlloc_3828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3827_;
            }
            3 => {
                if v_isShared_3833_ == 0 {
                    v___x_3835_ = v___x_3832_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
                    v___x_3835_ = v_reuseFailAlloc_3836_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy___redArg___boxed(
    mut v_jobs_3838_: *mut crate::leanh::LeanObject,
    mut v_a_3839_: *mut crate::leanh::LeanObject,
    mut v_a_3840_: *mut crate::leanh::LeanObject,
    mut v_a_3841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3842_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_3838_, v_a_3839_, v_a_3840_);
    crate::leanh::lean_dec(v_a_3840_);
    crate::leanh::lean_dec_ref(v_a_3839_);
    return v_res_3842_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy(
    mut v_00_u03b1_3843_: *mut crate::leanh::LeanObject,
    mut v_jobs_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_3844_, v_a_3845_, v_a_3846_);
    return v___x_3848_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy___boxed(
    mut v_00_u03b1_3849_: *mut crate::leanh::LeanObject,
    mut v_jobs_3850_: *mut crate::leanh::LeanObject,
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3854_ =
        l_Lean_Core_CoreM_parIterGreedy(v_00_u03b1_3849_, v_jobs_3850_, v_a_3851_, v_a_3852_);
    crate::leanh::lean_dec(v_a_3852_);
    crate::leanh::lean_dec_ref(v_a_3851_);
    return v_res_3854_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
    mut v_as_x27_3855_: *mut crate::leanh::LeanObject,
    mut v_b_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: u8 = 0;
    let mut v___x_1781__overap_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3855_) == 0 {
                    v___x_3860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3860_, 0, v_b_3856_);
                    return v___x_3860_;
                } else {
                    v_head_3861_ = crate::leanh::lean_ctor_get(v_as_x27_3855_, 0);
                    v_tail_3862_ = crate::leanh::lean_ctor_get(v_as_x27_3855_, 1);
                    crate::leanh::lean_inc(v_head_3861_);
                    v___x_1781__overap_3876_ = lean_task_get_own(v_head_3861_);
                    crate::leanh::lean_inc(v___y_3858_);
                    crate::leanh::lean_inc_ref(v___y_3857_);
                    v___x_3877_ = crate::leanh::lean_apply_3(
                        v___x_1781__overap_3876_,
                        v___y_3857_,
                        v___y_3858_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3877_) == 0 {
                        v_a_3878_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                        crate::leanh::lean_inc(v_a_3878_);
                        crate::leanh::lean_dec_ref_known(v___x_3877_, 1);
                        v___x_3879_ = l_Lean_Core_saveState___redArg(v___y_3858_);
                        if crate::leanh::lean_obj_tag(v___x_3879_) == 0 {
                            v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                            v_isSharedCheck_3888_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                            if v_isSharedCheck_3888_ == 0 {
                                v___x_3882_ = v___x_3879_;
                                v_isShared_3883_ = v_isSharedCheck_3888_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3880_);
                                crate::leanh::lean_dec(v___x_3879_);
                                v___x_3882_ = crate::leanh::lean_box(0);
                                v_isShared_3883_ = v_isSharedCheck_3888_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3878_);
                            v_a_3889_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                            crate::leanh::lean_inc(v_a_3889_);
                            crate::leanh::lean_dec_ref_known(v___x_3879_, 1);
                            v_a_3873_ = v_a_3889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                        crate::leanh::lean_inc(v_a_3890_);
                        crate::leanh::lean_dec_ref_known(v___x_3877_, 1);
                        v_a_3873_ = v_a_3890_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3865_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3865_, 0, v_a_3864_);
                crate::leanh::lean_ctor_set(v___x_3865_, 1, v_b_3856_);
                v_as_x27_3855_ = v_tail_3862_;
                v_b_3856_ = v___x_3865_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3869_ == 0 {
                    v___x_3870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3870_, 0, v___y_3868_);
                    v_a_3864_ = v___x_3870_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_3856_);
                    v___x_3871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3871_, 0, v___y_3868_);
                    return v___x_3871_;
                }
            }
            3 => {
                v___x_3874_ = l_Lean_Exception_isInterrupt(v_a_3873_);
                if v___x_3874_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3873_);
                    v___x_3875_ = l_Lean_Exception_isRuntime(v_a_3873_);
                    v___y_3868_ = v_a_3873_;
                    v___y_3869_ = v___x_3875_;
                    state = 2;
                    continue;
                } else {
                    v___y_3868_ = v_a_3873_;
                    v___y_3869_ = v___x_3874_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_3884_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3884_, 0, v_a_3878_);
                crate::leanh::lean_ctor_set(v___x_3884_, 1, v_a_3880_);
                if v_isShared_3883_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3882_, 1);
                    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
                    v___x_3886_ = v_reuseFailAlloc_3887_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_3864_ = v___x_3886_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(
    mut v_as_x27_3891_: *mut crate::leanh::LeanObject,
    mut v_b_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
        v_as_x27_3891_,
        v_b_3892_,
        v___y_3893_,
        v___y_3894_,
    );
    crate::leanh::lean_dec(v___y_3894_);
    crate::leanh::lean_dec_ref(v___y_3893_);
    crate::leanh::lean_dec(v_as_x27_3891_);
    return v_res_3896_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
    mut v_x_3897_: *mut crate::leanh::LeanObject,
    mut v_x_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3908_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3897_) == 0 {
                    v___x_3902_ = l_List_reverse___redArg(v_x_3898_);
                    v___x_3903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3903_, 0, v___x_3902_);
                    return v___x_3903_;
                } else {
                    v_head_3904_ = crate::leanh::lean_ctor_get(v_x_3897_, 0);
                    v_tail_3905_ = crate::leanh::lean_ctor_get(v_x_3897_, 1);
                    v_isSharedCheck_3923_ = (!crate::leanh::lean_is_exclusive(v_x_3897_)) as u8;
                    if v_isSharedCheck_3923_ == 0 {
                        v___x_3907_ = v_x_3897_;
                        v_isShared_3908_ = v_isSharedCheck_3923_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3905_);
                        crate::leanh::lean_inc(v_head_3904_);
                        crate::leanh::lean_dec(v_x_3897_);
                        v___x_3907_ = crate::leanh::lean_box(0);
                        v_isShared_3908_ = v_isSharedCheck_3923_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3909_ =
                    l_Lean_Core_CoreM_asTask_x27___redArg(v_head_3904_, v___y_3899_, v___y_3900_);
                if crate::leanh::lean_obj_tag(v___x_3909_) == 0 {
                    v_a_3910_ = crate::leanh::lean_ctor_get(v___x_3909_, 0);
                    crate::leanh::lean_inc(v_a_3910_);
                    crate::leanh::lean_dec_ref_known(v___x_3909_, 1);
                    if v_isShared_3908_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3907_, 1, v_x_3898_);
                        crate::leanh::lean_ctor_set(v___x_3907_, 0, v_a_3910_);
                        v___x_3912_ = v___x_3907_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3910_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_x_3898_);
                        v___x_3912_ = v_reuseFailAlloc_3914_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3907_);
                    crate::leanh::lean_dec(v_tail_3905_);
                    crate::leanh::lean_dec(v_x_3898_);
                    v_a_3915_ = crate::leanh::lean_ctor_get(v___x_3909_, 0);
                    v_isSharedCheck_3922_ = (!crate::leanh::lean_is_exclusive(v___x_3909_)) as u8;
                    if v_isSharedCheck_3922_ == 0 {
                        v___x_3917_ = v___x_3909_;
                        v_isShared_3918_ = v_isSharedCheck_3922_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3915_);
                        crate::leanh::lean_dec(v___x_3909_);
                        v___x_3917_ = crate::leanh::lean_box(0);
                        v_isShared_3918_ = v_isSharedCheck_3922_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3897_ = v_tail_3905_;
                v_x_3898_ = v___x_3912_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3918_ == 0 {
                    v___x_3920_ = v___x_3917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
                    v___x_3920_ = v_reuseFailAlloc_3921_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(
    mut v_x_3924_: *mut crate::leanh::LeanObject,
    mut v_x_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
        v_x_3924_,
        v_x_3925_,
        v___y_3926_,
        v___y_3927_,
    );
    crate::leanh::lean_dec(v___y_3927_);
    crate::leanh::lean_dec_ref(v___y_3926_);
    return v_res_3929_;
}
pub unsafe fn l_Lean_Core_CoreM_par___redArg(
    mut v_jobs_3930_: *mut crate::leanh::LeanObject,
    mut v_a_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v_a_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3952_: u8 = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3934_ = lean_st_ref_get(v_a_3932_);
                v___x_3935_ = crate::leanh::lean_box(0);
                v___x_3936_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
                    v_jobs_3930_,
                    v___x_3935_,
                    v_a_3931_,
                    v_a_3932_,
                );
                if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                    v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                    crate::leanh::lean_inc(v_a_3937_);
                    crate::leanh::lean_dec_ref_known(v___x_3936_, 1);
                    v___x_3938_ =
                        l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
                            v_a_3937_,
                            v___x_3935_,
                            v_a_3931_,
                            v_a_3932_,
                        );
                    crate::leanh::lean_dec(v_a_3937_);
                    if crate::leanh::lean_obj_tag(v___x_3938_) == 0 {
                        v_a_3939_ = crate::leanh::lean_ctor_get(v___x_3938_, 0);
                        v_isSharedCheck_3948_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3938_)) as u8;
                        if v_isSharedCheck_3948_ == 0 {
                            v___x_3941_ = v___x_3938_;
                            v_isShared_3942_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3939_);
                            crate::leanh::lean_dec(v___x_3938_);
                            v___x_3941_ = crate::leanh::lean_box(0);
                            v_isShared_3942_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3934_);
                        return v___x_3938_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3934_);
                    v_a_3949_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                    v_isSharedCheck_3956_ = (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                    if v_isSharedCheck_3956_ == 0 {
                        v___x_3951_ = v___x_3936_;
                        v_isShared_3952_ = v_isSharedCheck_3956_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3949_);
                        crate::leanh::lean_dec(v___x_3936_);
                        v___x_3951_ = crate::leanh::lean_box(0);
                        v_isShared_3952_ = v_isSharedCheck_3956_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3943_ = lean_st_ref_set(v_a_3932_, v___x_3934_);
                v___x_3944_ = l_List_reverse___redArg(v_a_3939_);
                if v_isShared_3942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3941_, 0, v___x_3944_);
                    v___x_3946_ = v___x_3941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
                    v___x_3946_ = v_reuseFailAlloc_3947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3946_;
            }
            3 => {
                if v_isShared_3952_ == 0 {
                    v___x_3954_ = v___x_3951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
                    v___x_3954_ = v_reuseFailAlloc_3955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_par___redArg___boxed(
    mut v_jobs_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_Core_CoreM_par___redArg(v_jobs_3957_, v_a_3958_, v_a_3959_);
    crate::leanh::lean_dec(v_a_3959_);
    crate::leanh::lean_dec_ref(v_a_3958_);
    return v_res_3961_;
}
pub unsafe fn l_Lean_Core_CoreM_par(
    mut v_00_u03b1_3962_: *mut crate::leanh::LeanObject,
    mut v_jobs_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Lean_Core_CoreM_par___redArg(v_jobs_3963_, v_a_3964_, v_a_3965_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Core_CoreM_par___boxed(
    mut v_00_u03b1_3968_: *mut crate::leanh::LeanObject,
    mut v_jobs_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lean_Core_CoreM_par(v_00_u03b1_3968_, v_jobs_3969_, v_a_3970_, v_a_3971_);
    crate::leanh::lean_dec(v_a_3971_);
    crate::leanh::lean_dec_ref(v_a_3970_);
    return v_res_3973_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(
    mut v_00_u03b1_3974_: *mut crate::leanh::LeanObject,
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
        v_x_3975_,
        v_x_3976_,
        v___y_3977_,
        v___y_3978_,
    );
    return v___x_3980_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(
    mut v_00_u03b1_3981_: *mut crate::leanh::LeanObject,
    mut v_x_3982_: *mut crate::leanh::LeanObject,
    mut v_x_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(
        v_00_u03b1_3981_,
        v_x_3982_,
        v_x_3983_,
        v___y_3984_,
        v___y_3985_,
    );
    crate::leanh::lean_dec(v___y_3985_);
    crate::leanh::lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(
    mut v_00_u03b1_3988_: *mut crate::leanh::LeanObject,
    mut v_as_3989_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3990_: *mut crate::leanh::LeanObject,
    mut v_b_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
        v_as_x27_3990_,
        v_b_3991_,
        v___y_3993_,
        v___y_3994_,
    );
    return v___x_3996_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(
    mut v_00_u03b1_3997_: *mut crate::leanh::LeanObject,
    mut v_as_3998_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3999_: *mut crate::leanh::LeanObject,
    mut v_b_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(
        v_00_u03b1_3997_,
        v_as_3998_,
        v_as_x27_3999_,
        v_b_4000_,
        v_a_4001_,
        v___y_4002_,
        v___y_4003_,
    );
    crate::leanh::lean_dec(v___y_4003_);
    crate::leanh::lean_dec_ref(v___y_4002_);
    crate::leanh::lean_dec(v_as_x27_3999_);
    crate::leanh::lean_dec(v_as_3998_);
    return v_res_4005_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
    mut v_as_x27_4006_: *mut crate::leanh::LeanObject,
    mut v_b_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591__overap_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___y_4025_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    let mut v___x_4033_: u8 = 0;
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4006_) == 0 {
                    v___x_4011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4011_, 0, v_b_4007_);
                    return v___x_4011_;
                } else {
                    v_head_4012_ = crate::leanh::lean_ctor_get(v_as_x27_4006_, 0);
                    v_tail_4013_ = crate::leanh::lean_ctor_get(v_as_x27_4006_, 1);
                    crate::leanh::lean_inc(v_head_4012_);
                    v___x_1591__overap_4014_ = lean_task_get_own(v_head_4012_);
                    crate::leanh::lean_inc(v___y_4009_);
                    crate::leanh::lean_inc_ref(v___y_4008_);
                    v___x_4015_ = crate::leanh::lean_apply_3(
                        v___x_1591__overap_4014_,
                        v___y_4008_,
                        v___y_4009_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4015_) == 0 {
                        v_a_4016_ = crate::leanh::lean_ctor_get(v___x_4015_, 0);
                        crate::leanh::lean_inc(v_a_4016_);
                        crate::leanh::lean_dec_ref_known(v___x_4015_, 1);
                        v___x_4017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4017_, 0, v_a_4016_);
                        v___x_4018_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                        crate::leanh::lean_ctor_set(v___x_4018_, 1, v_b_4007_);
                        v_as_x27_4006_ = v_tail_4013_;
                        v_b_4007_ = v___x_4018_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4020_ = crate::leanh::lean_ctor_get(v___x_4015_, 0);
                        v_isSharedCheck_4034_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4015_)) as u8;
                        if v_isSharedCheck_4034_ == 0 {
                            v___x_4022_ = v___x_4015_;
                            v_isShared_4023_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4020_);
                            crate::leanh::lean_dec(v___x_4015_);
                            v___x_4022_ = crate::leanh::lean_box(0);
                            v_isShared_4023_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4032_ = l_Lean_Exception_isInterrupt(v_a_4020_);
                if v___x_4032_ == 0 {
                    crate::leanh::lean_inc(v_a_4020_);
                    v___x_4033_ = l_Lean_Exception_isRuntime(v_a_4020_);
                    v___y_4025_ = v___x_4033_;
                    state = 2;
                    continue;
                } else {
                    v___y_4025_ = v___x_4032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_4025_ == 0 {
                    crate::leanh::lean_del_object(v___x_4022_);
                    v___x_4026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4026_, 0, v_a_4020_);
                    v___x_4027_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4027_, 0, v___x_4026_);
                    crate::leanh::lean_ctor_set(v___x_4027_, 1, v_b_4007_);
                    v_as_x27_4006_ = v_tail_4013_;
                    v_b_4007_ = v___x_4027_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_4007_);
                    if v_isShared_4023_ == 0 {
                        v___x_4030_ = v___x_4022_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4020_);
                        v___x_4030_ = v_reuseFailAlloc_4031_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(
    mut v_as_x27_4035_: *mut crate::leanh::LeanObject,
    mut v_b_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4040_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
        v_as_x27_4035_,
        v_b_4036_,
        v___y_4037_,
        v___y_4038_,
    );
    crate::leanh::lean_dec(v___y_4038_);
    crate::leanh::lean_dec_ref(v___y_4037_);
    crate::leanh::lean_dec(v_as_x27_4035_);
    return v_res_4040_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27___redArg(
    mut v_jobs_4041_: *mut crate::leanh::LeanObject,
    mut v_a_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4059_: u8 = 0;
    let mut v_a_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4045_ = lean_st_ref_get(v_a_4043_);
                v___x_4046_ = crate::leanh::lean_box(0);
                v___x_4047_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
                    v_jobs_4041_,
                    v___x_4046_,
                    v_a_4042_,
                    v_a_4043_,
                );
                if crate::leanh::lean_obj_tag(v___x_4047_) == 0 {
                    v_a_4048_ = crate::leanh::lean_ctor_get(v___x_4047_, 0);
                    crate::leanh::lean_inc(v_a_4048_);
                    crate::leanh::lean_dec_ref_known(v___x_4047_, 1);
                    v___x_4049_ =
                        l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
                            v_a_4048_,
                            v___x_4046_,
                            v_a_4042_,
                            v_a_4043_,
                        );
                    crate::leanh::lean_dec(v_a_4048_);
                    if crate::leanh::lean_obj_tag(v___x_4049_) == 0 {
                        v_a_4050_ = crate::leanh::lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4059_ == 0 {
                            v___x_4052_ = v___x_4049_;
                            v_isShared_4053_ = v_isSharedCheck_4059_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4050_);
                            crate::leanh::lean_dec(v___x_4049_);
                            v___x_4052_ = crate::leanh::lean_box(0);
                            v_isShared_4053_ = v_isSharedCheck_4059_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4045_);
                        return v___x_4049_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4045_);
                    v_a_4060_ = crate::leanh::lean_ctor_get(v___x_4047_, 0);
                    v_isSharedCheck_4067_ = (!crate::leanh::lean_is_exclusive(v___x_4047_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4062_ = v___x_4047_;
                        v_isShared_4063_ = v_isSharedCheck_4067_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4060_);
                        crate::leanh::lean_dec(v___x_4047_);
                        v___x_4062_ = crate::leanh::lean_box(0);
                        v_isShared_4063_ = v_isSharedCheck_4067_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4054_ = lean_st_ref_set(v_a_4043_, v___x_4045_);
                v___x_4055_ = l_List_reverse___redArg(v_a_4050_);
                if v_isShared_4053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4052_, 0, v___x_4055_);
                    v___x_4057_ = v___x_4052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4055_);
                    v___x_4057_ = v_reuseFailAlloc_4058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4057_;
            }
            3 => {
                if v_isShared_4063_ == 0 {
                    v___x_4065_ = v___x_4062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_par_x27___redArg___boxed(
    mut v_jobs_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
    mut v_a_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4072_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_4068_, v_a_4069_, v_a_4070_);
    crate::leanh::lean_dec(v_a_4070_);
    crate::leanh::lean_dec_ref(v_a_4069_);
    return v_res_4072_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27(
    mut v_00_u03b1_4073_: *mut crate::leanh::LeanObject,
    mut v_jobs_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4078_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_4074_, v_a_4075_, v_a_4076_);
    return v___x_4078_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27___boxed(
    mut v_00_u03b1_4079_: *mut crate::leanh::LeanObject,
    mut v_jobs_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_4079_, v_jobs_4080_, v_a_4081_, v_a_4082_);
    crate::leanh::lean_dec(v_a_4082_);
    crate::leanh::lean_dec_ref(v_a_4081_);
    return v_res_4084_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(
    mut v_00_u03b1_4085_: *mut crate::leanh::LeanObject,
    mut v_as_4086_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4087_: *mut crate::leanh::LeanObject,
    mut v_b_4088_: *mut crate::leanh::LeanObject,
    mut v_a_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4093_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
        v_as_x27_4087_,
        v_b_4088_,
        v___y_4090_,
        v___y_4091_,
    );
    return v___x_4093_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(
    mut v_00_u03b1_4094_: *mut crate::leanh::LeanObject,
    mut v_as_4095_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4096_: *mut crate::leanh::LeanObject,
    mut v_b_4097_: *mut crate::leanh::LeanObject,
    mut v_a_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(
        v_00_u03b1_4094_,
        v_as_4095_,
        v_as_x27_4096_,
        v_b_4097_,
        v_a_4098_,
        v___y_4099_,
        v___y_4100_,
    );
    crate::leanh::lean_dec(v___y_4100_);
    crate::leanh::lean_dec_ref(v___y_4099_);
    crate::leanh::lean_dec(v_as_x27_4096_);
    crate::leanh::lean_dec(v_as_4095_);
    return v_res_4102_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(
    mut v_a_4103_: *mut crate::leanh::LeanObject,
    mut v___x_4104_: *mut crate::leanh::LeanObject,
    mut v_____r_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4109_, 0, v_a_4103_);
    v___x_4110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4110_, 0, v___x_4109_);
    crate::leanh::lean_ctor_set(v___x_4110_, 1, v___x_4104_);
    v___x_4111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
    v___x_4112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
    return v___x_4112_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v___x_4114_: *mut crate::leanh::LeanObject,
    mut v_____r_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(
            v_a_4113_,
            v___x_4114_,
            v_____r_4115_,
            v___y_4116_,
            v___y_4117_,
        );
    crate::leanh::lean_dec(v___y_4117_);
    crate::leanh::lean_dec_ref(v___y_4116_);
    return v_res_4119_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(
    mut v_cancel_4123_: u8,
    mut v_fst_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
    mut v_b_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v_a_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v_a_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: u8 = 0;
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4125_) == 0 {
                    crate::leanh::lean_dec_ref(v_fst_4124_);
                    v___x_4130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4130_, 0, v_b_4126_);
                    return v___x_4130_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4126_);
                    v___x_4131_ = l_IO_waitAny_x27___redArg(v_a_4125_);
                    v_fst_4132_ = crate::leanh::lean_ctor_get(v___x_4131_, 0);
                    crate::leanh::lean_inc(v_fst_4132_);
                    v_snd_4133_ = crate::leanh::lean_ctor_get(v___x_4131_, 1);
                    crate::leanh::lean_inc(v_snd_4133_);
                    crate::leanh::lean_dec_ref(v___x_4131_);
                    v___x_4155_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_4128_);
                    crate::leanh::lean_inc_ref(v___y_4127_);
                    v___x_4156_ = crate::leanh::lean_apply_3(
                        v_fst_4132_,
                        v___y_4127_,
                        v___y_4128_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4156_) == 0 {
                        if v_cancel_4123_ == 0 {
                            v_a_4157_ = crate::leanh::lean_ctor_get(v___x_4156_, 0);
                            crate::leanh::lean_inc(v_a_4157_);
                            crate::leanh::lean_dec_ref_known(v___x_4156_, 1);
                            v___x_4158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_4157_, v___x_4155_, v___x_4155_, v___y_4127_, v___y_4128_);
                            v___y_4135_ = v___x_4158_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4159_ = crate::leanh::lean_ctor_get(v___x_4156_, 0);
                            crate::leanh::lean_inc(v_a_4159_);
                            crate::leanh::lean_dec_ref_known(v___x_4156_, 1);
                            crate::leanh::lean_inc_ref(v_fst_4124_);
                            v___x_4160_ =
                                crate::leanh::lean_apply_1(v_fst_4124_, crate::leanh::lean_box(0));
                            v___x_4161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_4159_, v___x_4155_, v___x_4160_, v___y_4127_, v___y_4128_);
                            v___y_4135_ = v___x_4161_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4162_ = crate::leanh::lean_ctor_get(v___x_4156_, 0);
                        v_isSharedCheck_4175_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4156_)) as u8;
                        if v_isSharedCheck_4175_ == 0 {
                            v___x_4164_ = v___x_4156_;
                            v_isShared_4165_ = v_isSharedCheck_4175_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4162_);
                            crate::leanh::lean_dec(v___x_4156_);
                            v___x_4164_ = crate::leanh::lean_box(0);
                            v_isShared_4165_ = v_isSharedCheck_4175_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4135_) == 0 {
                    v_a_4136_ = crate::leanh::lean_ctor_get(v___y_4135_, 0);
                    v_isSharedCheck_4146_ = (!crate::leanh::lean_is_exclusive(v___y_4135_)) as u8;
                    if v_isSharedCheck_4146_ == 0 {
                        v___x_4138_ = v___y_4135_;
                        v_isShared_4139_ = v_isSharedCheck_4146_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4136_);
                        crate::leanh::lean_dec(v___y_4135_);
                        v___x_4138_ = crate::leanh::lean_box(0);
                        v_isShared_4139_ = v_isSharedCheck_4146_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4133_);
                    crate::leanh::lean_dec_ref(v_fst_4124_);
                    v_a_4147_ = crate::leanh::lean_ctor_get(v___y_4135_, 0);
                    v_isSharedCheck_4154_ = (!crate::leanh::lean_is_exclusive(v___y_4135_)) as u8;
                    if v_isSharedCheck_4154_ == 0 {
                        v___x_4149_ = v___y_4135_;
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4147_);
                        crate::leanh::lean_dec(v___y_4135_);
                        v___x_4149_ = crate::leanh::lean_box(0);
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4136_) == 0 {
                    crate::leanh::lean_dec(v_snd_4133_);
                    crate::leanh::lean_dec_ref(v_fst_4124_);
                    v_a_4140_ = crate::leanh::lean_ctor_get(v_a_4136_, 0);
                    crate::leanh::lean_inc(v_a_4140_);
                    crate::leanh::lean_dec_ref_known(v_a_4136_, 1);
                    if v_isShared_4139_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4138_, 0, v_a_4140_);
                        v___x_4142_ = v___x_4138_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4140_);
                        v___x_4142_ = v_reuseFailAlloc_4143_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4138_);
                    v_a_4144_ = crate::leanh::lean_ctor_get(v_a_4136_, 0);
                    crate::leanh::lean_inc(v_a_4144_);
                    crate::leanh::lean_dec_ref_known(v_a_4136_, 1);
                    v_a_4125_ = v_snd_4133_;
                    v_b_4126_ = v_a_4144_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4142_;
            }
            4 => {
                if v_isShared_4150_ == 0 {
                    v___x_4152_ = v___x_4149_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
                    v___x_4152_ = v_reuseFailAlloc_4153_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4152_;
            }
            6 => {
                v___x_4166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                v___x_4173_ = l_Lean_Exception_isInterrupt(v_a_4162_);
                if v___x_4173_ == 0 {
                    crate::leanh::lean_inc(v_a_4162_);
                    v___x_4174_ = l_Lean_Exception_isRuntime(v_a_4162_);
                    v___y_4168_ = v___x_4174_;
                    state = 7;
                    continue;
                } else {
                    v___y_4168_ = v___x_4173_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_4168_ == 0 {
                    crate::leanh::lean_del_object(v___x_4164_);
                    crate::leanh::lean_dec(v_a_4162_);
                    v_a_4125_ = v_snd_4133_;
                    v_b_4126_ = v___x_4166_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4133_);
                    crate::leanh::lean_dec_ref(v_fst_4124_);
                    if v_isShared_4165_ == 0 {
                        v___x_4171_ = v___x_4164_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4162_);
                        v___x_4171_ = v_reuseFailAlloc_4172_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_4171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___boxed(
    mut v_cancel_4176_: *mut crate::leanh::LeanObject,
    mut v_fst_4177_: *mut crate::leanh::LeanObject,
    mut v_a_4178_: *mut crate::leanh::LeanObject,
    mut v_b_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_4183_: u8 = 0;
    let mut v_res_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4183_ = (crate::leanh::lean_unbox(v_cancel_4176_) as u8);
    v_res_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(
        v_cancel_boxed_4183_,
        v_fst_4177_,
        v_a_4178_,
        v_b_4179_,
        v___y_4180_,
        v___y_4181_,
    );
    crate::leanh::lean_dec(v___y_4181_);
    crate::leanh::lean_dec_ref(v___y_4180_);
    return v_res_4184_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4185_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0);
    v___x_4187_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4187_, 0, v___x_4186_);
    return v___x_4187_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
    v___x_4189_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4190_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4190_, 0, v___x_4189_);
    crate::leanh::lean_ctor_set(v___x_4190_, 1, v___x_4189_);
    crate::leanh::lean_ctor_set(v___x_4190_, 2, v___x_4189_);
    crate::leanh::lean_ctor_set(v___x_4190_, 3, v___x_4189_);
    crate::leanh::lean_ctor_set(v___x_4190_, 4, v___x_4188_);
    crate::leanh::lean_ctor_set(v___x_4190_, 5, v___x_4188_);
    crate::leanh::lean_ctor_set(v___x_4190_, 6, v___x_4188_);
    crate::leanh::lean_ctor_set(v___x_4190_, 7, v___x_4188_);
    crate::leanh::lean_ctor_set(v___x_4190_, 8, v___x_4188_);
    crate::leanh::lean_ctor_set(v___x_4190_, 9, v___x_4188_);
    return v___x_4190_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4191_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4192_ = lean_mk_empty_array_with_capacity(v___x_4191_);
    v___x_4193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
    return v___x_4193_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4194_ = 5usize;
    v___x_4195_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4196_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4197_ = lean_mk_empty_array_with_capacity(v___x_4196_);
    v___x_4198_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
    v___x_4199_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4198_);
    crate::leanh::lean_ctor_set(v___x_4199_, 1, v___x_4197_);
    crate::leanh::lean_ctor_set(v___x_4199_, 2, v___x_4195_);
    crate::leanh::lean_ctor_set(v___x_4199_, 3, v___x_4195_);
    crate::leanh::lean_ctor_set_usize(v___x_4199_, 4, v___x_4194_);
    return v___x_4199_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = crate::leanh::lean_box(1);
    v___x_4201_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
    v___x_4202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
    v___x_4203_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
    crate::leanh::lean_ctor_set(v___x_4203_, 1, v___x_4201_);
    crate::leanh::lean_ctor_set(v___x_4203_, 2, v___x_4200_);
    return v___x_4203_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(
    mut v_msgData_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = lean_st_ref_get(v___y_4206_);
    v_env_4209_ = crate::leanh::lean_ctor_get(v___x_4208_, 0);
    crate::leanh::lean_inc_ref(v_env_4209_);
    crate::leanh::lean_dec(v___x_4208_);
    v_options_4210_ = crate::leanh::lean_ctor_get(v___y_4205_, 2);
    v___x_4211_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
    v___x_4212_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_4210_);
    v___x_4213_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4213_, 0, v_env_4209_);
    crate::leanh::lean_ctor_set(v___x_4213_, 1, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4213_, 2, v___x_4212_);
    crate::leanh::lean_ctor_set(v___x_4213_, 3, v_options_4210_);
    v___x_4214_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
    crate::leanh::lean_ctor_set(v___x_4214_, 1, v_msgData_4204_);
    v___x_4215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4214_);
    return v___x_4215_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_4216_: *mut crate::leanh::LeanObject,
    mut v___y_4217_: *mut crate::leanh::LeanObject,
    mut v___y_4218_: *mut crate::leanh::LeanObject,
    mut v___y_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4220_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_4216_, v___y_4217_, v___y_4218_);
    crate::leanh::lean_dec(v___y_4218_);
    crate::leanh::lean_dec_ref(v___y_4217_);
    return v_res_4220_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
    mut v_msg_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4225_ = crate::leanh::lean_ctor_get(v___y_4222_, 5);
                v___x_4226_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_4221_, v___y_4222_, v___y_4223_);
                v_a_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                v_isSharedCheck_4235_ = (!crate::leanh::lean_is_exclusive(v___x_4226_)) as u8;
                if v_isSharedCheck_4235_ == 0 {
                    v___x_4229_ = v___x_4226_;
                    v_isShared_4230_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4227_);
                    crate::leanh::lean_dec(v___x_4226_);
                    v___x_4229_ = crate::leanh::lean_box(0);
                    v_isShared_4230_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4225_);
                v___x_4231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4231_, 0, v_ref_4225_);
                crate::leanh::lean_ctor_set(v___x_4231_, 1, v_a_4227_);
                if v_isShared_4230_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4229_, 1);
                    crate::leanh::lean_ctor_set(v___x_4229_, 0, v___x_4231_);
                    v___x_4233_ = v___x_4229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
                    v___x_4233_ = v_reuseFailAlloc_4234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(
    mut v_msg_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
        v_msg_4236_,
        v___y_4237_,
        v___y_4238_,
    );
    crate::leanh::lean_dec(v___y_4238_);
    crate::leanh::lean_dec_ref(v___y_4237_);
    return v_res_4240_;
}
pub unsafe fn _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Lean_Core_CoreM_parFirst___redArg___closed__0;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst___redArg(
    mut v_jobs_4244_: *mut crate::leanh::LeanObject,
    mut v_cancel_4245_: u8,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v_fst_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_a_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4274_: u8 = 0;
    let mut v_a_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4249_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(
                    v_jobs_4244_,
                    v_a_4246_,
                    v_a_4247_,
                );
                if crate::leanh::lean_obj_tag(v___x_4249_) == 0 {
                    v_a_4250_ = crate::leanh::lean_ctor_get(v___x_4249_, 0);
                    crate::leanh::lean_inc(v_a_4250_);
                    crate::leanh::lean_dec_ref_known(v___x_4249_, 1);
                    v_fst_4251_ = crate::leanh::lean_ctor_get(v_a_4250_, 0);
                    crate::leanh::lean_inc(v_fst_4251_);
                    v_snd_4252_ = crate::leanh::lean_ctor_get(v_a_4250_, 1);
                    crate::leanh::lean_inc(v_snd_4252_);
                    crate::leanh::lean_dec(v_a_4250_);
                    v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_4254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_4245_, v_fst_4251_, v_snd_4252_, v___x_4253_, v_a_4246_, v_a_4247_);
                    if crate::leanh::lean_obj_tag(v___x_4254_) == 0 {
                        v_a_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                        v_isSharedCheck_4266_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4254_)) as u8;
                        if v_isSharedCheck_4266_ == 0 {
                            v___x_4257_ = v___x_4254_;
                            v_isShared_4258_ = v_isSharedCheck_4266_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4255_);
                            crate::leanh::lean_dec(v___x_4254_);
                            v___x_4257_ = crate::leanh::lean_box(0);
                            v_isShared_4258_ = v_isSharedCheck_4266_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4267_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                        v_isSharedCheck_4274_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4254_)) as u8;
                        if v_isSharedCheck_4274_ == 0 {
                            v___x_4269_ = v___x_4254_;
                            v_isShared_4270_ = v_isSharedCheck_4274_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4267_);
                            crate::leanh::lean_dec(v___x_4254_);
                            v___x_4269_ = crate::leanh::lean_box(0);
                            v_isShared_4270_ = v_isSharedCheck_4274_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4275_ = crate::leanh::lean_ctor_get(v___x_4249_, 0);
                    v_isSharedCheck_4282_ = (!crate::leanh::lean_is_exclusive(v___x_4249_)) as u8;
                    if v_isSharedCheck_4282_ == 0 {
                        v___x_4277_ = v___x_4249_;
                        v_isShared_4278_ = v_isSharedCheck_4282_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4275_);
                        crate::leanh::lean_dec(v___x_4249_);
                        v___x_4277_ = crate::leanh::lean_box(0);
                        v_isShared_4278_ = v_isSharedCheck_4282_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4259_ = crate::leanh::lean_ctor_get(v_a_4255_, 0);
                crate::leanh::lean_inc(v_fst_4259_);
                crate::leanh::lean_dec(v_a_4255_);
                if crate::leanh::lean_obj_tag(v_fst_4259_) == 0 {
                    crate::leanh::lean_del_object(v___x_4257_);
                    v___x_4260_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_4261_ =
                        l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
                            v___x_4260_,
                            v_a_4246_,
                            v_a_4247_,
                        );
                    return v___x_4261_;
                } else {
                    v_val_4262_ = crate::leanh::lean_ctor_get(v_fst_4259_, 0);
                    crate::leanh::lean_inc(v_val_4262_);
                    crate::leanh::lean_dec_ref_known(v_fst_4259_, 1);
                    if v_isShared_4258_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4257_, 0, v_val_4262_);
                        v___x_4264_ = v___x_4257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_val_4262_);
                        v___x_4264_ = v_reuseFailAlloc_4265_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4264_;
            }
            3 => {
                if v_isShared_4270_ == 0 {
                    v___x_4272_ = v___x_4269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
                    v___x_4272_ = v_reuseFailAlloc_4273_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4272_;
            }
            5 => {
                if v_isShared_4278_ == 0 {
                    v___x_4280_ = v___x_4277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
                    v___x_4280_ = v_reuseFailAlloc_4281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_CoreM_parFirst___redArg___boxed(
    mut v_jobs_4283_: *mut crate::leanh::LeanObject,
    mut v_cancel_4284_: *mut crate::leanh::LeanObject,
    mut v_a_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_4288_: u8 = 0;
    let mut v_res_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4288_ = (crate::leanh::lean_unbox(v_cancel_4284_) as u8);
    v_res_4289_ = l_Lean_Core_CoreM_parFirst___redArg(
        v_jobs_4283_,
        v_cancel_boxed_4288_,
        v_a_4285_,
        v_a_4286_,
    );
    crate::leanh::lean_dec(v_a_4286_);
    crate::leanh::lean_dec_ref(v_a_4285_);
    return v_res_4289_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst(
    mut v_00_u03b1_4290_: *mut crate::leanh::LeanObject,
    mut v_jobs_4291_: *mut crate::leanh::LeanObject,
    mut v_cancel_4292_: u8,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ =
        l_Lean_Core_CoreM_parFirst___redArg(v_jobs_4291_, v_cancel_4292_, v_a_4293_, v_a_4294_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst___boxed(
    mut v_00_u03b1_4297_: *mut crate::leanh::LeanObject,
    mut v_jobs_4298_: *mut crate::leanh::LeanObject,
    mut v_cancel_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_4303_: u8 = 0;
    let mut v_res_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4303_ = (crate::leanh::lean_unbox(v_cancel_4299_) as u8);
    v_res_4304_ = l_Lean_Core_CoreM_parFirst(
        v_00_u03b1_4297_,
        v_jobs_4298_,
        v_cancel_boxed_4303_,
        v_a_4300_,
        v_a_4301_,
    );
    crate::leanh::lean_dec(v_a_4301_);
    crate::leanh::lean_dec_ref(v_a_4300_);
    return v_res_4304_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(
    mut v_00_u03b1_4305_: *mut crate::leanh::LeanObject,
    mut v_cancel_4306_: u8,
    mut v_fst_4307_: *mut crate::leanh::LeanObject,
    mut v_inst_4308_: *mut crate::leanh::LeanObject,
    mut v_R_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_b_4311_: *mut crate::leanh::LeanObject,
    mut v_c_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4316_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(
        v_cancel_4306_,
        v_fst_4307_,
        v_a_4310_,
        v_b_4311_,
        v___y_4313_,
        v___y_4314_,
    );
    return v___x_4316_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(
    mut v_00_u03b1_4317_: *mut crate::leanh::LeanObject,
    mut v_cancel_4318_: *mut crate::leanh::LeanObject,
    mut v_fst_4319_: *mut crate::leanh::LeanObject,
    mut v_inst_4320_: *mut crate::leanh::LeanObject,
    mut v_R_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
    mut v_b_4323_: *mut crate::leanh::LeanObject,
    mut v_c_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_4328_: u8 = 0;
    let mut v_res_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4328_ = (crate::leanh::lean_unbox(v_cancel_4318_) as u8);
    v_res_4329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(
        v_00_u03b1_4317_,
        v_cancel_boxed_4328_,
        v_fst_4319_,
        v_inst_4320_,
        v_R_4321_,
        v_a_4322_,
        v_b_4323_,
        v_c_4324_,
        v___y_4325_,
        v___y_4326_,
    );
    crate::leanh::lean_dec(v___y_4326_);
    crate::leanh::lean_dec_ref(v___y_4325_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(
    mut v_00_u03b1_4330_: *mut crate::leanh::LeanObject,
    mut v_msg_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
        v_msg_4331_,
        v___y_4332_,
        v___y_4333_,
    );
    return v___x_4335_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(
    mut v_00_u03b1_4336_: *mut crate::leanh::LeanObject,
    mut v_msg_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(
        v_00_u03b1_4336_,
        v_msg_4337_,
        v___y_4338_,
        v___y_4339_,
    );
    crate::leanh::lean_dec(v___y_4339_);
    crate::leanh::lean_dec_ref(v___y_4338_);
    return v_res_4341_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
    mut v_x_4342_: *mut crate::leanh::LeanObject,
    mut v_x_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4342_) == 0 {
                    v___x_4349_ = l_List_reverse___redArg(v_x_4343_);
                    v___x_4350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4350_, 0, v___x_4349_);
                    return v___x_4350_;
                } else {
                    v_head_4351_ = crate::leanh::lean_ctor_get(v_x_4342_, 0);
                    v_tail_4352_ = crate::leanh::lean_ctor_get(v_x_4342_, 1);
                    v_isSharedCheck_4370_ = (!crate::leanh::lean_is_exclusive(v_x_4342_)) as u8;
                    if v_isSharedCheck_4370_ == 0 {
                        v___x_4354_ = v_x_4342_;
                        v_isShared_4355_ = v_isSharedCheck_4370_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4352_);
                        crate::leanh::lean_inc(v_head_4351_);
                        crate::leanh::lean_dec(v_x_4342_);
                        v___x_4354_ = crate::leanh::lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4356_ = l_Lean_Meta_MetaM_asTask_x27___redArg(
                    v_head_4351_,
                    v___y_4344_,
                    v___y_4345_,
                    v___y_4346_,
                    v___y_4347_,
                );
                if crate::leanh::lean_obj_tag(v___x_4356_) == 0 {
                    v_a_4357_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                    crate::leanh::lean_inc(v_a_4357_);
                    crate::leanh::lean_dec_ref_known(v___x_4356_, 1);
                    if v_isShared_4355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4354_, 1, v_x_4343_);
                        crate::leanh::lean_ctor_set(v___x_4354_, 0, v_a_4357_);
                        v___x_4359_ = v___x_4354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_x_4343_);
                        v___x_4359_ = v_reuseFailAlloc_4361_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4354_);
                    crate::leanh::lean_dec(v_tail_4352_);
                    crate::leanh::lean_dec(v_x_4343_);
                    v_a_4362_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                    v_isSharedCheck_4369_ = (!crate::leanh::lean_is_exclusive(v___x_4356_)) as u8;
                    if v_isSharedCheck_4369_ == 0 {
                        v___x_4364_ = v___x_4356_;
                        v_isShared_4365_ = v_isSharedCheck_4369_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4362_);
                        crate::leanh::lean_dec(v___x_4356_);
                        v___x_4364_ = crate::leanh::lean_box(0);
                        v_isShared_4365_ = v_isSharedCheck_4369_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4342_ = v_tail_4352_;
                v_x_4343_ = v___x_4359_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4365_ == 0 {
                    v___x_4367_ = v___x_4364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
                    v___x_4367_ = v_reuseFailAlloc_4368_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(
    mut v_x_4371_: *mut crate::leanh::LeanObject,
    mut v_x_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
        v_x_4371_,
        v_x_4372_,
        v___y_4373_,
        v___y_4374_,
        v___y_4375_,
        v___y_4376_,
    );
    crate::leanh::lean_dec(v___y_4376_);
    crate::leanh::lean_dec_ref(v___y_4375_);
    crate::leanh::lean_dec(v___y_4374_);
    crate::leanh::lean_dec_ref(v___y_4373_);
    return v_res_4378_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
    mut v_as_x27_4379_: *mut crate::leanh::LeanObject,
    mut v_b_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
    mut v___y_4383_: *mut crate::leanh::LeanObject,
    mut v___y_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4395_: u8 = 0;
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4401_: u8 = 0;
    let mut v___x_2329__overap_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_a_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4379_) == 0 {
                    v___x_4386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4386_, 0, v_b_4380_);
                    return v___x_4386_;
                } else {
                    v_head_4387_ = crate::leanh::lean_ctor_get(v_as_x27_4379_, 0);
                    v_tail_4388_ = crate::leanh::lean_ctor_get(v_as_x27_4379_, 1);
                    crate::leanh::lean_inc(v_head_4387_);
                    v___x_2329__overap_4402_ = lean_task_get_own(v_head_4387_);
                    crate::leanh::lean_inc(v___y_4384_);
                    crate::leanh::lean_inc_ref(v___y_4383_);
                    crate::leanh::lean_inc(v___y_4382_);
                    crate::leanh::lean_inc_ref(v___y_4381_);
                    v___x_4403_ = crate::leanh::lean_apply_5(
                        v___x_2329__overap_4402_,
                        v___y_4381_,
                        v___y_4382_,
                        v___y_4383_,
                        v___y_4384_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4403_) == 0 {
                        v_a_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                        crate::leanh::lean_inc(v_a_4404_);
                        crate::leanh::lean_dec_ref_known(v___x_4403_, 1);
                        v___x_4405_ = l_Lean_Meta_saveState___redArg(v___y_4382_, v___y_4384_);
                        if crate::leanh::lean_obj_tag(v___x_4405_) == 0 {
                            v_a_4406_ = crate::leanh::lean_ctor_get(v___x_4405_, 0);
                            v_isSharedCheck_4414_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4405_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4408_ = v___x_4405_;
                                v_isShared_4409_ = v_isSharedCheck_4414_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4406_);
                                crate::leanh::lean_dec(v___x_4405_);
                                v___x_4408_ = crate::leanh::lean_box(0);
                                v_isShared_4409_ = v_isSharedCheck_4414_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4404_);
                            v_a_4415_ = crate::leanh::lean_ctor_get(v___x_4405_, 0);
                            crate::leanh::lean_inc(v_a_4415_);
                            crate::leanh::lean_dec_ref_known(v___x_4405_, 1);
                            v_a_4399_ = v_a_4415_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4416_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                        crate::leanh::lean_inc(v_a_4416_);
                        crate::leanh::lean_dec_ref_known(v___x_4403_, 1);
                        v_a_4399_ = v_a_4416_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4391_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4391_, 0, v_a_4390_);
                crate::leanh::lean_ctor_set(v___x_4391_, 1, v_b_4380_);
                v_as_x27_4379_ = v_tail_4388_;
                v_b_4380_ = v___x_4391_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_4395_ == 0 {
                    v___x_4396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4396_, 0, v___y_4394_);
                    v_a_4390_ = v___x_4396_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_4380_);
                    v___x_4397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4397_, 0, v___y_4394_);
                    return v___x_4397_;
                }
            }
            3 => {
                v___x_4400_ = l_Lean_Exception_isInterrupt(v_a_4399_);
                if v___x_4400_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_4399_);
                    v___x_4401_ = l_Lean_Exception_isRuntime(v_a_4399_);
                    v___y_4394_ = v_a_4399_;
                    v___y_4395_ = v___x_4401_;
                    state = 2;
                    continue;
                } else {
                    v___y_4394_ = v_a_4399_;
                    v___y_4395_ = v___x_4400_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4410_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4410_, 0, v_a_4404_);
                crate::leanh::lean_ctor_set(v___x_4410_, 1, v_a_4406_);
                if v_isShared_4409_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4408_, 1);
                    crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4410_);
                    v___x_4412_ = v___x_4408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_4390_ = v___x_4412_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(
    mut v_as_x27_4417_: *mut crate::leanh::LeanObject,
    mut v_b_4418_: *mut crate::leanh::LeanObject,
    mut v___y_4419_: *mut crate::leanh::LeanObject,
    mut v___y_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
        v_as_x27_4417_,
        v_b_4418_,
        v___y_4419_,
        v___y_4420_,
        v___y_4421_,
        v___y_4422_,
    );
    crate::leanh::lean_dec(v___y_4422_);
    crate::leanh::lean_dec_ref(v___y_4421_);
    crate::leanh::lean_dec(v___y_4420_);
    crate::leanh::lean_dec_ref(v___y_4419_);
    crate::leanh::lean_dec(v_as_x27_4417_);
    return v_res_4424_;
}
pub unsafe fn l_Lean_Meta_MetaM_par___redArg(
    mut v_jobs_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v_a_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4431_ = lean_st_ref_get(v_a_4427_);
                v___x_4432_ = crate::leanh::lean_box(0);
                v___x_4433_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
                    v_jobs_4425_,
                    v___x_4432_,
                    v_a_4426_,
                    v_a_4427_,
                    v_a_4428_,
                    v_a_4429_,
                );
                if crate::leanh::lean_obj_tag(v___x_4433_) == 0 {
                    v_a_4434_ = crate::leanh::lean_ctor_get(v___x_4433_, 0);
                    crate::leanh::lean_inc(v_a_4434_);
                    crate::leanh::lean_dec_ref_known(v___x_4433_, 1);
                    v___x_4435_ =
                        l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
                            v_a_4434_,
                            v___x_4432_,
                            v_a_4426_,
                            v_a_4427_,
                            v_a_4428_,
                            v_a_4429_,
                        );
                    crate::leanh::lean_dec(v_a_4434_);
                    if crate::leanh::lean_obj_tag(v___x_4435_) == 0 {
                        v_a_4436_ = crate::leanh::lean_ctor_get(v___x_4435_, 0);
                        v_isSharedCheck_4445_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4435_)) as u8;
                        if v_isSharedCheck_4445_ == 0 {
                            v___x_4438_ = v___x_4435_;
                            v_isShared_4439_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4436_);
                            crate::leanh::lean_dec(v___x_4435_);
                            v___x_4438_ = crate::leanh::lean_box(0);
                            v_isShared_4439_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4431_);
                        return v___x_4435_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4431_);
                    v_a_4446_ = crate::leanh::lean_ctor_get(v___x_4433_, 0);
                    v_isSharedCheck_4453_ = (!crate::leanh::lean_is_exclusive(v___x_4433_)) as u8;
                    if v_isSharedCheck_4453_ == 0 {
                        v___x_4448_ = v___x_4433_;
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4446_);
                        crate::leanh::lean_dec(v___x_4433_);
                        v___x_4448_ = crate::leanh::lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4440_ = lean_st_ref_set(v_a_4427_, v___x_4431_);
                v___x_4441_ = l_List_reverse___redArg(v_a_4436_);
                if v_isShared_4439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4438_, 0, v___x_4441_);
                    v___x_4443_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
                    v___x_4443_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4443_;
            }
            3 => {
                if v_isShared_4449_ == 0 {
                    v___x_4451_ = v___x_4448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_par___redArg___boxed(
    mut v_jobs_4454_: *mut crate::leanh::LeanObject,
    mut v_a_4455_: *mut crate::leanh::LeanObject,
    mut v_a_4456_: *mut crate::leanh::LeanObject,
    mut v_a_4457_: *mut crate::leanh::LeanObject,
    mut v_a_4458_: *mut crate::leanh::LeanObject,
    mut v_a_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4460_ =
        l_Lean_Meta_MetaM_par___redArg(v_jobs_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
    crate::leanh::lean_dec(v_a_4458_);
    crate::leanh::lean_dec_ref(v_a_4457_);
    crate::leanh::lean_dec(v_a_4456_);
    crate::leanh::lean_dec_ref(v_a_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_Meta_MetaM_par(
    mut v_00_u03b1_4461_: *mut crate::leanh::LeanObject,
    mut v_jobs_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
    mut v_a_4465_: *mut crate::leanh::LeanObject,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ =
        l_Lean_Meta_MetaM_par___redArg(v_jobs_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
    return v___x_4468_;
}
pub unsafe fn l_Lean_Meta_MetaM_par___boxed(
    mut v_00_u03b1_4469_: *mut crate::leanh::LeanObject,
    mut v_jobs_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
    mut v_a_4474_: *mut crate::leanh::LeanObject,
    mut v_a_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_Meta_MetaM_par(
        v_00_u03b1_4469_,
        v_jobs_4470_,
        v_a_4471_,
        v_a_4472_,
        v_a_4473_,
        v_a_4474_,
    );
    crate::leanh::lean_dec(v_a_4474_);
    crate::leanh::lean_dec_ref(v_a_4473_);
    crate::leanh::lean_dec(v_a_4472_);
    crate::leanh::lean_dec_ref(v_a_4471_);
    return v_res_4476_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(
    mut v_00_u03b1_4477_: *mut crate::leanh::LeanObject,
    mut v_x_4478_: *mut crate::leanh::LeanObject,
    mut v_x_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4485_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
        v_x_4478_,
        v_x_4479_,
        v___y_4480_,
        v___y_4481_,
        v___y_4482_,
        v___y_4483_,
    );
    return v___x_4485_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(
    mut v_00_u03b1_4486_: *mut crate::leanh::LeanObject,
    mut v_x_4487_: *mut crate::leanh::LeanObject,
    mut v_x_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4494_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(
        v_00_u03b1_4486_,
        v_x_4487_,
        v_x_4488_,
        v___y_4489_,
        v___y_4490_,
        v___y_4491_,
        v___y_4492_,
    );
    crate::leanh::lean_dec(v___y_4492_);
    crate::leanh::lean_dec_ref(v___y_4491_);
    crate::leanh::lean_dec(v___y_4490_);
    crate::leanh::lean_dec_ref(v___y_4489_);
    return v_res_4494_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(
    mut v_00_u03b1_4495_: *mut crate::leanh::LeanObject,
    mut v_as_4496_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4497_: *mut crate::leanh::LeanObject,
    mut v_b_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
    mut v___y_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
    mut v___y_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4505_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
        v_as_x27_4497_,
        v_b_4498_,
        v___y_4500_,
        v___y_4501_,
        v___y_4502_,
        v___y_4503_,
    );
    return v___x_4505_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(
    mut v_00_u03b1_4506_: *mut crate::leanh::LeanObject,
    mut v_as_4507_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4508_: *mut crate::leanh::LeanObject,
    mut v_b_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(
        v_00_u03b1_4506_,
        v_as_4507_,
        v_as_x27_4508_,
        v_b_4509_,
        v_a_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
    );
    crate::leanh::lean_dec(v___y_4514_);
    crate::leanh::lean_dec_ref(v___y_4513_);
    crate::leanh::lean_dec(v___y_4512_);
    crate::leanh::lean_dec_ref(v___y_4511_);
    crate::leanh::lean_dec(v_as_x27_4508_);
    crate::leanh::lean_dec(v_as_4507_);
    return v_res_4516_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
    mut v_as_x27_4517_: *mut crate::leanh::LeanObject,
    mut v_b_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032__overap_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4536_: u8 = 0;
    let mut v___y_4538_: u8 = 0;
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: u8 = 0;
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4517_) == 0 {
                    v___x_4524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4524_, 0, v_b_4518_);
                    return v___x_4524_;
                } else {
                    v_head_4525_ = crate::leanh::lean_ctor_get(v_as_x27_4517_, 0);
                    v_tail_4526_ = crate::leanh::lean_ctor_get(v_as_x27_4517_, 1);
                    crate::leanh::lean_inc(v_head_4525_);
                    v___x_2032__overap_4527_ = lean_task_get_own(v_head_4525_);
                    crate::leanh::lean_inc(v___y_4522_);
                    crate::leanh::lean_inc_ref(v___y_4521_);
                    crate::leanh::lean_inc(v___y_4520_);
                    crate::leanh::lean_inc_ref(v___y_4519_);
                    v___x_4528_ = crate::leanh::lean_apply_5(
                        v___x_2032__overap_4527_,
                        v___y_4519_,
                        v___y_4520_,
                        v___y_4521_,
                        v___y_4522_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4528_) == 0 {
                        v_a_4529_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                        crate::leanh::lean_inc(v_a_4529_);
                        crate::leanh::lean_dec_ref_known(v___x_4528_, 1);
                        v___x_4530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4530_, 0, v_a_4529_);
                        v___x_4531_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4531_, 0, v___x_4530_);
                        crate::leanh::lean_ctor_set(v___x_4531_, 1, v_b_4518_);
                        v_as_x27_4517_ = v_tail_4526_;
                        v_b_4518_ = v___x_4531_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4533_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                        v_isSharedCheck_4547_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4528_)) as u8;
                        if v_isSharedCheck_4547_ == 0 {
                            v___x_4535_ = v___x_4528_;
                            v_isShared_4536_ = v_isSharedCheck_4547_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4533_);
                            crate::leanh::lean_dec(v___x_4528_);
                            v___x_4535_ = crate::leanh::lean_box(0);
                            v_isShared_4536_ = v_isSharedCheck_4547_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4545_ = l_Lean_Exception_isInterrupt(v_a_4533_);
                if v___x_4545_ == 0 {
                    crate::leanh::lean_inc(v_a_4533_);
                    v___x_4546_ = l_Lean_Exception_isRuntime(v_a_4533_);
                    v___y_4538_ = v___x_4546_;
                    state = 2;
                    continue;
                } else {
                    v___y_4538_ = v___x_4545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_4538_ == 0 {
                    crate::leanh::lean_del_object(v___x_4535_);
                    v___x_4539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4539_, 0, v_a_4533_);
                    v___x_4540_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4539_);
                    crate::leanh::lean_ctor_set(v___x_4540_, 1, v_b_4518_);
                    v_as_x27_4517_ = v_tail_4526_;
                    v_b_4518_ = v___x_4540_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_4518_);
                    if v_isShared_4536_ == 0 {
                        v___x_4543_ = v___x_4535_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4533_);
                        v___x_4543_ = v_reuseFailAlloc_4544_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(
    mut v_as_x27_4548_: *mut crate::leanh::LeanObject,
    mut v_b_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4555_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
        v_as_x27_4548_,
        v_b_4549_,
        v___y_4550_,
        v___y_4551_,
        v___y_4552_,
        v___y_4553_,
    );
    crate::leanh::lean_dec(v___y_4553_);
    crate::leanh::lean_dec_ref(v___y_4552_);
    crate::leanh::lean_dec(v___y_4551_);
    crate::leanh::lean_dec_ref(v___y_4550_);
    crate::leanh::lean_dec(v_as_x27_4548_);
    return v_res_4555_;
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27___redArg(
    mut v_jobs_4556_: *mut crate::leanh::LeanObject,
    mut v_a_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4562_ = lean_st_ref_get(v_a_4558_);
                v___x_4563_ = crate::leanh::lean_box(0);
                v___x_4564_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
                    v_jobs_4556_,
                    v___x_4563_,
                    v_a_4557_,
                    v_a_4558_,
                    v_a_4559_,
                    v_a_4560_,
                );
                if crate::leanh::lean_obj_tag(v___x_4564_) == 0 {
                    v_a_4565_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                    crate::leanh::lean_inc(v_a_4565_);
                    crate::leanh::lean_dec_ref_known(v___x_4564_, 1);
                    v___x_4566_ =
                        l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
                            v_a_4565_,
                            v___x_4563_,
                            v_a_4557_,
                            v_a_4558_,
                            v_a_4559_,
                            v_a_4560_,
                        );
                    crate::leanh::lean_dec(v_a_4565_);
                    if crate::leanh::lean_obj_tag(v___x_4566_) == 0 {
                        v_a_4567_ = crate::leanh::lean_ctor_get(v___x_4566_, 0);
                        v_isSharedCheck_4576_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4566_)) as u8;
                        if v_isSharedCheck_4576_ == 0 {
                            v___x_4569_ = v___x_4566_;
                            v_isShared_4570_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4567_);
                            crate::leanh::lean_dec(v___x_4566_);
                            v___x_4569_ = crate::leanh::lean_box(0);
                            v_isShared_4570_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4562_);
                        return v___x_4566_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4562_);
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                    v_isSharedCheck_4584_ = (!crate::leanh::lean_is_exclusive(v___x_4564_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4564_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4577_);
                        crate::leanh::lean_dec(v___x_4564_);
                        v___x_4579_ = crate::leanh::lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4571_ = lean_st_ref_set(v_a_4558_, v___x_4562_);
                v___x_4572_ = l_List_reverse___redArg(v_a_4567_);
                if v_isShared_4570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4569_, 0, v___x_4572_);
                    v___x_4574_ = v___x_4569_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
                    v___x_4574_ = v_reuseFailAlloc_4575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4574_;
            }
            3 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27___redArg___boxed(
    mut v_jobs_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lean_Meta_MetaM_par_x27___redArg(
        v_jobs_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
    );
    crate::leanh::lean_dec(v_a_4589_);
    crate::leanh::lean_dec_ref(v_a_4588_);
    crate::leanh::lean_dec(v_a_4587_);
    crate::leanh::lean_dec_ref(v_a_4586_);
    return v_res_4591_;
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27(
    mut v_00_u03b1_4592_: *mut crate::leanh::LeanObject,
    mut v_jobs_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ = l_Lean_Meta_MetaM_par_x27___redArg(
        v_jobs_4593_,
        v_a_4594_,
        v_a_4595_,
        v_a_4596_,
        v_a_4597_,
    );
    return v___x_4599_;
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27___boxed(
    mut v_00_u03b1_4600_: *mut crate::leanh::LeanObject,
    mut v_jobs_4601_: *mut crate::leanh::LeanObject,
    mut v_a_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
    mut v_a_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_a_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4607_ = l_Lean_Meta_MetaM_par_x27(
        v_00_u03b1_4600_,
        v_jobs_4601_,
        v_a_4602_,
        v_a_4603_,
        v_a_4604_,
        v_a_4605_,
    );
    crate::leanh::lean_dec(v_a_4605_);
    crate::leanh::lean_dec_ref(v_a_4604_);
    crate::leanh::lean_dec(v_a_4603_);
    crate::leanh::lean_dec_ref(v_a_4602_);
    return v_res_4607_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(
    mut v_00_u03b1_4608_: *mut crate::leanh::LeanObject,
    mut v_as_4609_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4610_: *mut crate::leanh::LeanObject,
    mut v_b_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4618_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
        v_as_x27_4610_,
        v_b_4611_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
        v___y_4616_,
    );
    return v___x_4618_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(
    mut v_00_u03b1_4619_: *mut crate::leanh::LeanObject,
    mut v_as_4620_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4621_: *mut crate::leanh::LeanObject,
    mut v_b_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4629_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(
        v_00_u03b1_4619_,
        v_as_4620_,
        v_as_x27_4621_,
        v_b_4622_,
        v_a_4623_,
        v___y_4624_,
        v___y_4625_,
        v___y_4626_,
        v___y_4627_,
    );
    crate::leanh::lean_dec(v___y_4627_);
    crate::leanh::lean_dec_ref(v___y_4626_);
    crate::leanh::lean_dec(v___y_4625_);
    crate::leanh::lean_dec_ref(v___y_4624_);
    crate::leanh::lean_dec(v_as_x27_4621_);
    crate::leanh::lean_dec(v_as_4620_);
    return v_res_4629_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
    mut v_x_4630_: *mut crate::leanh::LeanObject,
    mut v_x_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_isSharedCheck_4658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4630_) == 0 {
                    v___x_4637_ = l_List_reverse___redArg(v_x_4631_);
                    v___x_4638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4638_, 0, v___x_4637_);
                    return v___x_4638_;
                } else {
                    v_head_4639_ = crate::leanh::lean_ctor_get(v_x_4630_, 0);
                    v_tail_4640_ = crate::leanh::lean_ctor_get(v_x_4630_, 1);
                    v_isSharedCheck_4658_ = (!crate::leanh::lean_is_exclusive(v_x_4630_)) as u8;
                    if v_isSharedCheck_4658_ == 0 {
                        v___x_4642_ = v_x_4630_;
                        v_isShared_4643_ = v_isSharedCheck_4658_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4640_);
                        crate::leanh::lean_inc(v_head_4639_);
                        crate::leanh::lean_dec(v_x_4630_);
                        v___x_4642_ = crate::leanh::lean_box(0);
                        v_isShared_4643_ = v_isSharedCheck_4658_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4644_ = l_Lean_Meta_MetaM_asTask___redArg(
                    v_head_4639_,
                    v___y_4632_,
                    v___y_4633_,
                    v___y_4634_,
                    v___y_4635_,
                );
                if crate::leanh::lean_obj_tag(v___x_4644_) == 0 {
                    v_a_4645_ = crate::leanh::lean_ctor_get(v___x_4644_, 0);
                    crate::leanh::lean_inc(v_a_4645_);
                    crate::leanh::lean_dec_ref_known(v___x_4644_, 1);
                    if v_isShared_4643_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4642_, 1, v_x_4631_);
                        crate::leanh::lean_ctor_set(v___x_4642_, 0, v_a_4645_);
                        v___x_4647_ = v___x_4642_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4649_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4645_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_x_4631_);
                        v___x_4647_ = v_reuseFailAlloc_4649_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4642_);
                    crate::leanh::lean_dec(v_tail_4640_);
                    crate::leanh::lean_dec(v_x_4631_);
                    v_a_4650_ = crate::leanh::lean_ctor_get(v___x_4644_, 0);
                    v_isSharedCheck_4657_ = (!crate::leanh::lean_is_exclusive(v___x_4644_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4652_ = v___x_4644_;
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4650_);
                        crate::leanh::lean_dec(v___x_4644_);
                        v___x_4652_ = crate::leanh::lean_box(0);
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4630_ = v_tail_4640_;
                v_x_4631_ = v___x_4647_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4653_ == 0 {
                    v___x_4655_ = v___x_4652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
                    v___x_4655_ = v_reuseFailAlloc_4656_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(
    mut v_x_4659_: *mut crate::leanh::LeanObject,
    mut v_x_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
        v_x_4659_,
        v_x_4660_,
        v___y_4661_,
        v___y_4662_,
        v___y_4663_,
        v___y_4664_,
    );
    crate::leanh::lean_dec(v___y_4664_);
    crate::leanh::lean_dec_ref(v___y_4663_);
    crate::leanh::lean_dec(v___y_4662_);
    crate::leanh::lean_dec_ref(v___y_4661_);
    return v_res_4666_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel___redArg(
    mut v_jobs_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
    mut v_a_4669_: *mut crate::leanh::LeanObject,
    mut v_a_4670_: *mut crate::leanh::LeanObject,
    mut v_a_4671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_isSharedCheck_4693_: u8 = 0;
    let mut v_a_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4673_ = crate::leanh::lean_box(0);
                v___x_4674_ =
                    l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
                        v_jobs_4667_,
                        v___x_4673_,
                        v_a_4668_,
                        v_a_4669_,
                        v_a_4670_,
                        v_a_4671_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4674_) == 0 {
                    v_a_4675_ = crate::leanh::lean_ctor_get(v___x_4674_, 0);
                    v_isSharedCheck_4693_ = (!crate::leanh::lean_is_exclusive(v___x_4674_)) as u8;
                    if v_isSharedCheck_4693_ == 0 {
                        v___x_4677_ = v___x_4674_;
                        v_isShared_4678_ = v_isSharedCheck_4693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4675_);
                        crate::leanh::lean_dec(v___x_4674_);
                        v___x_4677_ = crate::leanh::lean_box(0);
                        v_isShared_4678_ = v_isSharedCheck_4693_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4694_ = crate::leanh::lean_ctor_get(v___x_4674_, 0);
                    v_isSharedCheck_4701_ = (!crate::leanh::lean_is_exclusive(v___x_4674_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v___x_4696_ = v___x_4674_;
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4694_);
                        crate::leanh::lean_dec(v___x_4674_);
                        v___x_4696_ = crate::leanh::lean_box(0);
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4679_ = l_List_unzipTR___redArg(v_a_4675_);
                v_fst_4680_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                v_snd_4681_ = crate::leanh::lean_ctor_get(v___x_4679_, 1);
                v_isSharedCheck_4692_ = (!crate::leanh::lean_is_exclusive(v___x_4679_)) as u8;
                if v_isSharedCheck_4692_ == 0 {
                    v___x_4683_ = v___x_4679_;
                    v_isShared_4684_ = v_isSharedCheck_4692_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4681_);
                    crate::leanh::lean_inc(v_fst_4680_);
                    crate::leanh::lean_dec(v___x_4679_);
                    v___x_4683_ = crate::leanh::lean_box(0);
                    v_isShared_4684_ = v_isSharedCheck_4692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4685_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4685_, 0, v_fst_4680_);
                if v_isShared_4684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4683_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4683_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_snd_4681_);
                    v___x_4687_ = v_reuseFailAlloc_4691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4677_, 0, v___x_4687_);
                    v___x_4689_ = v___x_4677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
                    v___x_4689_ = v_reuseFailAlloc_4690_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4689_;
            }
            5 => {
                if v_isShared_4697_ == 0 {
                    v___x_4699_ = v___x_4696_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(
    mut v_jobs_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(
        v_jobs_4702_,
        v_a_4703_,
        v_a_4704_,
        v_a_4705_,
        v_a_4706_,
    );
    crate::leanh::lean_dec(v_a_4706_);
    crate::leanh::lean_dec_ref(v_a_4705_);
    crate::leanh::lean_dec(v_a_4704_);
    crate::leanh::lean_dec_ref(v_a_4703_);
    return v_res_4708_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel(
    mut v_00_u03b1_4709_: *mut crate::leanh::LeanObject,
    mut v_jobs_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4716_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(
        v_jobs_4710_,
        v_a_4711_,
        v_a_4712_,
        v_a_4713_,
        v_a_4714_,
    );
    return v___x_4716_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel___boxed(
    mut v_00_u03b1_4717_: *mut crate::leanh::LeanObject,
    mut v_jobs_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v_a_4721_: *mut crate::leanh::LeanObject,
    mut v_a_4722_: *mut crate::leanh::LeanObject,
    mut v_a_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Lean_Meta_MetaM_parIterWithCancel(
        v_00_u03b1_4717_,
        v_jobs_4718_,
        v_a_4719_,
        v_a_4720_,
        v_a_4721_,
        v_a_4722_,
    );
    crate::leanh::lean_dec(v_a_4722_);
    crate::leanh::lean_dec_ref(v_a_4721_);
    crate::leanh::lean_dec(v_a_4720_);
    crate::leanh::lean_dec_ref(v_a_4719_);
    return v_res_4724_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(
    mut v_00_u03b1_4725_: *mut crate::leanh::LeanObject,
    mut v_x_4726_: *mut crate::leanh::LeanObject,
    mut v_x_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4733_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
        v_x_4726_,
        v_x_4727_,
        v___y_4728_,
        v___y_4729_,
        v___y_4730_,
        v___y_4731_,
    );
    return v___x_4733_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(
    mut v_00_u03b1_4734_: *mut crate::leanh::LeanObject,
    mut v_x_4735_: *mut crate::leanh::LeanObject,
    mut v_x_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(
        v_00_u03b1_4734_,
        v_x_4735_,
        v_x_4736_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
    );
    crate::leanh::lean_dec(v___y_4740_);
    crate::leanh::lean_dec_ref(v___y_4739_);
    crate::leanh::lean_dec(v___y_4738_);
    crate::leanh::lean_dec_ref(v___y_4737_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIter___redArg(
    mut v_jobs_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4753_: u8 = 0;
    let mut v_snd_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut v_a_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4749_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(
                    v_jobs_4743_,
                    v_a_4744_,
                    v_a_4745_,
                    v_a_4746_,
                    v_a_4747_,
                );
                if crate::leanh::lean_obj_tag(v___x_4749_) == 0 {
                    v_a_4750_ = crate::leanh::lean_ctor_get(v___x_4749_, 0);
                    v_isSharedCheck_4758_ = (!crate::leanh::lean_is_exclusive(v___x_4749_)) as u8;
                    if v_isSharedCheck_4758_ == 0 {
                        v___x_4752_ = v___x_4749_;
                        v_isShared_4753_ = v_isSharedCheck_4758_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4750_);
                        crate::leanh::lean_dec(v___x_4749_);
                        v___x_4752_ = crate::leanh::lean_box(0);
                        v_isShared_4753_ = v_isSharedCheck_4758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4759_ = crate::leanh::lean_ctor_get(v___x_4749_, 0);
                    v_isSharedCheck_4766_ = (!crate::leanh::lean_is_exclusive(v___x_4749_)) as u8;
                    if v_isSharedCheck_4766_ == 0 {
                        v___x_4761_ = v___x_4749_;
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4759_);
                        crate::leanh::lean_dec(v___x_4749_);
                        v___x_4761_ = crate::leanh::lean_box(0);
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4754_ = crate::leanh::lean_ctor_get(v_a_4750_, 1);
                crate::leanh::lean_inc(v_snd_4754_);
                crate::leanh::lean_dec(v_a_4750_);
                if v_isShared_4753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4752_, 0, v_snd_4754_);
                    v___x_4756_ = v___x_4752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_snd_4754_);
                    v___x_4756_ = v_reuseFailAlloc_4757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4756_;
            }
            3 => {
                if v_isShared_4762_ == 0 {
                    v___x_4764_ = v___x_4761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
                    v___x_4764_ = v_reuseFailAlloc_4765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_parIter___redArg___boxed(
    mut v_jobs_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Meta_MetaM_parIter___redArg(
        v_jobs_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
    );
    crate::leanh::lean_dec(v_a_4771_);
    crate::leanh::lean_dec_ref(v_a_4770_);
    crate::leanh::lean_dec(v_a_4769_);
    crate::leanh::lean_dec_ref(v_a_4768_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIter(
    mut v_00_u03b1_4774_: *mut crate::leanh::LeanObject,
    mut v_jobs_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4781_ = l_Lean_Meta_MetaM_parIter___redArg(
        v_jobs_4775_,
        v_a_4776_,
        v_a_4777_,
        v_a_4778_,
        v_a_4779_,
    );
    return v___x_4781_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIter___boxed(
    mut v_00_u03b1_4782_: *mut crate::leanh::LeanObject,
    mut v_jobs_4783_: *mut crate::leanh::LeanObject,
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v_a_4785_: *mut crate::leanh::LeanObject,
    mut v_a_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Lean_Meta_MetaM_parIter(
        v_00_u03b1_4782_,
        v_jobs_4783_,
        v_a_4784_,
        v_a_4785_,
        v_a_4786_,
        v_a_4787_,
    );
    crate::leanh::lean_dec(v_a_4787_);
    crate::leanh::lean_dec_ref(v_a_4786_);
    crate::leanh::lean_dec(v_a_4785_);
    crate::leanh::lean_dec_ref(v_a_4784_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
    mut v_jobs_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4807_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut v_a_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4820_: u8 = 0;
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = crate::leanh::lean_box(0);
                v___x_4797_ =
                    l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
                        v_jobs_4790_,
                        v___x_4796_,
                        v_a_4791_,
                        v_a_4792_,
                        v_a_4793_,
                        v_a_4794_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4816_ = (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4816_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_dec(v___x_4797_);
                        v___x_4800_ = crate::leanh::lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4817_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4824_ = (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v___x_4819_ = v___x_4797_;
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4817_);
                        crate::leanh::lean_dec(v___x_4797_);
                        v___x_4819_ = crate::leanh::lean_box(0);
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4802_ = l_List_unzipTR___redArg(v_a_4798_);
                v_fst_4803_ = crate::leanh::lean_ctor_get(v___x_4802_, 0);
                v_snd_4804_ = crate::leanh::lean_ctor_get(v___x_4802_, 1);
                v_isSharedCheck_4815_ = (!crate::leanh::lean_is_exclusive(v___x_4802_)) as u8;
                if v_isSharedCheck_4815_ == 0 {
                    v___x_4806_ = v___x_4802_;
                    v_isShared_4807_ = v_isSharedCheck_4815_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4804_);
                    crate::leanh::lean_inc(v_fst_4803_);
                    crate::leanh::lean_dec(v___x_4802_);
                    v___x_4806_ = crate::leanh::lean_box(0);
                    v_isShared_4807_ = v_isSharedCheck_4815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4808_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4808_, 0, v_fst_4803_);
                if v_isShared_4807_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4806_, 0, v___x_4808_);
                    v___x_4810_ = v___x_4806_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_snd_4804_);
                    v___x_4810_ = v_reuseFailAlloc_4814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4800_, 0, v___x_4810_);
                    v___x_4812_ = v___x_4800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
                    v___x_4812_ = v_reuseFailAlloc_4813_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4812_;
            }
            5 => {
                if v_isShared_4820_ == 0 {
                    v___x_4822_ = v___x_4819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
                    v___x_4822_ = v_reuseFailAlloc_4823_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(
    mut v_jobs_4825_: *mut crate::leanh::LeanObject,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_a_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
        v_jobs_4825_,
        v_a_4826_,
        v_a_4827_,
        v_a_4828_,
        v_a_4829_,
    );
    crate::leanh::lean_dec(v_a_4829_);
    crate::leanh::lean_dec_ref(v_a_4828_);
    crate::leanh::lean_dec(v_a_4827_);
    crate::leanh::lean_dec_ref(v_a_4826_);
    return v_res_4831_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel(
    mut v_00_u03b1_4832_: *mut crate::leanh::LeanObject,
    mut v_jobs_4833_: *mut crate::leanh::LeanObject,
    mut v_a_4834_: *mut crate::leanh::LeanObject,
    mut v_a_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
    mut v_a_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4839_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
        v_jobs_4833_,
        v_a_4834_,
        v_a_4835_,
        v_a_4836_,
        v_a_4837_,
    );
    return v___x_4839_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(
    mut v_00_u03b1_4840_: *mut crate::leanh::LeanObject,
    mut v_jobs_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
    mut v_a_4844_: *mut crate::leanh::LeanObject,
    mut v_a_4845_: *mut crate::leanh::LeanObject,
    mut v_a_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(
        v_00_u03b1_4840_,
        v_jobs_4841_,
        v_a_4842_,
        v_a_4843_,
        v_a_4844_,
        v_a_4845_,
    );
    crate::leanh::lean_dec(v_a_4845_);
    crate::leanh::lean_dec_ref(v_a_4844_);
    crate::leanh::lean_dec(v_a_4843_);
    crate::leanh::lean_dec_ref(v_a_4842_);
    return v_res_4847_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy___redArg(
    mut v_jobs_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v_snd_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v_a_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4854_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
                    v_jobs_4848_,
                    v_a_4849_,
                    v_a_4850_,
                    v_a_4851_,
                    v_a_4852_,
                );
                if crate::leanh::lean_obj_tag(v___x_4854_) == 0 {
                    v_a_4855_ = crate::leanh::lean_ctor_get(v___x_4854_, 0);
                    v_isSharedCheck_4863_ = (!crate::leanh::lean_is_exclusive(v___x_4854_)) as u8;
                    if v_isSharedCheck_4863_ == 0 {
                        v___x_4857_ = v___x_4854_;
                        v_isShared_4858_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4855_);
                        crate::leanh::lean_dec(v___x_4854_);
                        v___x_4857_ = crate::leanh::lean_box(0);
                        v_isShared_4858_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4864_ = crate::leanh::lean_ctor_get(v___x_4854_, 0);
                    v_isSharedCheck_4871_ = (!crate::leanh::lean_is_exclusive(v___x_4854_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4866_ = v___x_4854_;
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4864_);
                        crate::leanh::lean_dec(v___x_4854_);
                        v___x_4866_ = crate::leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4859_ = crate::leanh::lean_ctor_get(v_a_4855_, 1);
                crate::leanh::lean_inc(v_snd_4859_);
                crate::leanh::lean_dec(v_a_4855_);
                if v_isShared_4858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4857_, 0, v_snd_4859_);
                    v___x_4861_ = v___x_4857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_snd_4859_);
                    v___x_4861_ = v_reuseFailAlloc_4862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4861_;
            }
            3 => {
                if v_isShared_4867_ == 0 {
                    v___x_4869_ = v___x_4866_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
                    v___x_4869_ = v_reuseFailAlloc_4870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(
    mut v_jobs_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4878_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(
        v_jobs_4872_,
        v_a_4873_,
        v_a_4874_,
        v_a_4875_,
        v_a_4876_,
    );
    crate::leanh::lean_dec(v_a_4876_);
    crate::leanh::lean_dec_ref(v_a_4875_);
    crate::leanh::lean_dec(v_a_4874_);
    crate::leanh::lean_dec_ref(v_a_4873_);
    return v_res_4878_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy(
    mut v_00_u03b1_4879_: *mut crate::leanh::LeanObject,
    mut v_jobs_4880_: *mut crate::leanh::LeanObject,
    mut v_a_4881_: *mut crate::leanh::LeanObject,
    mut v_a_4882_: *mut crate::leanh::LeanObject,
    mut v_a_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4886_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(
        v_jobs_4880_,
        v_a_4881_,
        v_a_4882_,
        v_a_4883_,
        v_a_4884_,
    );
    return v___x_4886_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy___boxed(
    mut v_00_u03b1_4887_: *mut crate::leanh::LeanObject,
    mut v_jobs_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Lean_Meta_MetaM_parIterGreedy(
        v_00_u03b1_4887_,
        v_jobs_4888_,
        v_a_4889_,
        v_a_4890_,
        v_a_4891_,
        v_a_4892_,
    );
    crate::leanh::lean_dec(v_a_4892_);
    crate::leanh::lean_dec_ref(v_a_4891_);
    crate::leanh::lean_dec(v_a_4890_);
    crate::leanh::lean_dec_ref(v_a_4889_);
    return v_res_4894_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(
    mut v_a_4895_: *mut crate::leanh::LeanObject,
    mut v___x_4896_: *mut crate::leanh::LeanObject,
    mut v_____r_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4903_, 0, v_a_4895_);
    v___x_4904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    crate::leanh::lean_ctor_set(v___x_4904_, 1, v___x_4896_);
    v___x_4905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4904_);
    v___x_4906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4906_, 0, v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_4907_: *mut crate::leanh::LeanObject,
    mut v___x_4908_: *mut crate::leanh::LeanObject,
    mut v_____r_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4915_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(
            v_a_4907_,
            v___x_4908_,
            v_____r_4909_,
            v___y_4910_,
            v___y_4911_,
            v___y_4912_,
            v___y_4913_,
        );
    crate::leanh::lean_dec(v___y_4913_);
    crate::leanh::lean_dec_ref(v___y_4912_);
    crate::leanh::lean_dec(v___y_4911_);
    crate::leanh::lean_dec_ref(v___y_4910_);
    return v_res_4915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(
    mut v_cancel_4916_: u8,
    mut v_fst_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_b_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v_a_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4941_: u8 = 0;
    let mut v_a_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4960_: u8 = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4963_: u8 = 0;
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: u8 = 0;
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4918_) == 0 {
                    crate::leanh::lean_dec_ref(v_fst_4917_);
                    v___x_4925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4925_, 0, v_b_4919_);
                    return v___x_4925_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4919_);
                    v___x_4926_ = l_IO_waitAny_x27___redArg(v_a_4918_);
                    v_fst_4927_ = crate::leanh::lean_ctor_get(v___x_4926_, 0);
                    crate::leanh::lean_inc(v_fst_4927_);
                    v_snd_4928_ = crate::leanh::lean_ctor_get(v___x_4926_, 1);
                    crate::leanh::lean_inc(v_snd_4928_);
                    crate::leanh::lean_dec_ref(v___x_4926_);
                    v___x_4950_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_4923_);
                    crate::leanh::lean_inc_ref(v___y_4922_);
                    crate::leanh::lean_inc(v___y_4921_);
                    crate::leanh::lean_inc_ref(v___y_4920_);
                    v___x_4951_ = crate::leanh::lean_apply_5(
                        v_fst_4927_,
                        v___y_4920_,
                        v___y_4921_,
                        v___y_4922_,
                        v___y_4923_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4951_) == 0 {
                        if v_cancel_4916_ == 0 {
                            v_a_4952_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                            crate::leanh::lean_inc(v_a_4952_);
                            crate::leanh::lean_dec_ref_known(v___x_4951_, 1);
                            v___x_4953_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_4952_, v___x_4950_, v___x_4950_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
                            v___y_4930_ = v___x_4953_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4954_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                            crate::leanh::lean_inc(v_a_4954_);
                            crate::leanh::lean_dec_ref_known(v___x_4951_, 1);
                            crate::leanh::lean_inc_ref(v_fst_4917_);
                            v___x_4955_ =
                                crate::leanh::lean_apply_1(v_fst_4917_, crate::leanh::lean_box(0));
                            v___x_4956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_4954_, v___x_4950_, v___x_4955_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
                            v___y_4930_ = v___x_4956_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4957_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4970_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4970_ == 0 {
                            v___x_4959_ = v___x_4951_;
                            v_isShared_4960_ = v_isSharedCheck_4970_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4957_);
                            crate::leanh::lean_dec(v___x_4951_);
                            v___x_4959_ = crate::leanh::lean_box(0);
                            v_isShared_4960_ = v_isSharedCheck_4970_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4930_) == 0 {
                    v_a_4931_ = crate::leanh::lean_ctor_get(v___y_4930_, 0);
                    v_isSharedCheck_4941_ = (!crate::leanh::lean_is_exclusive(v___y_4930_)) as u8;
                    if v_isSharedCheck_4941_ == 0 {
                        v___x_4933_ = v___y_4930_;
                        v_isShared_4934_ = v_isSharedCheck_4941_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4931_);
                        crate::leanh::lean_dec(v___y_4930_);
                        v___x_4933_ = crate::leanh::lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4941_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4928_);
                    crate::leanh::lean_dec_ref(v_fst_4917_);
                    v_a_4942_ = crate::leanh::lean_ctor_get(v___y_4930_, 0);
                    v_isSharedCheck_4949_ = (!crate::leanh::lean_is_exclusive(v___y_4930_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4944_ = v___y_4930_;
                        v_isShared_4945_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4942_);
                        crate::leanh::lean_dec(v___y_4930_);
                        v___x_4944_ = crate::leanh::lean_box(0);
                        v_isShared_4945_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4931_) == 0 {
                    crate::leanh::lean_dec(v_snd_4928_);
                    crate::leanh::lean_dec_ref(v_fst_4917_);
                    v_a_4935_ = crate::leanh::lean_ctor_get(v_a_4931_, 0);
                    crate::leanh::lean_inc(v_a_4935_);
                    crate::leanh::lean_dec_ref_known(v_a_4931_, 1);
                    if v_isShared_4934_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4933_, 0, v_a_4935_);
                        v___x_4937_ = v___x_4933_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4938_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4935_);
                        v___x_4937_ = v_reuseFailAlloc_4938_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4933_);
                    v_a_4939_ = crate::leanh::lean_ctor_get(v_a_4931_, 0);
                    crate::leanh::lean_inc(v_a_4939_);
                    crate::leanh::lean_dec_ref_known(v_a_4931_, 1);
                    v_a_4918_ = v_snd_4928_;
                    v_b_4919_ = v_a_4939_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4937_;
            }
            4 => {
                if v_isShared_4945_ == 0 {
                    v___x_4947_ = v___x_4944_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
                    v___x_4947_ = v_reuseFailAlloc_4948_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4947_;
            }
            6 => {
                v___x_4961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                v___x_4968_ = l_Lean_Exception_isInterrupt(v_a_4957_);
                if v___x_4968_ == 0 {
                    crate::leanh::lean_inc(v_a_4957_);
                    v___x_4969_ = l_Lean_Exception_isRuntime(v_a_4957_);
                    v___y_4963_ = v___x_4969_;
                    state = 7;
                    continue;
                } else {
                    v___y_4963_ = v___x_4968_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_4963_ == 0 {
                    crate::leanh::lean_del_object(v___x_4959_);
                    crate::leanh::lean_dec(v_a_4957_);
                    v_a_4918_ = v_snd_4928_;
                    v_b_4919_ = v___x_4961_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4928_);
                    crate::leanh::lean_dec_ref(v_fst_4917_);
                    if v_isShared_4960_ == 0 {
                        v___x_4966_ = v___x_4959_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4957_);
                        v___x_4966_ = v_reuseFailAlloc_4967_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_4966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(
    mut v_cancel_4971_: *mut crate::leanh::LeanObject,
    mut v_fst_4972_: *mut crate::leanh::LeanObject,
    mut v_a_4973_: *mut crate::leanh::LeanObject,
    mut v_b_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_4980_: u8 = 0;
    let mut v_res_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4980_ = (crate::leanh::lean_unbox(v_cancel_4971_) as u8);
    v_res_4981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(
        v_cancel_boxed_4980_,
        v_fst_4972_,
        v_a_4973_,
        v_b_4974_,
        v___y_4975_,
        v___y_4976_,
        v___y_4977_,
        v___y_4978_,
    );
    crate::leanh::lean_dec(v___y_4978_);
    crate::leanh::lean_dec_ref(v___y_4977_);
    crate::leanh::lean_dec(v___y_4976_);
    crate::leanh::lean_dec_ref(v___y_4975_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(
    mut v_msgData_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4988_ = lean_st_ref_get(v___y_4986_);
    v_env_4989_ = crate::leanh::lean_ctor_get(v___x_4988_, 0);
    crate::leanh::lean_inc_ref(v_env_4989_);
    crate::leanh::lean_dec(v___x_4988_);
    v___x_4990_ = lean_st_ref_get(v___y_4984_);
    v_mctx_4991_ = crate::leanh::lean_ctor_get(v___x_4990_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4991_);
    crate::leanh::lean_dec(v___x_4990_);
    v_lctx_4992_ = crate::leanh::lean_ctor_get(v___y_4983_, 2);
    v_options_4993_ = crate::leanh::lean_ctor_get(v___y_4985_, 2);
    crate::leanh::lean_inc_ref(v_options_4993_);
    crate::leanh::lean_inc_ref(v_lctx_4992_);
    v___x_4994_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4994_, 0, v_env_4989_);
    crate::leanh::lean_ctor_set(v___x_4994_, 1, v_mctx_4991_);
    crate::leanh::lean_ctor_set(v___x_4994_, 2, v_lctx_4992_);
    crate::leanh::lean_ctor_set(v___x_4994_, 3, v_options_4993_);
    v___x_4995_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4995_, 0, v___x_4994_);
    crate::leanh::lean_ctor_set(v___x_4995_, 1, v_msgData_4982_);
    v___x_4996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4996_, 0, v___x_4995_);
    return v___x_4996_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
    crate::leanh::lean_dec(v___y_5001_);
    crate::leanh::lean_dec_ref(v___y_5000_);
    crate::leanh::lean_dec(v___y_4999_);
    crate::leanh::lean_dec_ref(v___y_4998_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
    mut v_msg_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5010_ = crate::leanh::lean_ctor_get(v___y_5007_, 5);
                v___x_5011_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
                v_a_5012_ = crate::leanh::lean_ctor_get(v___x_5011_, 0);
                v_isSharedCheck_5020_ = (!crate::leanh::lean_is_exclusive(v___x_5011_)) as u8;
                if v_isSharedCheck_5020_ == 0 {
                    v___x_5014_ = v___x_5011_;
                    v_isShared_5015_ = v_isSharedCheck_5020_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5012_);
                    crate::leanh::lean_dec(v___x_5011_);
                    v___x_5014_ = crate::leanh::lean_box(0);
                    v_isShared_5015_ = v_isSharedCheck_5020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5010_);
                v___x_5016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5016_, 0, v_ref_5010_);
                crate::leanh::lean_ctor_set(v___x_5016_, 1, v_a_5012_);
                if v_isShared_5015_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5014_, 1);
                    crate::leanh::lean_ctor_set(v___x_5014_, 0, v___x_5016_);
                    v___x_5018_ = v___x_5014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5016_);
                    v___x_5018_ = v_reuseFailAlloc_5019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(
    mut v_msg_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
        v_msg_5021_,
        v___y_5022_,
        v___y_5023_,
        v___y_5024_,
        v___y_5025_,
    );
    crate::leanh::lean_dec(v___y_5025_);
    crate::leanh::lean_dec_ref(v___y_5024_);
    crate::leanh::lean_dec(v___y_5023_);
    crate::leanh::lean_dec_ref(v___y_5022_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst___redArg(
    mut v_jobs_5028_: *mut crate::leanh::LeanObject,
    mut v_cancel_5029_: u8,
    mut v_a_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
    mut v_a_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v_fst_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut v_a_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_a_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5035_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
                    v_jobs_5028_,
                    v_a_5030_,
                    v_a_5031_,
                    v_a_5032_,
                    v_a_5033_,
                );
                if crate::leanh::lean_obj_tag(v___x_5035_) == 0 {
                    v_a_5036_ = crate::leanh::lean_ctor_get(v___x_5035_, 0);
                    crate::leanh::lean_inc(v_a_5036_);
                    crate::leanh::lean_dec_ref_known(v___x_5035_, 1);
                    v_fst_5037_ = crate::leanh::lean_ctor_get(v_a_5036_, 0);
                    crate::leanh::lean_inc(v_fst_5037_);
                    v_snd_5038_ = crate::leanh::lean_ctor_get(v_a_5036_, 1);
                    crate::leanh::lean_inc(v_snd_5038_);
                    crate::leanh::lean_dec(v_a_5036_);
                    v___x_5039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_5040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_5029_, v_fst_5037_, v_snd_5038_, v___x_5039_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                    if crate::leanh::lean_obj_tag(v___x_5040_) == 0 {
                        v_a_5041_ = crate::leanh::lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5052_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5052_ == 0 {
                            v___x_5043_ = v___x_5040_;
                            v_isShared_5044_ = v_isSharedCheck_5052_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5041_);
                            crate::leanh::lean_dec(v___x_5040_);
                            v___x_5043_ = crate::leanh::lean_box(0);
                            v_isShared_5044_ = v_isSharedCheck_5052_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5053_ = crate::leanh::lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5060_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5060_ == 0 {
                            v___x_5055_ = v___x_5040_;
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5053_);
                            crate::leanh::lean_dec(v___x_5040_);
                            v___x_5055_ = crate::leanh::lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5061_ = crate::leanh::lean_ctor_get(v___x_5035_, 0);
                    v_isSharedCheck_5068_ = (!crate::leanh::lean_is_exclusive(v___x_5035_)) as u8;
                    if v_isSharedCheck_5068_ == 0 {
                        v___x_5063_ = v___x_5035_;
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5061_);
                        crate::leanh::lean_dec(v___x_5035_);
                        v___x_5063_ = crate::leanh::lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5045_ = crate::leanh::lean_ctor_get(v_a_5041_, 0);
                crate::leanh::lean_inc(v_fst_5045_);
                crate::leanh::lean_dec(v_a_5041_);
                if crate::leanh::lean_obj_tag(v_fst_5045_) == 0 {
                    crate::leanh::lean_del_object(v___x_5043_);
                    v___x_5046_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_5047_ =
                        l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
                            v___x_5046_,
                            v_a_5030_,
                            v_a_5031_,
                            v_a_5032_,
                            v_a_5033_,
                        );
                    return v___x_5047_;
                } else {
                    v_val_5048_ = crate::leanh::lean_ctor_get(v_fst_5045_, 0);
                    crate::leanh::lean_inc(v_val_5048_);
                    crate::leanh::lean_dec_ref_known(v_fst_5045_, 1);
                    if v_isShared_5044_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5043_, 0, v_val_5048_);
                        v___x_5050_ = v___x_5043_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_val_5048_);
                        v___x_5050_ = v_reuseFailAlloc_5051_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5050_;
            }
            3 => {
                if v_isShared_5056_ == 0 {
                    v___x_5058_ = v___x_5055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
                    v___x_5058_ = v_reuseFailAlloc_5059_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5058_;
            }
            5 => {
                if v_isShared_5064_ == 0 {
                    v___x_5066_ = v___x_5063_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
                    v___x_5066_ = v_reuseFailAlloc_5067_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst___redArg___boxed(
    mut v_jobs_5069_: *mut crate::leanh::LeanObject,
    mut v_cancel_5070_: *mut crate::leanh::LeanObject,
    mut v_a_5071_: *mut crate::leanh::LeanObject,
    mut v_a_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
    mut v_a_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_5076_: u8 = 0;
    let mut v_res_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5076_ = (crate::leanh::lean_unbox(v_cancel_5070_) as u8);
    v_res_5077_ = l_Lean_Meta_MetaM_parFirst___redArg(
        v_jobs_5069_,
        v_cancel_boxed_5076_,
        v_a_5071_,
        v_a_5072_,
        v_a_5073_,
        v_a_5074_,
    );
    crate::leanh::lean_dec(v_a_5074_);
    crate::leanh::lean_dec_ref(v_a_5073_);
    crate::leanh::lean_dec(v_a_5072_);
    crate::leanh::lean_dec_ref(v_a_5071_);
    return v_res_5077_;
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst(
    mut v_00_u03b1_5078_: *mut crate::leanh::LeanObject,
    mut v_jobs_5079_: *mut crate::leanh::LeanObject,
    mut v_cancel_5080_: u8,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_Meta_MetaM_parFirst___redArg(
        v_jobs_5079_,
        v_cancel_5080_,
        v_a_5081_,
        v_a_5082_,
        v_a_5083_,
        v_a_5084_,
    );
    return v___x_5086_;
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst___boxed(
    mut v_00_u03b1_5087_: *mut crate::leanh::LeanObject,
    mut v_jobs_5088_: *mut crate::leanh::LeanObject,
    mut v_cancel_5089_: *mut crate::leanh::LeanObject,
    mut v_a_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
    mut v_a_5093_: *mut crate::leanh::LeanObject,
    mut v_a_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_5095_: u8 = 0;
    let mut v_res_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5095_ = (crate::leanh::lean_unbox(v_cancel_5089_) as u8);
    v_res_5096_ = l_Lean_Meta_MetaM_parFirst(
        v_00_u03b1_5087_,
        v_jobs_5088_,
        v_cancel_boxed_5095_,
        v_a_5090_,
        v_a_5091_,
        v_a_5092_,
        v_a_5093_,
    );
    crate::leanh::lean_dec(v_a_5093_);
    crate::leanh::lean_dec_ref(v_a_5092_);
    crate::leanh::lean_dec(v_a_5091_);
    crate::leanh::lean_dec_ref(v_a_5090_);
    return v_res_5096_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(
    mut v_00_u03b1_5097_: *mut crate::leanh::LeanObject,
    mut v_cancel_5098_: u8,
    mut v_fst_5099_: *mut crate::leanh::LeanObject,
    mut v_inst_5100_: *mut crate::leanh::LeanObject,
    mut v_R_5101_: *mut crate::leanh::LeanObject,
    mut v_a_5102_: *mut crate::leanh::LeanObject,
    mut v_b_5103_: *mut crate::leanh::LeanObject,
    mut v_c_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(
        v_cancel_5098_,
        v_fst_5099_,
        v_a_5102_,
        v_b_5103_,
        v___y_5105_,
        v___y_5106_,
        v___y_5107_,
        v___y_5108_,
    );
    return v___x_5110_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(
    mut v_00_u03b1_5111_: *mut crate::leanh::LeanObject,
    mut v_cancel_5112_: *mut crate::leanh::LeanObject,
    mut v_fst_5113_: *mut crate::leanh::LeanObject,
    mut v_inst_5114_: *mut crate::leanh::LeanObject,
    mut v_R_5115_: *mut crate::leanh::LeanObject,
    mut v_a_5116_: *mut crate::leanh::LeanObject,
    mut v_b_5117_: *mut crate::leanh::LeanObject,
    mut v_c_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_5124_: u8 = 0;
    let mut v_res_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5124_ = (crate::leanh::lean_unbox(v_cancel_5112_) as u8);
    v_res_5125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(
        v_00_u03b1_5111_,
        v_cancel_boxed_5124_,
        v_fst_5113_,
        v_inst_5114_,
        v_R_5115_,
        v_a_5116_,
        v_b_5117_,
        v_c_5118_,
        v___y_5119_,
        v___y_5120_,
        v___y_5121_,
        v___y_5122_,
    );
    crate::leanh::lean_dec(v___y_5122_);
    crate::leanh::lean_dec_ref(v___y_5121_);
    crate::leanh::lean_dec(v___y_5120_);
    crate::leanh::lean_dec_ref(v___y_5119_);
    return v_res_5125_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(
    mut v_00_u03b1_5126_: *mut crate::leanh::LeanObject,
    mut v_msg_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5133_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
        v_msg_5127_,
        v___y_5128_,
        v___y_5129_,
        v___y_5130_,
        v___y_5131_,
    );
    return v___x_5133_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(
    mut v_00_u03b1_5134_: *mut crate::leanh::LeanObject,
    mut v_msg_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5141_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(
        v_00_u03b1_5134_,
        v_msg_5135_,
        v___y_5136_,
        v___y_5137_,
        v___y_5138_,
        v___y_5139_,
    );
    crate::leanh::lean_dec(v___y_5139_);
    crate::leanh::lean_dec_ref(v___y_5138_);
    crate::leanh::lean_dec(v___y_5137_);
    crate::leanh::lean_dec_ref(v___y_5136_);
    return v_res_5141_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(
    mut v_x_5142_: *mut crate::leanh::LeanObject,
    mut v_x_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5157_: u8 = 0;
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5142_) == 0 {
                    v___x_5151_ = l_List_reverse___redArg(v_x_5143_);
                    v___x_5152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
                    return v___x_5152_;
                } else {
                    v_head_5153_ = crate::leanh::lean_ctor_get(v_x_5142_, 0);
                    v_tail_5154_ = crate::leanh::lean_ctor_get(v_x_5142_, 1);
                    v_isSharedCheck_5172_ = (!crate::leanh::lean_is_exclusive(v_x_5142_)) as u8;
                    if v_isSharedCheck_5172_ == 0 {
                        v___x_5156_ = v_x_5142_;
                        v_isShared_5157_ = v_isSharedCheck_5172_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5154_);
                        crate::leanh::lean_inc(v_head_5153_);
                        crate::leanh::lean_dec(v_x_5142_);
                        v___x_5156_ = crate::leanh::lean_box(0);
                        v_isShared_5157_ = v_isSharedCheck_5172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5158_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(
                    v_head_5153_,
                    v___y_5144_,
                    v___y_5145_,
                    v___y_5146_,
                    v___y_5147_,
                    v___y_5148_,
                    v___y_5149_,
                );
                if crate::leanh::lean_obj_tag(v___x_5158_) == 0 {
                    v_a_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
                    crate::leanh::lean_inc(v_a_5159_);
                    crate::leanh::lean_dec_ref_known(v___x_5158_, 1);
                    if v_isShared_5157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5156_, 1, v_x_5143_);
                        crate::leanh::lean_ctor_set(v___x_5156_, 0, v_a_5159_);
                        v___x_5161_ = v___x_5156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5159_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_x_5143_);
                        v___x_5161_ = v_reuseFailAlloc_5163_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5156_);
                    crate::leanh::lean_dec(v_tail_5154_);
                    crate::leanh::lean_dec(v_x_5143_);
                    v_a_5164_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
                    v_isSharedCheck_5171_ = (!crate::leanh::lean_is_exclusive(v___x_5158_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5166_ = v___x_5158_;
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5164_);
                        crate::leanh::lean_dec(v___x_5158_);
                        v___x_5166_ = crate::leanh::lean_box(0);
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5142_ = v_tail_5154_;
                v_x_5143_ = v___x_5161_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5167_ == 0 {
                    v___x_5169_ = v___x_5166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
                    v___x_5169_ = v_reuseFailAlloc_5170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(
    mut v_x_5173_: *mut crate::leanh::LeanObject,
    mut v_x_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5182_ =
        l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(
            v_x_5173_,
            v_x_5174_,
            v___y_5175_,
            v___y_5176_,
            v___y_5177_,
            v___y_5178_,
            v___y_5179_,
            v___y_5180_,
        );
    crate::leanh::lean_dec(v___y_5180_);
    crate::leanh::lean_dec_ref(v___y_5179_);
    crate::leanh::lean_dec(v___y_5178_);
    crate::leanh::lean_dec_ref(v___y_5177_);
    crate::leanh::lean_dec(v___y_5176_);
    crate::leanh::lean_dec_ref(v___y_5175_);
    return v_res_5182_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
    mut v_jobs_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
    mut v_a_5186_: *mut crate::leanh::LeanObject,
    mut v_a_5187_: *mut crate::leanh::LeanObject,
    mut v_a_5188_: *mut crate::leanh::LeanObject,
    mut v_a_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5196_: u8 = 0;
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5202_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5210_: u8 = 0;
    let mut v_isSharedCheck_5211_: u8 = 0;
    let mut v_a_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5191_ = crate::leanh::lean_box(0);
                v___x_5192_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_5183_, v___x_5191_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                if crate::leanh::lean_obj_tag(v___x_5192_) == 0 {
                    v_a_5193_ = crate::leanh::lean_ctor_get(v___x_5192_, 0);
                    v_isSharedCheck_5211_ = (!crate::leanh::lean_is_exclusive(v___x_5192_)) as u8;
                    if v_isSharedCheck_5211_ == 0 {
                        v___x_5195_ = v___x_5192_;
                        v_isShared_5196_ = v_isSharedCheck_5211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5193_);
                        crate::leanh::lean_dec(v___x_5192_);
                        v___x_5195_ = crate::leanh::lean_box(0);
                        v_isShared_5196_ = v_isSharedCheck_5211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5212_ = crate::leanh::lean_ctor_get(v___x_5192_, 0);
                    v_isSharedCheck_5219_ = (!crate::leanh::lean_is_exclusive(v___x_5192_)) as u8;
                    if v_isSharedCheck_5219_ == 0 {
                        v___x_5214_ = v___x_5192_;
                        v_isShared_5215_ = v_isSharedCheck_5219_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5212_);
                        crate::leanh::lean_dec(v___x_5192_);
                        v___x_5214_ = crate::leanh::lean_box(0);
                        v_isShared_5215_ = v_isSharedCheck_5219_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5197_ = l_List_unzipTR___redArg(v_a_5193_);
                v_fst_5198_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                v_snd_5199_ = crate::leanh::lean_ctor_get(v___x_5197_, 1);
                v_isSharedCheck_5210_ = (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                if v_isSharedCheck_5210_ == 0 {
                    v___x_5201_ = v___x_5197_;
                    v_isShared_5202_ = v_isSharedCheck_5210_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5199_);
                    crate::leanh::lean_inc(v_fst_5198_);
                    crate::leanh::lean_dec(v___x_5197_);
                    v___x_5201_ = crate::leanh::lean_box(0);
                    v_isShared_5202_ = v_isSharedCheck_5210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5203_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_5203_, 0, v_fst_5198_);
                if v_isShared_5202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5201_, 0, v___x_5203_);
                    v___x_5205_ = v___x_5201_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_snd_5199_);
                    v___x_5205_ = v_reuseFailAlloc_5209_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5195_, 0, v___x_5205_);
                    v___x_5207_ = v___x_5195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5205_);
                    v___x_5207_ = v_reuseFailAlloc_5208_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5207_;
            }
            5 => {
                if v_isShared_5215_ == 0 {
                    v___x_5217_ = v___x_5214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
                    v___x_5217_ = v_reuseFailAlloc_5218_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(
    mut v_jobs_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
    mut v_a_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
        v_jobs_5220_,
        v_a_5221_,
        v_a_5222_,
        v_a_5223_,
        v_a_5224_,
        v_a_5225_,
        v_a_5226_,
    );
    crate::leanh::lean_dec(v_a_5226_);
    crate::leanh::lean_dec_ref(v_a_5225_);
    crate::leanh::lean_dec(v_a_5224_);
    crate::leanh::lean_dec_ref(v_a_5223_);
    crate::leanh::lean_dec(v_a_5222_);
    crate::leanh::lean_dec_ref(v_a_5221_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel(
    mut v_00_u03b1_5229_: *mut crate::leanh::LeanObject,
    mut v_jobs_5230_: *mut crate::leanh::LeanObject,
    mut v_a_5231_: *mut crate::leanh::LeanObject,
    mut v_a_5232_: *mut crate::leanh::LeanObject,
    mut v_a_5233_: *mut crate::leanh::LeanObject,
    mut v_a_5234_: *mut crate::leanh::LeanObject,
    mut v_a_5235_: *mut crate::leanh::LeanObject,
    mut v_a_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5238_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
        v_jobs_5230_,
        v_a_5231_,
        v_a_5232_,
        v_a_5233_,
        v_a_5234_,
        v_a_5235_,
        v_a_5236_,
    );
    return v___x_5238_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(
    mut v_00_u03b1_5239_: *mut crate::leanh::LeanObject,
    mut v_jobs_5240_: *mut crate::leanh::LeanObject,
    mut v_a_5241_: *mut crate::leanh::LeanObject,
    mut v_a_5242_: *mut crate::leanh::LeanObject,
    mut v_a_5243_: *mut crate::leanh::LeanObject,
    mut v_a_5244_: *mut crate::leanh::LeanObject,
    mut v_a_5245_: *mut crate::leanh::LeanObject,
    mut v_a_5246_: *mut crate::leanh::LeanObject,
    mut v_a_5247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(
        v_00_u03b1_5239_,
        v_jobs_5240_,
        v_a_5241_,
        v_a_5242_,
        v_a_5243_,
        v_a_5244_,
        v_a_5245_,
        v_a_5246_,
    );
    crate::leanh::lean_dec(v_a_5246_);
    crate::leanh::lean_dec_ref(v_a_5245_);
    crate::leanh::lean_dec(v_a_5244_);
    crate::leanh::lean_dec_ref(v_a_5243_);
    crate::leanh::lean_dec(v_a_5242_);
    crate::leanh::lean_dec_ref(v_a_5241_);
    return v_res_5248_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(
    mut v_00_u03b1_5249_: *mut crate::leanh::LeanObject,
    mut v_x_5250_: *mut crate::leanh::LeanObject,
    mut v_x_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
    mut v___y_5257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5259_ =
        l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(
            v_x_5250_,
            v_x_5251_,
            v___y_5252_,
            v___y_5253_,
            v___y_5254_,
            v___y_5255_,
            v___y_5256_,
            v___y_5257_,
        );
    return v___x_5259_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(
    mut v_00_u03b1_5260_: *mut crate::leanh::LeanObject,
    mut v_x_5261_: *mut crate::leanh::LeanObject,
    mut v_x_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(
        v_00_u03b1_5260_,
        v_x_5261_,
        v_x_5262_,
        v___y_5263_,
        v___y_5264_,
        v___y_5265_,
        v___y_5266_,
        v___y_5267_,
        v___y_5268_,
    );
    crate::leanh::lean_dec(v___y_5268_);
    crate::leanh::lean_dec_ref(v___y_5267_);
    crate::leanh::lean_dec(v___y_5266_);
    crate::leanh::lean_dec_ref(v___y_5265_);
    crate::leanh::lean_dec(v___y_5264_);
    crate::leanh::lean_dec_ref(v___y_5263_);
    return v_res_5270_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter___redArg(
    mut v_jobs_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
    mut v_a_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v_snd_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_a_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5279_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
                    v_jobs_5271_,
                    v_a_5272_,
                    v_a_5273_,
                    v_a_5274_,
                    v_a_5275_,
                    v_a_5276_,
                    v_a_5277_,
                );
                if crate::leanh::lean_obj_tag(v___x_5279_) == 0 {
                    v_a_5280_ = crate::leanh::lean_ctor_get(v___x_5279_, 0);
                    v_isSharedCheck_5288_ = (!crate::leanh::lean_is_exclusive(v___x_5279_)) as u8;
                    if v_isSharedCheck_5288_ == 0 {
                        v___x_5282_ = v___x_5279_;
                        v_isShared_5283_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5280_);
                        crate::leanh::lean_dec(v___x_5279_);
                        v___x_5282_ = crate::leanh::lean_box(0);
                        v_isShared_5283_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5289_ = crate::leanh::lean_ctor_get(v___x_5279_, 0);
                    v_isSharedCheck_5296_ = (!crate::leanh::lean_is_exclusive(v___x_5279_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5291_ = v___x_5279_;
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5289_);
                        crate::leanh::lean_dec(v___x_5279_);
                        v___x_5291_ = crate::leanh::lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5284_ = crate::leanh::lean_ctor_get(v_a_5280_, 1);
                crate::leanh::lean_inc(v_snd_5284_);
                crate::leanh::lean_dec(v_a_5280_);
                if v_isShared_5283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5282_, 0, v_snd_5284_);
                    v___x_5286_ = v___x_5282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_snd_5284_);
                    v___x_5286_ = v_reuseFailAlloc_5287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5286_;
            }
            3 => {
                if v_isShared_5292_ == 0 {
                    v___x_5294_ = v___x_5291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
                    v___x_5294_ = v_reuseFailAlloc_5295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(
    mut v_jobs_5297_: *mut crate::leanh::LeanObject,
    mut v_a_5298_: *mut crate::leanh::LeanObject,
    mut v_a_5299_: *mut crate::leanh::LeanObject,
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5305_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(
        v_jobs_5297_,
        v_a_5298_,
        v_a_5299_,
        v_a_5300_,
        v_a_5301_,
        v_a_5302_,
        v_a_5303_,
    );
    crate::leanh::lean_dec(v_a_5303_);
    crate::leanh::lean_dec_ref(v_a_5302_);
    crate::leanh::lean_dec(v_a_5301_);
    crate::leanh::lean_dec_ref(v_a_5300_);
    crate::leanh::lean_dec(v_a_5299_);
    crate::leanh::lean_dec_ref(v_a_5298_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter(
    mut v_00_u03b1_5306_: *mut crate::leanh::LeanObject,
    mut v_jobs_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_a_5311_: *mut crate::leanh::LeanObject,
    mut v_a_5312_: *mut crate::leanh::LeanObject,
    mut v_a_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5315_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(
        v_jobs_5307_,
        v_a_5308_,
        v_a_5309_,
        v_a_5310_,
        v_a_5311_,
        v_a_5312_,
        v_a_5313_,
    );
    return v___x_5315_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter___boxed(
    mut v_00_u03b1_5316_: *mut crate::leanh::LeanObject,
    mut v_jobs_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
    mut v_a_5322_: *mut crate::leanh::LeanObject,
    mut v_a_5323_: *mut crate::leanh::LeanObject,
    mut v_a_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5325_ = l_Lean_Elab_Term_TermElabM_parIter(
        v_00_u03b1_5316_,
        v_jobs_5317_,
        v_a_5318_,
        v_a_5319_,
        v_a_5320_,
        v_a_5321_,
        v_a_5322_,
        v_a_5323_,
    );
    crate::leanh::lean_dec(v_a_5323_);
    crate::leanh::lean_dec_ref(v_a_5322_);
    crate::leanh::lean_dec(v_a_5321_);
    crate::leanh::lean_dec_ref(v_a_5320_);
    crate::leanh::lean_dec(v_a_5319_);
    crate::leanh::lean_dec_ref(v_a_5318_);
    return v_res_5325_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
    mut v_jobs_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
    mut v_a_5331_: *mut crate::leanh::LeanObject,
    mut v_a_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5353_: u8 = 0;
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5334_ = crate::leanh::lean_box(0);
                v___x_5335_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_5326_, v___x_5334_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
                if crate::leanh::lean_obj_tag(v___x_5335_) == 0 {
                    v_a_5336_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
                    v_isSharedCheck_5354_ = (!crate::leanh::lean_is_exclusive(v___x_5335_)) as u8;
                    if v_isSharedCheck_5354_ == 0 {
                        v___x_5338_ = v___x_5335_;
                        v_isShared_5339_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5336_);
                        crate::leanh::lean_dec(v___x_5335_);
                        v___x_5338_ = crate::leanh::lean_box(0);
                        v_isShared_5339_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
                    v_isSharedCheck_5362_ = (!crate::leanh::lean_is_exclusive(v___x_5335_)) as u8;
                    if v_isSharedCheck_5362_ == 0 {
                        v___x_5357_ = v___x_5335_;
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5355_);
                        crate::leanh::lean_dec(v___x_5335_);
                        v___x_5357_ = crate::leanh::lean_box(0);
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5340_ = l_List_unzipTR___redArg(v_a_5336_);
                v_fst_5341_ = crate::leanh::lean_ctor_get(v___x_5340_, 0);
                v_snd_5342_ = crate::leanh::lean_ctor_get(v___x_5340_, 1);
                v_isSharedCheck_5353_ = (!crate::leanh::lean_is_exclusive(v___x_5340_)) as u8;
                if v_isSharedCheck_5353_ == 0 {
                    v___x_5344_ = v___x_5340_;
                    v_isShared_5345_ = v_isSharedCheck_5353_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5342_);
                    crate::leanh::lean_inc(v_fst_5341_);
                    crate::leanh::lean_dec(v___x_5340_);
                    v___x_5344_ = crate::leanh::lean_box(0);
                    v_isShared_5345_ = v_isSharedCheck_5353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5346_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_5346_, 0, v_fst_5341_);
                if v_isShared_5345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5344_, 0, v___x_5346_);
                    v___x_5348_ = v___x_5344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_snd_5342_);
                    v___x_5348_ = v_reuseFailAlloc_5352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5338_, 0, v___x_5348_);
                    v___x_5350_ = v___x_5338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
                    v___x_5350_ = v_reuseFailAlloc_5351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5350_;
            }
            5 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(
    mut v_jobs_5363_: *mut crate::leanh::LeanObject,
    mut v_a_5364_: *mut crate::leanh::LeanObject,
    mut v_a_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
        v_jobs_5363_,
        v_a_5364_,
        v_a_5365_,
        v_a_5366_,
        v_a_5367_,
        v_a_5368_,
        v_a_5369_,
    );
    crate::leanh::lean_dec(v_a_5369_);
    crate::leanh::lean_dec_ref(v_a_5368_);
    crate::leanh::lean_dec(v_a_5367_);
    crate::leanh::lean_dec_ref(v_a_5366_);
    crate::leanh::lean_dec(v_a_5365_);
    crate::leanh::lean_dec_ref(v_a_5364_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(
    mut v_00_u03b1_5372_: *mut crate::leanh::LeanObject,
    mut v_jobs_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
    mut v_a_5376_: *mut crate::leanh::LeanObject,
    mut v_a_5377_: *mut crate::leanh::LeanObject,
    mut v_a_5378_: *mut crate::leanh::LeanObject,
    mut v_a_5379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5381_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
        v_jobs_5373_,
        v_a_5374_,
        v_a_5375_,
        v_a_5376_,
        v_a_5377_,
        v_a_5378_,
        v_a_5379_,
    );
    return v___x_5381_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(
    mut v_00_u03b1_5382_: *mut crate::leanh::LeanObject,
    mut v_jobs_5383_: *mut crate::leanh::LeanObject,
    mut v_a_5384_: *mut crate::leanh::LeanObject,
    mut v_a_5385_: *mut crate::leanh::LeanObject,
    mut v_a_5386_: *mut crate::leanh::LeanObject,
    mut v_a_5387_: *mut crate::leanh::LeanObject,
    mut v_a_5388_: *mut crate::leanh::LeanObject,
    mut v_a_5389_: *mut crate::leanh::LeanObject,
    mut v_a_5390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5391_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(
        v_00_u03b1_5382_,
        v_jobs_5383_,
        v_a_5384_,
        v_a_5385_,
        v_a_5386_,
        v_a_5387_,
        v_a_5388_,
        v_a_5389_,
    );
    crate::leanh::lean_dec(v_a_5389_);
    crate::leanh::lean_dec_ref(v_a_5388_);
    crate::leanh::lean_dec(v_a_5387_);
    crate::leanh::lean_dec_ref(v_a_5386_);
    crate::leanh::lean_dec(v_a_5385_);
    crate::leanh::lean_dec_ref(v_a_5384_);
    return v_res_5391_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(
    mut v_jobs_5392_: *mut crate::leanh::LeanObject,
    mut v_a_5393_: *mut crate::leanh::LeanObject,
    mut v_a_5394_: *mut crate::leanh::LeanObject,
    mut v_a_5395_: *mut crate::leanh::LeanObject,
    mut v_a_5396_: *mut crate::leanh::LeanObject,
    mut v_a_5397_: *mut crate::leanh::LeanObject,
    mut v_a_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_snd_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v_a_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5400_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
                    v_jobs_5392_,
                    v_a_5393_,
                    v_a_5394_,
                    v_a_5395_,
                    v_a_5396_,
                    v_a_5397_,
                    v_a_5398_,
                );
                if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                    v_a_5401_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5409_ = (!crate::leanh::lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v___x_5403_ = v___x_5400_;
                        v_isShared_5404_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5401_);
                        crate::leanh::lean_dec(v___x_5400_);
                        v___x_5403_ = crate::leanh::lean_box(0);
                        v_isShared_5404_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5410_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5417_ = (!crate::leanh::lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5412_ = v___x_5400_;
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5410_);
                        crate::leanh::lean_dec(v___x_5400_);
                        v___x_5412_ = crate::leanh::lean_box(0);
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5405_ = crate::leanh::lean_ctor_get(v_a_5401_, 1);
                crate::leanh::lean_inc(v_snd_5405_);
                crate::leanh::lean_dec(v_a_5401_);
                if v_isShared_5404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5403_, 0, v_snd_5405_);
                    v___x_5407_ = v___x_5403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_snd_5405_);
                    v___x_5407_ = v_reuseFailAlloc_5408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5407_;
            }
            3 => {
                if v_isShared_5413_ == 0 {
                    v___x_5415_ = v___x_5412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
                    v___x_5415_ = v_reuseFailAlloc_5416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(
    mut v_jobs_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v_a_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
    mut v_a_5422_: *mut crate::leanh::LeanObject,
    mut v_a_5423_: *mut crate::leanh::LeanObject,
    mut v_a_5424_: *mut crate::leanh::LeanObject,
    mut v_a_5425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5426_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(
        v_jobs_5418_,
        v_a_5419_,
        v_a_5420_,
        v_a_5421_,
        v_a_5422_,
        v_a_5423_,
        v_a_5424_,
    );
    crate::leanh::lean_dec(v_a_5424_);
    crate::leanh::lean_dec_ref(v_a_5423_);
    crate::leanh::lean_dec(v_a_5422_);
    crate::leanh::lean_dec_ref(v_a_5421_);
    crate::leanh::lean_dec(v_a_5420_);
    crate::leanh::lean_dec_ref(v_a_5419_);
    return v_res_5426_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy(
    mut v_00_u03b1_5427_: *mut crate::leanh::LeanObject,
    mut v_jobs_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: *mut crate::leanh::LeanObject,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
    mut v_a_5433_: *mut crate::leanh::LeanObject,
    mut v_a_5434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5436_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(
        v_jobs_5428_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
        v_a_5433_,
        v_a_5434_,
    );
    return v___x_5436_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(
    mut v_00_u03b1_5437_: *mut crate::leanh::LeanObject,
    mut v_jobs_5438_: *mut crate::leanh::LeanObject,
    mut v_a_5439_: *mut crate::leanh::LeanObject,
    mut v_a_5440_: *mut crate::leanh::LeanObject,
    mut v_a_5441_: *mut crate::leanh::LeanObject,
    mut v_a_5442_: *mut crate::leanh::LeanObject,
    mut v_a_5443_: *mut crate::leanh::LeanObject,
    mut v_a_5444_: *mut crate::leanh::LeanObject,
    mut v_a_5445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5446_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(
        v_00_u03b1_5437_,
        v_jobs_5438_,
        v_a_5439_,
        v_a_5440_,
        v_a_5441_,
        v_a_5442_,
        v_a_5443_,
        v_a_5444_,
    );
    crate::leanh::lean_dec(v_a_5444_);
    crate::leanh::lean_dec_ref(v_a_5443_);
    crate::leanh::lean_dec(v_a_5442_);
    crate::leanh::lean_dec_ref(v_a_5441_);
    crate::leanh::lean_dec(v_a_5440_);
    crate::leanh::lean_dec_ref(v_a_5439_);
    return v_res_5446_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
    mut v_x_5447_: *mut crate::leanh::LeanObject,
    mut v_x_5448_: *mut crate::leanh::LeanObject,
    mut v___y_5449_: *mut crate::leanh::LeanObject,
    mut v___y_5450_: *mut crate::leanh::LeanObject,
    mut v___y_5451_: *mut crate::leanh::LeanObject,
    mut v___y_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
    mut v___y_5454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5462_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5447_) == 0 {
                    v___x_5456_ = l_List_reverse___redArg(v_x_5448_);
                    v___x_5457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5457_, 0, v___x_5456_);
                    return v___x_5457_;
                } else {
                    v_head_5458_ = crate::leanh::lean_ctor_get(v_x_5447_, 0);
                    v_tail_5459_ = crate::leanh::lean_ctor_get(v_x_5447_, 1);
                    v_isSharedCheck_5477_ = (!crate::leanh::lean_is_exclusive(v_x_5447_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5461_ = v_x_5447_;
                        v_isShared_5462_ = v_isSharedCheck_5477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5459_);
                        crate::leanh::lean_inc(v_head_5458_);
                        crate::leanh::lean_dec(v_x_5447_);
                        v___x_5461_ = crate::leanh::lean_box(0);
                        v_isShared_5462_ = v_isSharedCheck_5477_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5463_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(
                    v_head_5458_,
                    v___y_5449_,
                    v___y_5450_,
                    v___y_5451_,
                    v___y_5452_,
                    v___y_5453_,
                    v___y_5454_,
                );
                if crate::leanh::lean_obj_tag(v___x_5463_) == 0 {
                    v_a_5464_ = crate::leanh::lean_ctor_get(v___x_5463_, 0);
                    crate::leanh::lean_inc(v_a_5464_);
                    crate::leanh::lean_dec_ref_known(v___x_5463_, 1);
                    if v_isShared_5462_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5461_, 1, v_x_5448_);
                        crate::leanh::lean_ctor_set(v___x_5461_, 0, v_a_5464_);
                        v___x_5466_ = v___x_5461_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5468_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5464_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_x_5448_);
                        v___x_5466_ = v_reuseFailAlloc_5468_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5461_);
                    crate::leanh::lean_dec(v_tail_5459_);
                    crate::leanh::lean_dec(v_x_5448_);
                    v_a_5469_ = crate::leanh::lean_ctor_get(v___x_5463_, 0);
                    v_isSharedCheck_5476_ = (!crate::leanh::lean_is_exclusive(v___x_5463_)) as u8;
                    if v_isSharedCheck_5476_ == 0 {
                        v___x_5471_ = v___x_5463_;
                        v_isShared_5472_ = v_isSharedCheck_5476_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5469_);
                        crate::leanh::lean_dec(v___x_5463_);
                        v___x_5471_ = crate::leanh::lean_box(0);
                        v_isShared_5472_ = v_isSharedCheck_5476_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5447_ = v_tail_5459_;
                v_x_5448_ = v___x_5466_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5472_ == 0 {
                    v___x_5474_ = v___x_5471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
                    v___x_5474_ = v_reuseFailAlloc_5475_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(
    mut v_x_5478_: *mut crate::leanh::LeanObject,
    mut v_x_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5487_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
        v_x_5478_,
        v_x_5479_,
        v___y_5480_,
        v___y_5481_,
        v___y_5482_,
        v___y_5483_,
        v___y_5484_,
        v___y_5485_,
    );
    crate::leanh::lean_dec(v___y_5485_);
    crate::leanh::lean_dec_ref(v___y_5484_);
    crate::leanh::lean_dec(v___y_5483_);
    crate::leanh::lean_dec_ref(v___y_5482_);
    crate::leanh::lean_dec(v___y_5481_);
    crate::leanh::lean_dec_ref(v___y_5480_);
    return v_res_5487_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(
    mut v_as_x27_5488_: *mut crate::leanh::LeanObject,
    mut v_b_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5502_: u8 = 0;
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: u8 = 0;
    let mut v___x_2960__overap_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut v_a_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5488_) == 0 {
                    v___x_5497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5497_, 0, v_b_5489_);
                    return v___x_5497_;
                } else {
                    v_head_5498_ = crate::leanh::lean_ctor_get(v_as_x27_5488_, 0);
                    v_tail_5499_ = crate::leanh::lean_ctor_get(v_as_x27_5488_, 1);
                    crate::leanh::lean_inc(v_head_5498_);
                    v___x_2960__overap_5511_ = lean_task_get_own(v_head_5498_);
                    crate::leanh::lean_inc(v___y_5495_);
                    crate::leanh::lean_inc_ref(v___y_5494_);
                    crate::leanh::lean_inc(v___y_5493_);
                    crate::leanh::lean_inc_ref(v___y_5492_);
                    crate::leanh::lean_inc(v___y_5491_);
                    crate::leanh::lean_inc_ref(v___y_5490_);
                    v___x_5512_ = crate::leanh::lean_apply_7(
                        v___x_2960__overap_5511_,
                        v___y_5490_,
                        v___y_5491_,
                        v___y_5492_,
                        v___y_5493_,
                        v___y_5494_,
                        v___y_5495_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5512_) == 0 {
                        v_a_5513_ = crate::leanh::lean_ctor_get(v___x_5512_, 0);
                        crate::leanh::lean_inc(v_a_5513_);
                        crate::leanh::lean_dec_ref_known(v___x_5512_, 1);
                        v___x_5514_ = l_Lean_Elab_Term_saveState___redArg(
                            v___y_5491_,
                            v___y_5493_,
                            v___y_5495_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                            v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                            v_isSharedCheck_5525_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5514_)) as u8;
                            if v_isSharedCheck_5525_ == 0 {
                                v___x_5517_ = v___x_5514_;
                                v_isShared_5518_ = v_isSharedCheck_5525_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5515_);
                                crate::leanh::lean_dec(v___x_5514_);
                                v___x_5517_ = crate::leanh::lean_box(0);
                                v_isShared_5518_ = v_isSharedCheck_5525_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5513_);
                            v_a_5526_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                            crate::leanh::lean_inc(v_a_5526_);
                            crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                            v_a_5508_ = v_a_5526_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5527_ = crate::leanh::lean_ctor_get(v___x_5512_, 0);
                        crate::leanh::lean_inc(v_a_5527_);
                        crate::leanh::lean_dec_ref_known(v___x_5512_, 1);
                        v_a_5508_ = v_a_5527_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5502_ == 0 {
                    v___x_5503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5503_, 0, v___y_5501_);
                    v___x_5504_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5504_, 0, v___x_5503_);
                    crate::leanh::lean_ctor_set(v___x_5504_, 1, v_b_5489_);
                    v_as_x27_5488_ = v_tail_5499_;
                    v_b_5489_ = v___x_5504_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_5489_);
                    v___x_5506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5506_, 0, v___y_5501_);
                    return v___x_5506_;
                }
            }
            2 => {
                v___x_5509_ = l_Lean_Exception_isInterrupt(v_a_5508_);
                if v___x_5509_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_5508_);
                    v___x_5510_ = l_Lean_Exception_isRuntime(v_a_5508_);
                    v___y_5501_ = v_a_5508_;
                    v___y_5502_ = v___x_5510_;
                    state = 1;
                    continue;
                } else {
                    v___y_5501_ = v_a_5508_;
                    v___y_5502_ = v___x_5509_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5519_, 0, v_a_5513_);
                crate::leanh::lean_ctor_set(v___x_5519_, 1, v_a_5515_);
                if v_isShared_5518_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5517_, 1);
                    crate::leanh::lean_ctor_set(v___x_5517_, 0, v___x_5519_);
                    v___x_5521_ = v___x_5517_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5519_);
                    v___x_5521_ = v_reuseFailAlloc_5524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5522_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                crate::leanh::lean_ctor_set(v___x_5522_, 1, v_b_5489_);
                v_as_x27_5488_ = v_tail_5499_;
                v_b_5489_ = v___x_5522_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(
    mut v_as_x27_5528_: *mut crate::leanh::LeanObject,
    mut v_b_5529_: *mut crate::leanh::LeanObject,
    mut v___y_5530_: *mut crate::leanh::LeanObject,
    mut v___y_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
    mut v___y_5536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5537_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(
        v_as_x27_5528_,
        v_b_5529_,
        v___y_5530_,
        v___y_5531_,
        v___y_5532_,
        v___y_5533_,
        v___y_5534_,
        v___y_5535_,
    );
    crate::leanh::lean_dec(v___y_5535_);
    crate::leanh::lean_dec_ref(v___y_5534_);
    crate::leanh::lean_dec(v___y_5533_);
    crate::leanh::lean_dec_ref(v___y_5532_);
    crate::leanh::lean_dec(v___y_5531_);
    crate::leanh::lean_dec_ref(v___y_5530_);
    crate::leanh::lean_dec(v_as_x27_5528_);
    return v_res_5537_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par___redArg(
    mut v_jobs_5538_: *mut crate::leanh::LeanObject,
    mut v_a_5539_: *mut crate::leanh::LeanObject,
    mut v_a_5540_: *mut crate::leanh::LeanObject,
    mut v_a_5541_: *mut crate::leanh::LeanObject,
    mut v_a_5542_: *mut crate::leanh::LeanObject,
    mut v_a_5543_: *mut crate::leanh::LeanObject,
    mut v_a_5544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5546_ = lean_st_ref_get(v_a_5540_);
                v___x_5547_ = crate::leanh::lean_box(0);
                v___x_5548_ =
                    l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
                        v_jobs_5538_,
                        v___x_5547_,
                        v_a_5539_,
                        v_a_5540_,
                        v_a_5541_,
                        v_a_5542_,
                        v_a_5543_,
                        v_a_5544_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5548_) == 0 {
                    v_a_5549_ = crate::leanh::lean_ctor_get(v___x_5548_, 0);
                    crate::leanh::lean_inc(v_a_5549_);
                    crate::leanh::lean_dec_ref_known(v___x_5548_, 1);
                    v___x_5550_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_5549_, v___x_5547_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
                    crate::leanh::lean_dec(v_a_5549_);
                    if crate::leanh::lean_obj_tag(v___x_5550_) == 0 {
                        v_a_5551_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                        v_isSharedCheck_5560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5550_)) as u8;
                        if v_isSharedCheck_5560_ == 0 {
                            v___x_5553_ = v___x_5550_;
                            v_isShared_5554_ = v_isSharedCheck_5560_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5551_);
                            crate::leanh::lean_dec(v___x_5550_);
                            v___x_5553_ = crate::leanh::lean_box(0);
                            v_isShared_5554_ = v_isSharedCheck_5560_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5546_);
                        return v___x_5550_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5546_);
                    v_a_5561_ = crate::leanh::lean_ctor_get(v___x_5548_, 0);
                    v_isSharedCheck_5568_ = (!crate::leanh::lean_is_exclusive(v___x_5548_)) as u8;
                    if v_isSharedCheck_5568_ == 0 {
                        v___x_5563_ = v___x_5548_;
                        v_isShared_5564_ = v_isSharedCheck_5568_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5561_);
                        crate::leanh::lean_dec(v___x_5548_);
                        v___x_5563_ = crate::leanh::lean_box(0);
                        v_isShared_5564_ = v_isSharedCheck_5568_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5555_ = lean_st_ref_set(v_a_5540_, v___x_5546_);
                v___x_5556_ = l_List_reverse___redArg(v_a_5551_);
                if v_isShared_5554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5553_, 0, v___x_5556_);
                    v___x_5558_ = v___x_5553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
                    v___x_5558_ = v_reuseFailAlloc_5559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5558_;
            }
            3 => {
                if v_isShared_5564_ == 0 {
                    v___x_5566_ = v___x_5563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
                    v___x_5566_ = v_reuseFailAlloc_5567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par___redArg___boxed(
    mut v_jobs_5569_: *mut crate::leanh::LeanObject,
    mut v_a_5570_: *mut crate::leanh::LeanObject,
    mut v_a_5571_: *mut crate::leanh::LeanObject,
    mut v_a_5572_: *mut crate::leanh::LeanObject,
    mut v_a_5573_: *mut crate::leanh::LeanObject,
    mut v_a_5574_: *mut crate::leanh::LeanObject,
    mut v_a_5575_: *mut crate::leanh::LeanObject,
    mut v_a_5576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_Lean_Elab_Term_TermElabM_par___redArg(
        v_jobs_5569_,
        v_a_5570_,
        v_a_5571_,
        v_a_5572_,
        v_a_5573_,
        v_a_5574_,
        v_a_5575_,
    );
    crate::leanh::lean_dec(v_a_5575_);
    crate::leanh::lean_dec_ref(v_a_5574_);
    crate::leanh::lean_dec(v_a_5573_);
    crate::leanh::lean_dec_ref(v_a_5572_);
    crate::leanh::lean_dec(v_a_5571_);
    crate::leanh::lean_dec_ref(v_a_5570_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par(
    mut v_00_u03b1_5578_: *mut crate::leanh::LeanObject,
    mut v_jobs_5579_: *mut crate::leanh::LeanObject,
    mut v_a_5580_: *mut crate::leanh::LeanObject,
    mut v_a_5581_: *mut crate::leanh::LeanObject,
    mut v_a_5582_: *mut crate::leanh::LeanObject,
    mut v_a_5583_: *mut crate::leanh::LeanObject,
    mut v_a_5584_: *mut crate::leanh::LeanObject,
    mut v_a_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5587_ = l_Lean_Elab_Term_TermElabM_par___redArg(
        v_jobs_5579_,
        v_a_5580_,
        v_a_5581_,
        v_a_5582_,
        v_a_5583_,
        v_a_5584_,
        v_a_5585_,
    );
    return v___x_5587_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par___boxed(
    mut v_00_u03b1_5588_: *mut crate::leanh::LeanObject,
    mut v_jobs_5589_: *mut crate::leanh::LeanObject,
    mut v_a_5590_: *mut crate::leanh::LeanObject,
    mut v_a_5591_: *mut crate::leanh::LeanObject,
    mut v_a_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
    mut v_a_5594_: *mut crate::leanh::LeanObject,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l_Lean_Elab_Term_TermElabM_par(
        v_00_u03b1_5588_,
        v_jobs_5589_,
        v_a_5590_,
        v_a_5591_,
        v_a_5592_,
        v_a_5593_,
        v_a_5594_,
        v_a_5595_,
    );
    crate::leanh::lean_dec(v_a_5595_);
    crate::leanh::lean_dec_ref(v_a_5594_);
    crate::leanh::lean_dec(v_a_5593_);
    crate::leanh::lean_dec_ref(v_a_5592_);
    crate::leanh::lean_dec(v_a_5591_);
    crate::leanh::lean_dec_ref(v_a_5590_);
    return v_res_5597_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(
    mut v_00_u03b1_5598_: *mut crate::leanh::LeanObject,
    mut v_x_5599_: *mut crate::leanh::LeanObject,
    mut v_x_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5608_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
        v_x_5599_,
        v_x_5600_,
        v___y_5601_,
        v___y_5602_,
        v___y_5603_,
        v___y_5604_,
        v___y_5605_,
        v___y_5606_,
    );
    return v___x_5608_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(
    mut v_00_u03b1_5609_: *mut crate::leanh::LeanObject,
    mut v_x_5610_: *mut crate::leanh::LeanObject,
    mut v_x_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5619_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(
        v_00_u03b1_5609_,
        v_x_5610_,
        v_x_5611_,
        v___y_5612_,
        v___y_5613_,
        v___y_5614_,
        v___y_5615_,
        v___y_5616_,
        v___y_5617_,
    );
    crate::leanh::lean_dec(v___y_5617_);
    crate::leanh::lean_dec_ref(v___y_5616_);
    crate::leanh::lean_dec(v___y_5615_);
    crate::leanh::lean_dec_ref(v___y_5614_);
    crate::leanh::lean_dec(v___y_5613_);
    crate::leanh::lean_dec_ref(v___y_5612_);
    return v_res_5619_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(
    mut v_00_u03b1_5620_: *mut crate::leanh::LeanObject,
    mut v_as_5621_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5622_: *mut crate::leanh::LeanObject,
    mut v_b_5623_: *mut crate::leanh::LeanObject,
    mut v_a_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5632_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(
        v_as_x27_5622_,
        v_b_5623_,
        v___y_5625_,
        v___y_5626_,
        v___y_5627_,
        v___y_5628_,
        v___y_5629_,
        v___y_5630_,
    );
    return v___x_5632_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(
    mut v_00_u03b1_5633_: *mut crate::leanh::LeanObject,
    mut v_as_5634_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5635_: *mut crate::leanh::LeanObject,
    mut v_b_5636_: *mut crate::leanh::LeanObject,
    mut v_a_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5645_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(
        v_00_u03b1_5633_,
        v_as_5634_,
        v_as_x27_5635_,
        v_b_5636_,
        v_a_5637_,
        v___y_5638_,
        v___y_5639_,
        v___y_5640_,
        v___y_5641_,
        v___y_5642_,
        v___y_5643_,
    );
    crate::leanh::lean_dec(v___y_5643_);
    crate::leanh::lean_dec_ref(v___y_5642_);
    crate::leanh::lean_dec(v___y_5641_);
    crate::leanh::lean_dec_ref(v___y_5640_);
    crate::leanh::lean_dec(v___y_5639_);
    crate::leanh::lean_dec_ref(v___y_5638_);
    crate::leanh::lean_dec(v_as_x27_5635_);
    crate::leanh::lean_dec(v_as_5634_);
    return v_res_5645_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(
    mut v_as_x27_5646_: *mut crate::leanh::LeanObject,
    mut v_b_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570__overap_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5667_: u8 = 0;
    let mut v___y_5669_: u8 = 0;
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: u8 = 0;
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5646_) == 0 {
                    v___x_5655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5655_, 0, v_b_5647_);
                    return v___x_5655_;
                } else {
                    v_head_5656_ = crate::leanh::lean_ctor_get(v_as_x27_5646_, 0);
                    v_tail_5657_ = crate::leanh::lean_ctor_get(v_as_x27_5646_, 1);
                    crate::leanh::lean_inc(v_head_5656_);
                    v___x_2570__overap_5658_ = lean_task_get_own(v_head_5656_);
                    crate::leanh::lean_inc(v___y_5653_);
                    crate::leanh::lean_inc_ref(v___y_5652_);
                    crate::leanh::lean_inc(v___y_5651_);
                    crate::leanh::lean_inc_ref(v___y_5650_);
                    crate::leanh::lean_inc(v___y_5649_);
                    crate::leanh::lean_inc_ref(v___y_5648_);
                    v___x_5659_ = crate::leanh::lean_apply_7(
                        v___x_2570__overap_5658_,
                        v___y_5648_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                        v___y_5653_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5659_) == 0 {
                        v_a_5660_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                        crate::leanh::lean_inc(v_a_5660_);
                        crate::leanh::lean_dec_ref_known(v___x_5659_, 1);
                        v___x_5661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5661_, 0, v_a_5660_);
                        v___x_5662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5662_, 0, v___x_5661_);
                        crate::leanh::lean_ctor_set(v___x_5662_, 1, v_b_5647_);
                        v_as_x27_5646_ = v_tail_5657_;
                        v_b_5647_ = v___x_5662_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5664_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                        v_isSharedCheck_5678_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5659_)) as u8;
                        if v_isSharedCheck_5678_ == 0 {
                            v___x_5666_ = v___x_5659_;
                            v_isShared_5667_ = v_isSharedCheck_5678_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5664_);
                            crate::leanh::lean_dec(v___x_5659_);
                            v___x_5666_ = crate::leanh::lean_box(0);
                            v_isShared_5667_ = v_isSharedCheck_5678_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5676_ = l_Lean_Exception_isInterrupt(v_a_5664_);
                if v___x_5676_ == 0 {
                    crate::leanh::lean_inc(v_a_5664_);
                    v___x_5677_ = l_Lean_Exception_isRuntime(v_a_5664_);
                    v___y_5669_ = v___x_5677_;
                    state = 2;
                    continue;
                } else {
                    v___y_5669_ = v___x_5676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5669_ == 0 {
                    crate::leanh::lean_del_object(v___x_5666_);
                    v___x_5670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5670_, 0, v_a_5664_);
                    v___x_5671_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5671_, 0, v___x_5670_);
                    crate::leanh::lean_ctor_set(v___x_5671_, 1, v_b_5647_);
                    v_as_x27_5646_ = v_tail_5657_;
                    v_b_5647_ = v___x_5671_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_5647_);
                    if v_isShared_5667_ == 0 {
                        v___x_5674_ = v___x_5666_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5664_);
                        v___x_5674_ = v_reuseFailAlloc_5675_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(
    mut v_as_x27_5679_: *mut crate::leanh::LeanObject,
    mut v_b_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(
        v_as_x27_5679_,
        v_b_5680_,
        v___y_5681_,
        v___y_5682_,
        v___y_5683_,
        v___y_5684_,
        v___y_5685_,
        v___y_5686_,
    );
    crate::leanh::lean_dec(v___y_5686_);
    crate::leanh::lean_dec_ref(v___y_5685_);
    crate::leanh::lean_dec(v___y_5684_);
    crate::leanh::lean_dec_ref(v___y_5683_);
    crate::leanh::lean_dec(v___y_5682_);
    crate::leanh::lean_dec_ref(v___y_5681_);
    crate::leanh::lean_dec(v_as_x27_5679_);
    return v_res_5688_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27___redArg(
    mut v_jobs_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5705_: u8 = 0;
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5711_: u8 = 0;
    let mut v_a_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5715_: u8 = 0;
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5697_ = lean_st_ref_get(v_a_5691_);
                v___x_5698_ = crate::leanh::lean_box(0);
                v___x_5699_ =
                    l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
                        v_jobs_5689_,
                        v___x_5698_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                        v_a_5694_,
                        v_a_5695_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5699_) == 0 {
                    v_a_5700_ = crate::leanh::lean_ctor_get(v___x_5699_, 0);
                    crate::leanh::lean_inc(v_a_5700_);
                    crate::leanh::lean_dec_ref_known(v___x_5699_, 1);
                    v___x_5701_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_5700_, v___x_5698_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
                    crate::leanh::lean_dec(v_a_5700_);
                    if crate::leanh::lean_obj_tag(v___x_5701_) == 0 {
                        v_a_5702_ = crate::leanh::lean_ctor_get(v___x_5701_, 0);
                        v_isSharedCheck_5711_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5701_)) as u8;
                        if v_isSharedCheck_5711_ == 0 {
                            v___x_5704_ = v___x_5701_;
                            v_isShared_5705_ = v_isSharedCheck_5711_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5702_);
                            crate::leanh::lean_dec(v___x_5701_);
                            v___x_5704_ = crate::leanh::lean_box(0);
                            v_isShared_5705_ = v_isSharedCheck_5711_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5697_);
                        return v___x_5701_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5697_);
                    v_a_5712_ = crate::leanh::lean_ctor_get(v___x_5699_, 0);
                    v_isSharedCheck_5719_ = (!crate::leanh::lean_is_exclusive(v___x_5699_)) as u8;
                    if v_isSharedCheck_5719_ == 0 {
                        v___x_5714_ = v___x_5699_;
                        v_isShared_5715_ = v_isSharedCheck_5719_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5712_);
                        crate::leanh::lean_dec(v___x_5699_);
                        v___x_5714_ = crate::leanh::lean_box(0);
                        v_isShared_5715_ = v_isSharedCheck_5719_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5706_ = lean_st_ref_set(v_a_5691_, v___x_5697_);
                v___x_5707_ = l_List_reverse___redArg(v_a_5702_);
                if v_isShared_5705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5704_, 0, v___x_5707_);
                    v___x_5709_ = v___x_5704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5707_);
                    v___x_5709_ = v_reuseFailAlloc_5710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5709_;
            }
            3 => {
                if v_isShared_5715_ == 0 {
                    v___x_5717_ = v___x_5714_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5712_);
                    v___x_5717_ = v_reuseFailAlloc_5718_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(
    mut v_jobs_5720_: *mut crate::leanh::LeanObject,
    mut v_a_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
    mut v_a_5725_: *mut crate::leanh::LeanObject,
    mut v_a_5726_: *mut crate::leanh::LeanObject,
    mut v_a_5727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5728_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(
        v_jobs_5720_,
        v_a_5721_,
        v_a_5722_,
        v_a_5723_,
        v_a_5724_,
        v_a_5725_,
        v_a_5726_,
    );
    crate::leanh::lean_dec(v_a_5726_);
    crate::leanh::lean_dec_ref(v_a_5725_);
    crate::leanh::lean_dec(v_a_5724_);
    crate::leanh::lean_dec_ref(v_a_5723_);
    crate::leanh::lean_dec(v_a_5722_);
    crate::leanh::lean_dec_ref(v_a_5721_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27(
    mut v_00_u03b1_5729_: *mut crate::leanh::LeanObject,
    mut v_jobs_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
    mut v_a_5733_: *mut crate::leanh::LeanObject,
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5738_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(
        v_jobs_5730_,
        v_a_5731_,
        v_a_5732_,
        v_a_5733_,
        v_a_5734_,
        v_a_5735_,
        v_a_5736_,
    );
    return v___x_5738_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27___boxed(
    mut v_00_u03b1_5739_: *mut crate::leanh::LeanObject,
    mut v_jobs_5740_: *mut crate::leanh::LeanObject,
    mut v_a_5741_: *mut crate::leanh::LeanObject,
    mut v_a_5742_: *mut crate::leanh::LeanObject,
    mut v_a_5743_: *mut crate::leanh::LeanObject,
    mut v_a_5744_: *mut crate::leanh::LeanObject,
    mut v_a_5745_: *mut crate::leanh::LeanObject,
    mut v_a_5746_: *mut crate::leanh::LeanObject,
    mut v_a_5747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_Lean_Elab_Term_TermElabM_par_x27(
        v_00_u03b1_5739_,
        v_jobs_5740_,
        v_a_5741_,
        v_a_5742_,
        v_a_5743_,
        v_a_5744_,
        v_a_5745_,
        v_a_5746_,
    );
    crate::leanh::lean_dec(v_a_5746_);
    crate::leanh::lean_dec_ref(v_a_5745_);
    crate::leanh::lean_dec(v_a_5744_);
    crate::leanh::lean_dec_ref(v_a_5743_);
    crate::leanh::lean_dec(v_a_5742_);
    crate::leanh::lean_dec_ref(v_a_5741_);
    return v_res_5748_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(
    mut v_00_u03b1_5749_: *mut crate::leanh::LeanObject,
    mut v_as_5750_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5751_: *mut crate::leanh::LeanObject,
    mut v_b_5752_: *mut crate::leanh::LeanObject,
    mut v_a_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5761_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(
        v_as_x27_5751_,
        v_b_5752_,
        v___y_5754_,
        v___y_5755_,
        v___y_5756_,
        v___y_5757_,
        v___y_5758_,
        v___y_5759_,
    );
    return v___x_5761_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(
    mut v_00_u03b1_5762_: *mut crate::leanh::LeanObject,
    mut v_as_5763_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5764_: *mut crate::leanh::LeanObject,
    mut v_b_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
    mut v___y_5769_: *mut crate::leanh::LeanObject,
    mut v___y_5770_: *mut crate::leanh::LeanObject,
    mut v___y_5771_: *mut crate::leanh::LeanObject,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5774_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(
        v_00_u03b1_5762_,
        v_as_5763_,
        v_as_x27_5764_,
        v_b_5765_,
        v_a_5766_,
        v___y_5767_,
        v___y_5768_,
        v___y_5769_,
        v___y_5770_,
        v___y_5771_,
        v___y_5772_,
    );
    crate::leanh::lean_dec(v___y_5772_);
    crate::leanh::lean_dec_ref(v___y_5771_);
    crate::leanh::lean_dec(v___y_5770_);
    crate::leanh::lean_dec_ref(v___y_5769_);
    crate::leanh::lean_dec(v___y_5768_);
    crate::leanh::lean_dec_ref(v___y_5767_);
    crate::leanh::lean_dec(v_as_x27_5764_);
    crate::leanh::lean_dec(v_as_5763_);
    return v_res_5774_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5775_ = crate::leanh::lean_box(1);
    v___x_5776_ = l_Lean_MessageData_ofFormat(v___x_5775_);
    return v___x_5776_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5780_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2;
    v___x_5781_ = l_Lean_MessageData_ofFormat(v___x_5780_);
    return v___x_5781_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(
    mut v_x_5782_: *mut crate::leanh::LeanObject,
    mut v_x_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5788_: u8 = 0;
    let mut v_before_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5792_: u8 = 0;
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5805_: u8 = 0;
    let mut v_unused_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5783_) == 0 {
                    return v_x_5782_;
                } else {
                    v_head_5784_ = crate::leanh::lean_ctor_get(v_x_5783_, 0);
                    v_tail_5785_ = crate::leanh::lean_ctor_get(v_x_5783_, 1);
                    v_isSharedCheck_5807_ = (!crate::leanh::lean_is_exclusive(v_x_5783_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5787_ = v_x_5783_;
                        v_isShared_5788_ = v_isSharedCheck_5807_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5785_);
                        crate::leanh::lean_inc(v_head_5784_);
                        crate::leanh::lean_dec(v_x_5783_);
                        v___x_5787_ = crate::leanh::lean_box(0);
                        v_isShared_5788_ = v_isSharedCheck_5807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5789_ = crate::leanh::lean_ctor_get(v_head_5784_, 0);
                v_isSharedCheck_5805_ = (!crate::leanh::lean_is_exclusive(v_head_5784_)) as u8;
                if v_isSharedCheck_5805_ == 0 {
                    v_unused_5806_ = crate::leanh::lean_ctor_get(v_head_5784_, 1);
                    crate::leanh::lean_dec(v_unused_5806_);
                    v___x_5791_ = v_head_5784_;
                    v_isShared_5792_ = v_isSharedCheck_5805_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5789_);
                    crate::leanh::lean_dec(v_head_5784_);
                    v___x_5791_ = crate::leanh::lean_box(0);
                    v_isShared_5792_ = v_isSharedCheck_5805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
                if v_isShared_5792_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5791_, 7);
                    crate::leanh::lean_ctor_set(v___x_5791_, 1, v___x_5793_);
                    crate::leanh::lean_ctor_set(v___x_5791_, 0, v_x_5782_);
                    v___x_5795_ = v___x_5791_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5804_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_x_5782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5804_, 1, v___x_5793_);
                    v___x_5795_ = v_reuseFailAlloc_5804_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
                if v_isShared_5788_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5787_, 7);
                    crate::leanh::lean_ctor_set(v___x_5787_, 1, v___x_5796_);
                    crate::leanh::lean_ctor_set(v___x_5787_, 0, v___x_5795_);
                    v___x_5798_ = v___x_5787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5803_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5796_);
                    v___x_5798_ = v_reuseFailAlloc_5803_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5799_ = l_Lean_MessageData_ofSyntax(v_before_5789_);
                v___x_5800_ = l_Lean_indentD(v___x_5799_);
                v___x_5801_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5801_, 0, v___x_5798_);
                crate::leanh::lean_ctor_set(v___x_5801_, 1, v___x_5800_);
                v_x_5782_ = v___x_5801_;
                v_x_5783_ = v_tail_5785_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(
    mut v_opts_5808_: *mut crate::leanh::LeanObject,
    mut v_opt_5809_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5810_ = crate::leanh::lean_ctor_get(v_opt_5809_, 0);
    v_defValue_5811_ = crate::leanh::lean_ctor_get(v_opt_5809_, 1);
    v_map_5812_ = crate::leanh::lean_ctor_get(v_opts_5808_, 0);
    v___x_5813_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5812_,
            v_name_5810_,
        );
    if crate::leanh::lean_obj_tag(v___x_5813_) == 0 {
        let mut v___x_5814_: u8 = 0;
        v___x_5814_ = (crate::leanh::lean_unbox(v_defValue_5811_) as u8);
        return v___x_5814_;
    } else {
        let mut v_val_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5815_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
        crate::leanh::lean_inc(v_val_5815_);
        crate::leanh::lean_dec_ref_known(v___x_5813_, 1);
        if crate::leanh::lean_obj_tag(v_val_5815_) == 1 {
            let mut v_v_5816_: u8 = 0;
            v_v_5816_ = crate::leanh::lean_ctor_get_uint8(v_val_5815_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5815_, 0);
            return v_v_5816_;
        } else {
            let mut v___x_5817_: u8 = 0;
            crate::leanh::lean_dec(v_val_5815_);
            v___x_5817_ = (crate::leanh::lean_unbox(v_defValue_5811_) as u8);
            return v___x_5817_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(
    mut v_opts_5818_: *mut crate::leanh::LeanObject,
    mut v_opt_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5820_: u8 = 0;
    let mut v_r_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5820_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_5818_, v_opt_5819_);
    crate::leanh::lean_dec_ref(v_opt_5819_);
    crate::leanh::lean_dec_ref(v_opts_5818_);
    v_r_5821_ = crate::leanh::lean_box((v_res_5820_) as usize);
    return v_r_5821_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5825_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1;
    v___x_5826_ = l_Lean_MessageData_ofFormat(v___x_5825_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(
    mut v_msgData_5827_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: u8 = 0;
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_unused_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5831_ = crate::leanh::lean_ctor_get(v___y_5829_, 2);
                v___x_5832_ = l_Lean_Elab_pp_macroStack;
                v___x_5833_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_options_5831_, v___x_5832_);
                if v___x_5833_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5828_);
                    v___x_5834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5834_, 0, v_msgData_5827_);
                    return v___x_5834_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5828_) == 0 {
                        v___x_5835_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5835_, 0, v_msgData_5827_);
                        return v___x_5835_;
                    } else {
                        v_head_5836_ = crate::leanh::lean_ctor_get(v_macroStack_5828_, 0);
                        crate::leanh::lean_inc(v_head_5836_);
                        v_after_5837_ = crate::leanh::lean_ctor_get(v_head_5836_, 1);
                        v_isSharedCheck_5852_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5836_)) as u8;
                        if v_isSharedCheck_5852_ == 0 {
                            v_unused_5853_ = crate::leanh::lean_ctor_get(v_head_5836_, 0);
                            crate::leanh::lean_dec(v_unused_5853_);
                            v___x_5839_ = v_head_5836_;
                            v_isShared_5840_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5837_);
                            crate::leanh::lean_dec(v_head_5836_);
                            v___x_5839_ = crate::leanh::lean_box(0);
                            v_isShared_5840_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
                if v_isShared_5840_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5839_, 7);
                    crate::leanh::lean_ctor_set(v___x_5839_, 1, v___x_5841_);
                    crate::leanh::lean_ctor_set(v___x_5839_, 0, v_msgData_5827_);
                    v___x_5843_ = v___x_5839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_msgData_5827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 1, v___x_5841_);
                    v___x_5843_ = v_reuseFailAlloc_5851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
                v___x_5845_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5845_, 0, v___x_5843_);
                crate::leanh::lean_ctor_set(v___x_5845_, 1, v___x_5844_);
                v___x_5846_ = l_Lean_MessageData_ofSyntax(v_after_5837_);
                v___x_5847_ = l_Lean_indentD(v___x_5846_);
                v_msgData_5848_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5848_, 0, v___x_5845_);
                crate::leanh::lean_ctor_set(v_msgData_5848_, 1, v___x_5847_);
                v___x_5849_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_5848_, v_macroStack_5828_);
                v___x_5850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5850_, 0, v___x_5849_);
                return v___x_5850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(
    mut v_msgData_5854_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_5854_, v_macroStack_5855_, v___y_5856_);
    crate::leanh::lean_dec_ref(v___y_5856_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(
    mut v_msg_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5867_ = crate::leanh::lean_ctor_get(v___y_5864_, 5);
                v___x_5868_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_5859_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
                v_a_5869_ = crate::leanh::lean_ctor_get(v___x_5868_, 0);
                crate::leanh::lean_inc(v_a_5869_);
                crate::leanh::lean_dec_ref(v___x_5868_);
                v_macroStack_5870_ = crate::leanh::lean_ctor_get(v___y_5860_, 1);
                v___x_5871_ = l_Lean_Elab_getBetterRef(v_ref_5867_, v_macroStack_5870_);
                crate::leanh::lean_inc(v_macroStack_5870_);
                v___x_5872_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_5869_, v_macroStack_5870_, v___y_5864_);
                v_a_5873_ = crate::leanh::lean_ctor_get(v___x_5872_, 0);
                v_isSharedCheck_5881_ = (!crate::leanh::lean_is_exclusive(v___x_5872_)) as u8;
                if v_isSharedCheck_5881_ == 0 {
                    v___x_5875_ = v___x_5872_;
                    v_isShared_5876_ = v_isSharedCheck_5881_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5873_);
                    crate::leanh::lean_dec(v___x_5872_);
                    v___x_5875_ = crate::leanh::lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5877_, 0, v___x_5871_);
                crate::leanh::lean_ctor_set(v___x_5877_, 1, v_a_5873_);
                if v_isShared_5876_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5875_, 1);
                    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5877_);
                    v___x_5879_ = v___x_5875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5880_, 0, v___x_5877_);
                    v___x_5879_ = v_reuseFailAlloc_5880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(
    mut v_msg_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5890_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(
        v_msg_5882_,
        v___y_5883_,
        v___y_5884_,
        v___y_5885_,
        v___y_5886_,
        v___y_5887_,
        v___y_5888_,
    );
    crate::leanh::lean_dec(v___y_5888_);
    crate::leanh::lean_dec_ref(v___y_5887_);
    crate::leanh::lean_dec(v___y_5886_);
    crate::leanh::lean_dec_ref(v___y_5885_);
    crate::leanh::lean_dec(v___y_5884_);
    crate::leanh::lean_dec_ref(v___y_5883_);
    return v_res_5890_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(
    mut v_a_5891_: *mut crate::leanh::LeanObject,
    mut v___x_5892_: *mut crate::leanh::LeanObject,
    mut v_____r_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
    mut v___y_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5901_, 0, v_a_5891_);
    v___x_5902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5902_, 0, v___x_5901_);
    crate::leanh::lean_ctor_set(v___x_5902_, 1, v___x_5892_);
    v___x_5903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5903_, 0, v___x_5902_);
    v___x_5904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5904_, 0, v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_5905_: *mut crate::leanh::LeanObject,
    mut v___x_5906_: *mut crate::leanh::LeanObject,
    mut v_____r_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
    mut v___y_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5905_, v___x_5906_, v_____r_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
    crate::leanh::lean_dec(v___y_5913_);
    crate::leanh::lean_dec_ref(v___y_5912_);
    crate::leanh::lean_dec(v___y_5911_);
    crate::leanh::lean_dec_ref(v___y_5910_);
    crate::leanh::lean_dec(v___y_5909_);
    crate::leanh::lean_dec_ref(v___y_5908_);
    return v_res_5915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(
    mut v_cancel_5916_: u8,
    mut v_fst_5917_: *mut crate::leanh::LeanObject,
    mut v_a_5918_: *mut crate::leanh::LeanObject,
    mut v_b_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5936_: u8 = 0;
    let mut v_a_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5943_: u8 = 0;
    let mut v_a_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5947_: u8 = 0;
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5965_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: u8 = 0;
    let mut v_isSharedCheck_5972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5918_) == 0 {
                    crate::leanh::lean_dec_ref(v_fst_5917_);
                    v___x_5927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5927_, 0, v_b_5919_);
                    return v___x_5927_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5919_);
                    v___x_5928_ = l_IO_waitAny_x27___redArg(v_a_5918_);
                    v_fst_5929_ = crate::leanh::lean_ctor_get(v___x_5928_, 0);
                    crate::leanh::lean_inc(v_fst_5929_);
                    v_snd_5930_ = crate::leanh::lean_ctor_get(v___x_5928_, 1);
                    crate::leanh::lean_inc(v_snd_5930_);
                    crate::leanh::lean_dec_ref(v___x_5928_);
                    v___x_5952_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_5925_);
                    crate::leanh::lean_inc_ref(v___y_5924_);
                    crate::leanh::lean_inc(v___y_5923_);
                    crate::leanh::lean_inc_ref(v___y_5922_);
                    crate::leanh::lean_inc(v___y_5921_);
                    crate::leanh::lean_inc_ref(v___y_5920_);
                    v___x_5953_ = crate::leanh::lean_apply_7(
                        v_fst_5929_,
                        v___y_5920_,
                        v___y_5921_,
                        v___y_5922_,
                        v___y_5923_,
                        v___y_5924_,
                        v___y_5925_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5953_) == 0 {
                        if v_cancel_5916_ == 0 {
                            v_a_5954_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                            crate::leanh::lean_inc(v_a_5954_);
                            crate::leanh::lean_dec_ref_known(v___x_5953_, 1);
                            v___x_5955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5954_, v___x_5952_, v___x_5952_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
                            v___y_5932_ = v___x_5955_;
                            state = 1;
                            continue;
                        } else {
                            v_a_5956_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                            crate::leanh::lean_inc(v_a_5956_);
                            crate::leanh::lean_dec_ref_known(v___x_5953_, 1);
                            crate::leanh::lean_inc_ref(v_fst_5917_);
                            v___x_5957_ =
                                crate::leanh::lean_apply_1(v_fst_5917_, crate::leanh::lean_box(0));
                            v___x_5958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5956_, v___x_5952_, v___x_5957_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
                            v___y_5932_ = v___x_5958_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5959_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                        v_isSharedCheck_5972_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                        if v_isSharedCheck_5972_ == 0 {
                            v___x_5961_ = v___x_5953_;
                            v_isShared_5962_ = v_isSharedCheck_5972_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5959_);
                            crate::leanh::lean_dec(v___x_5953_);
                            v___x_5961_ = crate::leanh::lean_box(0);
                            v_isShared_5962_ = v_isSharedCheck_5972_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5932_) == 0 {
                    v_a_5933_ = crate::leanh::lean_ctor_get(v___y_5932_, 0);
                    v_isSharedCheck_5943_ = (!crate::leanh::lean_is_exclusive(v___y_5932_)) as u8;
                    if v_isSharedCheck_5943_ == 0 {
                        v___x_5935_ = v___y_5932_;
                        v_isShared_5936_ = v_isSharedCheck_5943_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5933_);
                        crate::leanh::lean_dec(v___y_5932_);
                        v___x_5935_ = crate::leanh::lean_box(0);
                        v_isShared_5936_ = v_isSharedCheck_5943_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_5930_);
                    crate::leanh::lean_dec_ref(v_fst_5917_);
                    v_a_5944_ = crate::leanh::lean_ctor_get(v___y_5932_, 0);
                    v_isSharedCheck_5951_ = (!crate::leanh::lean_is_exclusive(v___y_5932_)) as u8;
                    if v_isSharedCheck_5951_ == 0 {
                        v___x_5946_ = v___y_5932_;
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5944_);
                        crate::leanh::lean_dec(v___y_5932_);
                        v___x_5946_ = crate::leanh::lean_box(0);
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5933_) == 0 {
                    crate::leanh::lean_dec(v_snd_5930_);
                    crate::leanh::lean_dec_ref(v_fst_5917_);
                    v_a_5937_ = crate::leanh::lean_ctor_get(v_a_5933_, 0);
                    crate::leanh::lean_inc(v_a_5937_);
                    crate::leanh::lean_dec_ref_known(v_a_5933_, 1);
                    if v_isShared_5936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5935_, 0, v_a_5937_);
                        v___x_5939_ = v___x_5935_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5937_);
                        v___x_5939_ = v_reuseFailAlloc_5940_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5935_);
                    v_a_5941_ = crate::leanh::lean_ctor_get(v_a_5933_, 0);
                    crate::leanh::lean_inc(v_a_5941_);
                    crate::leanh::lean_dec_ref_known(v_a_5933_, 1);
                    v_a_5918_ = v_snd_5930_;
                    v_b_5919_ = v_a_5941_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_5939_;
            }
            4 => {
                if v_isShared_5947_ == 0 {
                    v___x_5949_ = v___x_5946_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_a_5944_);
                    v___x_5949_ = v_reuseFailAlloc_5950_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5949_;
            }
            6 => {
                v___x_5963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                v___x_5970_ = l_Lean_Exception_isInterrupt(v_a_5959_);
                if v___x_5970_ == 0 {
                    crate::leanh::lean_inc(v_a_5959_);
                    v___x_5971_ = l_Lean_Exception_isRuntime(v_a_5959_);
                    v___y_5965_ = v___x_5971_;
                    state = 7;
                    continue;
                } else {
                    v___y_5965_ = v___x_5970_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_5965_ == 0 {
                    crate::leanh::lean_del_object(v___x_5961_);
                    crate::leanh::lean_dec(v_a_5959_);
                    v_a_5918_ = v_snd_5930_;
                    v_b_5919_ = v___x_5963_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_5930_);
                    crate::leanh::lean_dec_ref(v_fst_5917_);
                    if v_isShared_5962_ == 0 {
                        v___x_5968_ = v___x_5961_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5959_);
                        v___x_5968_ = v_reuseFailAlloc_5969_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_5968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(
    mut v_cancel_5973_: *mut crate::leanh::LeanObject,
    mut v_fst_5974_: *mut crate::leanh::LeanObject,
    mut v_a_5975_: *mut crate::leanh::LeanObject,
    mut v_b_5976_: *mut crate::leanh::LeanObject,
    mut v___y_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_5984_: u8 = 0;
    let mut v_res_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5984_ = (crate::leanh::lean_unbox(v_cancel_5973_) as u8);
    v_res_5985_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(
            v_cancel_boxed_5984_,
            v_fst_5974_,
            v_a_5975_,
            v_b_5976_,
            v___y_5977_,
            v___y_5978_,
            v___y_5979_,
            v___y_5980_,
            v___y_5981_,
            v___y_5982_,
        );
    crate::leanh::lean_dec(v___y_5982_);
    crate::leanh::lean_dec_ref(v___y_5981_);
    crate::leanh::lean_dec(v___y_5980_);
    crate::leanh::lean_dec_ref(v___y_5979_);
    crate::leanh::lean_dec(v___y_5978_);
    crate::leanh::lean_dec_ref(v___y_5977_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst___redArg(
    mut v_jobs_5986_: *mut crate::leanh::LeanObject,
    mut v_cancel_5987_: u8,
    mut v_a_5988_: *mut crate::leanh::LeanObject,
    mut v_a_5989_: *mut crate::leanh::LeanObject,
    mut v_a_5990_: *mut crate::leanh::LeanObject,
    mut v_a_5991_: *mut crate::leanh::LeanObject,
    mut v_a_5992_: *mut crate::leanh::LeanObject,
    mut v_a_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v_fst_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6012_: u8 = 0;
    let mut v_a_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6020_: u8 = 0;
    let mut v_a_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6024_: u8 = 0;
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5995_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
                    v_jobs_5986_,
                    v_a_5988_,
                    v_a_5989_,
                    v_a_5990_,
                    v_a_5991_,
                    v_a_5992_,
                    v_a_5993_,
                );
                if crate::leanh::lean_obj_tag(v___x_5995_) == 0 {
                    v_a_5996_ = crate::leanh::lean_ctor_get(v___x_5995_, 0);
                    crate::leanh::lean_inc(v_a_5996_);
                    crate::leanh::lean_dec_ref_known(v___x_5995_, 1);
                    v_fst_5997_ = crate::leanh::lean_ctor_get(v_a_5996_, 0);
                    crate::leanh::lean_inc(v_fst_5997_);
                    v_snd_5998_ = crate::leanh::lean_ctor_get(v_a_5996_, 1);
                    crate::leanh::lean_inc(v_snd_5998_);
                    crate::leanh::lean_dec(v_a_5996_);
                    v___x_5999_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_6000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_5987_, v_fst_5997_, v_snd_5998_, v___x_5999_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
                    if crate::leanh::lean_obj_tag(v___x_6000_) == 0 {
                        v_a_6001_ = crate::leanh::lean_ctor_get(v___x_6000_, 0);
                        v_isSharedCheck_6012_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6000_)) as u8;
                        if v_isSharedCheck_6012_ == 0 {
                            v___x_6003_ = v___x_6000_;
                            v_isShared_6004_ = v_isSharedCheck_6012_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6001_);
                            crate::leanh::lean_dec(v___x_6000_);
                            v___x_6003_ = crate::leanh::lean_box(0);
                            v_isShared_6004_ = v_isSharedCheck_6012_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6013_ = crate::leanh::lean_ctor_get(v___x_6000_, 0);
                        v_isSharedCheck_6020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6000_)) as u8;
                        if v_isSharedCheck_6020_ == 0 {
                            v___x_6015_ = v___x_6000_;
                            v_isShared_6016_ = v_isSharedCheck_6020_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6013_);
                            crate::leanh::lean_dec(v___x_6000_);
                            v___x_6015_ = crate::leanh::lean_box(0);
                            v_isShared_6016_ = v_isSharedCheck_6020_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6021_ = crate::leanh::lean_ctor_get(v___x_5995_, 0);
                    v_isSharedCheck_6028_ = (!crate::leanh::lean_is_exclusive(v___x_5995_)) as u8;
                    if v_isSharedCheck_6028_ == 0 {
                        v___x_6023_ = v___x_5995_;
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6021_);
                        crate::leanh::lean_dec(v___x_5995_);
                        v___x_6023_ = crate::leanh::lean_box(0);
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6005_ = crate::leanh::lean_ctor_get(v_a_6001_, 0);
                crate::leanh::lean_inc(v_fst_6005_);
                crate::leanh::lean_dec(v_a_6001_);
                if crate::leanh::lean_obj_tag(v_fst_6005_) == 0 {
                    crate::leanh::lean_del_object(v___x_6003_);
                    v___x_6006_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_6007_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_6006_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
                    return v___x_6007_;
                } else {
                    v_val_6008_ = crate::leanh::lean_ctor_get(v_fst_6005_, 0);
                    crate::leanh::lean_inc(v_val_6008_);
                    crate::leanh::lean_dec_ref_known(v_fst_6005_, 1);
                    if v_isShared_6004_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6003_, 0, v_val_6008_);
                        v___x_6010_ = v___x_6003_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_val_6008_);
                        v___x_6010_ = v_reuseFailAlloc_6011_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6010_;
            }
            3 => {
                if v_isShared_6016_ == 0 {
                    v___x_6018_ = v___x_6015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6019_, 0, v_a_6013_);
                    v___x_6018_ = v_reuseFailAlloc_6019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6018_;
            }
            5 => {
                if v_isShared_6024_ == 0 {
                    v___x_6026_ = v___x_6023_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
                    v___x_6026_ = v_reuseFailAlloc_6027_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(
    mut v_jobs_6029_: *mut crate::leanh::LeanObject,
    mut v_cancel_6030_: *mut crate::leanh::LeanObject,
    mut v_a_6031_: *mut crate::leanh::LeanObject,
    mut v_a_6032_: *mut crate::leanh::LeanObject,
    mut v_a_6033_: *mut crate::leanh::LeanObject,
    mut v_a_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
    mut v_a_6037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_6038_: u8 = 0;
    let mut v_res_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6038_ = (crate::leanh::lean_unbox(v_cancel_6030_) as u8);
    v_res_6039_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(
        v_jobs_6029_,
        v_cancel_boxed_6038_,
        v_a_6031_,
        v_a_6032_,
        v_a_6033_,
        v_a_6034_,
        v_a_6035_,
        v_a_6036_,
    );
    crate::leanh::lean_dec(v_a_6036_);
    crate::leanh::lean_dec_ref(v_a_6035_);
    crate::leanh::lean_dec(v_a_6034_);
    crate::leanh::lean_dec_ref(v_a_6033_);
    crate::leanh::lean_dec(v_a_6032_);
    crate::leanh::lean_dec_ref(v_a_6031_);
    return v_res_6039_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst(
    mut v_00_u03b1_6040_: *mut crate::leanh::LeanObject,
    mut v_jobs_6041_: *mut crate::leanh::LeanObject,
    mut v_cancel_6042_: u8,
    mut v_a_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
    mut v_a_6048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6050_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(
        v_jobs_6041_,
        v_cancel_6042_,
        v_a_6043_,
        v_a_6044_,
        v_a_6045_,
        v_a_6046_,
        v_a_6047_,
        v_a_6048_,
    );
    return v___x_6050_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst___boxed(
    mut v_00_u03b1_6051_: *mut crate::leanh::LeanObject,
    mut v_jobs_6052_: *mut crate::leanh::LeanObject,
    mut v_cancel_6053_: *mut crate::leanh::LeanObject,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
    mut v_a_6059_: *mut crate::leanh::LeanObject,
    mut v_a_6060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_6061_: u8 = 0;
    let mut v_res_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6061_ = (crate::leanh::lean_unbox(v_cancel_6053_) as u8);
    v_res_6062_ = l_Lean_Elab_Term_TermElabM_parFirst(
        v_00_u03b1_6051_,
        v_jobs_6052_,
        v_cancel_boxed_6061_,
        v_a_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
        v_a_6059_,
    );
    crate::leanh::lean_dec(v_a_6059_);
    crate::leanh::lean_dec_ref(v_a_6058_);
    crate::leanh::lean_dec(v_a_6057_);
    crate::leanh::lean_dec_ref(v_a_6056_);
    crate::leanh::lean_dec(v_a_6055_);
    crate::leanh::lean_dec_ref(v_a_6054_);
    return v_res_6062_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(
    mut v_00_u03b1_6063_: *mut crate::leanh::LeanObject,
    mut v_cancel_6064_: u8,
    mut v_fst_6065_: *mut crate::leanh::LeanObject,
    mut v_inst_6066_: *mut crate::leanh::LeanObject,
    mut v_R_6067_: *mut crate::leanh::LeanObject,
    mut v_a_6068_: *mut crate::leanh::LeanObject,
    mut v_b_6069_: *mut crate::leanh::LeanObject,
    mut v_c_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6078_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(
            v_cancel_6064_,
            v_fst_6065_,
            v_a_6068_,
            v_b_6069_,
            v___y_6071_,
            v___y_6072_,
            v___y_6073_,
            v___y_6074_,
            v___y_6075_,
            v___y_6076_,
        );
    return v___x_6078_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(
    mut v_00_u03b1_6079_: *mut crate::leanh::LeanObject,
    mut v_cancel_6080_: *mut crate::leanh::LeanObject,
    mut v_fst_6081_: *mut crate::leanh::LeanObject,
    mut v_inst_6082_: *mut crate::leanh::LeanObject,
    mut v_R_6083_: *mut crate::leanh::LeanObject,
    mut v_a_6084_: *mut crate::leanh::LeanObject,
    mut v_b_6085_: *mut crate::leanh::LeanObject,
    mut v_c_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
    mut v___y_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_6094_: u8 = 0;
    let mut v_res_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6094_ = (crate::leanh::lean_unbox(v_cancel_6080_) as u8);
    v_res_6095_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(
        v_00_u03b1_6079_,
        v_cancel_boxed_6094_,
        v_fst_6081_,
        v_inst_6082_,
        v_R_6083_,
        v_a_6084_,
        v_b_6085_,
        v_c_6086_,
        v___y_6087_,
        v___y_6088_,
        v___y_6089_,
        v___y_6090_,
        v___y_6091_,
        v___y_6092_,
    );
    crate::leanh::lean_dec(v___y_6092_);
    crate::leanh::lean_dec_ref(v___y_6091_);
    crate::leanh::lean_dec(v___y_6090_);
    crate::leanh::lean_dec_ref(v___y_6089_);
    crate::leanh::lean_dec(v___y_6088_);
    crate::leanh::lean_dec_ref(v___y_6087_);
    return v_res_6095_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(
    mut v_00_u03b1_6096_: *mut crate::leanh::LeanObject,
    mut v_msg_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
    mut v___y_6099_: *mut crate::leanh::LeanObject,
    mut v___y_6100_: *mut crate::leanh::LeanObject,
    mut v___y_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
    mut v___y_6103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6105_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(
        v_msg_6097_,
        v___y_6098_,
        v___y_6099_,
        v___y_6100_,
        v___y_6101_,
        v___y_6102_,
        v___y_6103_,
    );
    return v___x_6105_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(
    mut v_00_u03b1_6106_: *mut crate::leanh::LeanObject,
    mut v_msg_6107_: *mut crate::leanh::LeanObject,
    mut v___y_6108_: *mut crate::leanh::LeanObject,
    mut v___y_6109_: *mut crate::leanh::LeanObject,
    mut v___y_6110_: *mut crate::leanh::LeanObject,
    mut v___y_6111_: *mut crate::leanh::LeanObject,
    mut v___y_6112_: *mut crate::leanh::LeanObject,
    mut v___y_6113_: *mut crate::leanh::LeanObject,
    mut v___y_6114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6115_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(
        v_00_u03b1_6106_,
        v_msg_6107_,
        v___y_6108_,
        v___y_6109_,
        v___y_6110_,
        v___y_6111_,
        v___y_6112_,
        v___y_6113_,
    );
    crate::leanh::lean_dec(v___y_6113_);
    crate::leanh::lean_dec_ref(v___y_6112_);
    crate::leanh::lean_dec(v___y_6111_);
    crate::leanh::lean_dec_ref(v___y_6110_);
    crate::leanh::lean_dec(v___y_6109_);
    crate::leanh::lean_dec_ref(v___y_6108_);
    return v_res_6115_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(
    mut v_msgData_6116_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6117_: *mut crate::leanh::LeanObject,
    mut v___y_6118_: *mut crate::leanh::LeanObject,
    mut v___y_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
    mut v___y_6122_: *mut crate::leanh::LeanObject,
    mut v___y_6123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6125_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_6116_, v_macroStack_6117_, v___y_6122_);
    return v___x_6125_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_6126_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6127_: *mut crate::leanh::LeanObject,
    mut v___y_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6135_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_6126_, v_macroStack_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
    crate::leanh::lean_dec(v___y_6133_);
    crate::leanh::lean_dec_ref(v___y_6132_);
    crate::leanh::lean_dec(v___y_6131_);
    crate::leanh::lean_dec_ref(v___y_6130_);
    crate::leanh::lean_dec(v___y_6129_);
    crate::leanh::lean_dec_ref(v___y_6128_);
    return v_res_6135_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(
    mut v_x_6136_: *mut crate::leanh::LeanObject,
    mut v_x_6137_: *mut crate::leanh::LeanObject,
    mut v___y_6138_: *mut crate::leanh::LeanObject,
    mut v___y_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
    mut v___y_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v_isSharedCheck_6168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6136_) == 0 {
                    v___x_6147_ = l_List_reverse___redArg(v_x_6137_);
                    v___x_6148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6148_, 0, v___x_6147_);
                    return v___x_6148_;
                } else {
                    v_head_6149_ = crate::leanh::lean_ctor_get(v_x_6136_, 0);
                    v_tail_6150_ = crate::leanh::lean_ctor_get(v_x_6136_, 1);
                    v_isSharedCheck_6168_ = (!crate::leanh::lean_is_exclusive(v_x_6136_)) as u8;
                    if v_isSharedCheck_6168_ == 0 {
                        v___x_6152_ = v_x_6136_;
                        v_isShared_6153_ = v_isSharedCheck_6168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6150_);
                        crate::leanh::lean_inc(v_head_6149_);
                        crate::leanh::lean_dec(v_x_6136_);
                        v___x_6152_ = crate::leanh::lean_box(0);
                        v_isShared_6153_ = v_isSharedCheck_6168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6154_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(
                    v_head_6149_,
                    v___y_6138_,
                    v___y_6139_,
                    v___y_6140_,
                    v___y_6141_,
                    v___y_6142_,
                    v___y_6143_,
                    v___y_6144_,
                    v___y_6145_,
                );
                if crate::leanh::lean_obj_tag(v___x_6154_) == 0 {
                    v_a_6155_ = crate::leanh::lean_ctor_get(v___x_6154_, 0);
                    crate::leanh::lean_inc(v_a_6155_);
                    crate::leanh::lean_dec_ref_known(v___x_6154_, 1);
                    if v_isShared_6153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6152_, 1, v_x_6137_);
                        crate::leanh::lean_ctor_set(v___x_6152_, 0, v_a_6155_);
                        v___x_6157_ = v___x_6152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6159_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_a_6155_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6159_, 1, v_x_6137_);
                        v___x_6157_ = v_reuseFailAlloc_6159_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6152_);
                    crate::leanh::lean_dec(v_tail_6150_);
                    crate::leanh::lean_dec(v_x_6137_);
                    v_a_6160_ = crate::leanh::lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6167_ = (!crate::leanh::lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6167_ == 0 {
                        v___x_6162_ = v___x_6154_;
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6160_);
                        crate::leanh::lean_dec(v___x_6154_);
                        v___x_6162_ = crate::leanh::lean_box(0);
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6136_ = v_tail_6150_;
                v_x_6137_ = v___x_6157_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6163_ == 0 {
                    v___x_6165_ = v___x_6162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(
    mut v_x_6169_: *mut crate::leanh::LeanObject,
    mut v_x_6170_: *mut crate::leanh::LeanObject,
    mut v___y_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6180_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(
            v_x_6169_,
            v_x_6170_,
            v___y_6171_,
            v___y_6172_,
            v___y_6173_,
            v___y_6174_,
            v___y_6175_,
            v___y_6176_,
            v___y_6177_,
            v___y_6178_,
        );
    crate::leanh::lean_dec(v___y_6178_);
    crate::leanh::lean_dec_ref(v___y_6177_);
    crate::leanh::lean_dec(v___y_6176_);
    crate::leanh::lean_dec_ref(v___y_6175_);
    crate::leanh::lean_dec(v___y_6174_);
    crate::leanh::lean_dec_ref(v___y_6173_);
    crate::leanh::lean_dec(v___y_6172_);
    crate::leanh::lean_dec_ref(v___y_6171_);
    return v_res_6180_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(
    mut v_jobs_6181_: *mut crate::leanh::LeanObject,
    mut v_a_6182_: *mut crate::leanh::LeanObject,
    mut v_a_6183_: *mut crate::leanh::LeanObject,
    mut v_a_6184_: *mut crate::leanh::LeanObject,
    mut v_a_6185_: *mut crate::leanh::LeanObject,
    mut v_a_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6196_: u8 = 0;
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut v_a_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6215_: u8 = 0;
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6191_ = crate::leanh::lean_box(0);
                v___x_6192_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_6181_, v___x_6191_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
                if crate::leanh::lean_obj_tag(v___x_6192_) == 0 {
                    v_a_6193_ = crate::leanh::lean_ctor_get(v___x_6192_, 0);
                    v_isSharedCheck_6211_ = (!crate::leanh::lean_is_exclusive(v___x_6192_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v___x_6195_ = v___x_6192_;
                        v_isShared_6196_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6193_);
                        crate::leanh::lean_dec(v___x_6192_);
                        v___x_6195_ = crate::leanh::lean_box(0);
                        v_isShared_6196_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6212_ = crate::leanh::lean_ctor_get(v___x_6192_, 0);
                    v_isSharedCheck_6219_ = (!crate::leanh::lean_is_exclusive(v___x_6192_)) as u8;
                    if v_isSharedCheck_6219_ == 0 {
                        v___x_6214_ = v___x_6192_;
                        v_isShared_6215_ = v_isSharedCheck_6219_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6212_);
                        crate::leanh::lean_dec(v___x_6192_);
                        v___x_6214_ = crate::leanh::lean_box(0);
                        v_isShared_6215_ = v_isSharedCheck_6219_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6197_ = l_List_unzipTR___redArg(v_a_6193_);
                v_fst_6198_ = crate::leanh::lean_ctor_get(v___x_6197_, 0);
                v_snd_6199_ = crate::leanh::lean_ctor_get(v___x_6197_, 1);
                v_isSharedCheck_6210_ = (!crate::leanh::lean_is_exclusive(v___x_6197_)) as u8;
                if v_isSharedCheck_6210_ == 0 {
                    v___x_6201_ = v___x_6197_;
                    v_isShared_6202_ = v_isSharedCheck_6210_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6199_);
                    crate::leanh::lean_inc(v_fst_6198_);
                    crate::leanh::lean_dec(v___x_6197_);
                    v___x_6201_ = crate::leanh::lean_box(0);
                    v_isShared_6202_ = v_isSharedCheck_6210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6203_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_6203_, 0, v_fst_6198_);
                if v_isShared_6202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6201_, 0, v___x_6203_);
                    v___x_6205_ = v___x_6201_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v___x_6203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 1, v_snd_6199_);
                    v___x_6205_ = v_reuseFailAlloc_6209_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6195_, 0, v___x_6205_);
                    v___x_6207_ = v___x_6195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6205_);
                    v___x_6207_ = v_reuseFailAlloc_6208_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6207_;
            }
            5 => {
                if v_isShared_6215_ == 0 {
                    v___x_6217_ = v___x_6214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6218_, 0, v_a_6212_);
                    v___x_6217_ = v_reuseFailAlloc_6218_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(
    mut v_jobs_6220_: *mut crate::leanh::LeanObject,
    mut v_a_6221_: *mut crate::leanh::LeanObject,
    mut v_a_6222_: *mut crate::leanh::LeanObject,
    mut v_a_6223_: *mut crate::leanh::LeanObject,
    mut v_a_6224_: *mut crate::leanh::LeanObject,
    mut v_a_6225_: *mut crate::leanh::LeanObject,
    mut v_a_6226_: *mut crate::leanh::LeanObject,
    mut v_a_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_a_6229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6230_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(
        v_jobs_6220_,
        v_a_6221_,
        v_a_6222_,
        v_a_6223_,
        v_a_6224_,
        v_a_6225_,
        v_a_6226_,
        v_a_6227_,
        v_a_6228_,
    );
    crate::leanh::lean_dec(v_a_6228_);
    crate::leanh::lean_dec_ref(v_a_6227_);
    crate::leanh::lean_dec(v_a_6226_);
    crate::leanh::lean_dec_ref(v_a_6225_);
    crate::leanh::lean_dec(v_a_6224_);
    crate::leanh::lean_dec_ref(v_a_6223_);
    crate::leanh::lean_dec(v_a_6222_);
    crate::leanh::lean_dec_ref(v_a_6221_);
    return v_res_6230_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel(
    mut v_00_u03b1_6231_: *mut crate::leanh::LeanObject,
    mut v_jobs_6232_: *mut crate::leanh::LeanObject,
    mut v_a_6233_: *mut crate::leanh::LeanObject,
    mut v_a_6234_: *mut crate::leanh::LeanObject,
    mut v_a_6235_: *mut crate::leanh::LeanObject,
    mut v_a_6236_: *mut crate::leanh::LeanObject,
    mut v_a_6237_: *mut crate::leanh::LeanObject,
    mut v_a_6238_: *mut crate::leanh::LeanObject,
    mut v_a_6239_: *mut crate::leanh::LeanObject,
    mut v_a_6240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6242_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(
        v_jobs_6232_,
        v_a_6233_,
        v_a_6234_,
        v_a_6235_,
        v_a_6236_,
        v_a_6237_,
        v_a_6238_,
        v_a_6239_,
        v_a_6240_,
    );
    return v___x_6242_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(
    mut v_00_u03b1_6243_: *mut crate::leanh::LeanObject,
    mut v_jobs_6244_: *mut crate::leanh::LeanObject,
    mut v_a_6245_: *mut crate::leanh::LeanObject,
    mut v_a_6246_: *mut crate::leanh::LeanObject,
    mut v_a_6247_: *mut crate::leanh::LeanObject,
    mut v_a_6248_: *mut crate::leanh::LeanObject,
    mut v_a_6249_: *mut crate::leanh::LeanObject,
    mut v_a_6250_: *mut crate::leanh::LeanObject,
    mut v_a_6251_: *mut crate::leanh::LeanObject,
    mut v_a_6252_: *mut crate::leanh::LeanObject,
    mut v_a_6253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6254_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(
        v_00_u03b1_6243_,
        v_jobs_6244_,
        v_a_6245_,
        v_a_6246_,
        v_a_6247_,
        v_a_6248_,
        v_a_6249_,
        v_a_6250_,
        v_a_6251_,
        v_a_6252_,
    );
    crate::leanh::lean_dec(v_a_6252_);
    crate::leanh::lean_dec_ref(v_a_6251_);
    crate::leanh::lean_dec(v_a_6250_);
    crate::leanh::lean_dec_ref(v_a_6249_);
    crate::leanh::lean_dec(v_a_6248_);
    crate::leanh::lean_dec_ref(v_a_6247_);
    crate::leanh::lean_dec(v_a_6246_);
    crate::leanh::lean_dec_ref(v_a_6245_);
    return v_res_6254_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(
    mut v_00_u03b1_6255_: *mut crate::leanh::LeanObject,
    mut v_x_6256_: *mut crate::leanh::LeanObject,
    mut v_x_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
    mut v___y_6264_: *mut crate::leanh::LeanObject,
    mut v___y_6265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6267_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(
            v_x_6256_,
            v_x_6257_,
            v___y_6258_,
            v___y_6259_,
            v___y_6260_,
            v___y_6261_,
            v___y_6262_,
            v___y_6263_,
            v___y_6264_,
            v___y_6265_,
        );
    return v___x_6267_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(
    mut v_00_u03b1_6268_: *mut crate::leanh::LeanObject,
    mut v_x_6269_: *mut crate::leanh::LeanObject,
    mut v_x_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
    mut v___y_6277_: *mut crate::leanh::LeanObject,
    mut v___y_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6280_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(
        v_00_u03b1_6268_,
        v_x_6269_,
        v_x_6270_,
        v___y_6271_,
        v___y_6272_,
        v___y_6273_,
        v___y_6274_,
        v___y_6275_,
        v___y_6276_,
        v___y_6277_,
        v___y_6278_,
    );
    crate::leanh::lean_dec(v___y_6278_);
    crate::leanh::lean_dec_ref(v___y_6277_);
    crate::leanh::lean_dec(v___y_6276_);
    crate::leanh::lean_dec_ref(v___y_6275_);
    crate::leanh::lean_dec(v___y_6274_);
    crate::leanh::lean_dec_ref(v___y_6273_);
    crate::leanh::lean_dec(v___y_6272_);
    crate::leanh::lean_dec_ref(v___y_6271_);
    return v_res_6280_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter___redArg(
    mut v_jobs_6281_: *mut crate::leanh::LeanObject,
    mut v_a_6282_: *mut crate::leanh::LeanObject,
    mut v_a_6283_: *mut crate::leanh::LeanObject,
    mut v_a_6284_: *mut crate::leanh::LeanObject,
    mut v_a_6285_: *mut crate::leanh::LeanObject,
    mut v_a_6286_: *mut crate::leanh::LeanObject,
    mut v_a_6287_: *mut crate::leanh::LeanObject,
    mut v_a_6288_: *mut crate::leanh::LeanObject,
    mut v_a_6289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_snd_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v_a_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6291_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(
                    v_jobs_6281_,
                    v_a_6282_,
                    v_a_6283_,
                    v_a_6284_,
                    v_a_6285_,
                    v_a_6286_,
                    v_a_6287_,
                    v_a_6288_,
                    v_a_6289_,
                );
                if crate::leanh::lean_obj_tag(v___x_6291_) == 0 {
                    v_a_6292_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6300_ = (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6292_);
                        crate::leanh::lean_dec(v___x_6291_);
                        v___x_6294_ = crate::leanh::lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6301_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6308_ = (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6308_ == 0 {
                        v___x_6303_ = v___x_6291_;
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6301_);
                        crate::leanh::lean_dec(v___x_6291_);
                        v___x_6303_ = crate::leanh::lean_box(0);
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6296_ = crate::leanh::lean_ctor_get(v_a_6292_, 1);
                crate::leanh::lean_inc(v_snd_6296_);
                crate::leanh::lean_dec(v_a_6292_);
                if v_isShared_6295_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6294_, 0, v_snd_6296_);
                    v___x_6298_ = v___x_6294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_snd_6296_);
                    v___x_6298_ = v_reuseFailAlloc_6299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6298_;
            }
            3 => {
                if v_isShared_6304_ == 0 {
                    v___x_6306_ = v___x_6303_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6307_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_a_6301_);
                    v___x_6306_ = v_reuseFailAlloc_6307_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(
    mut v_jobs_6309_: *mut crate::leanh::LeanObject,
    mut v_a_6310_: *mut crate::leanh::LeanObject,
    mut v_a_6311_: *mut crate::leanh::LeanObject,
    mut v_a_6312_: *mut crate::leanh::LeanObject,
    mut v_a_6313_: *mut crate::leanh::LeanObject,
    mut v_a_6314_: *mut crate::leanh::LeanObject,
    mut v_a_6315_: *mut crate::leanh::LeanObject,
    mut v_a_6316_: *mut crate::leanh::LeanObject,
    mut v_a_6317_: *mut crate::leanh::LeanObject,
    mut v_a_6318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6319_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(
        v_jobs_6309_,
        v_a_6310_,
        v_a_6311_,
        v_a_6312_,
        v_a_6313_,
        v_a_6314_,
        v_a_6315_,
        v_a_6316_,
        v_a_6317_,
    );
    crate::leanh::lean_dec(v_a_6317_);
    crate::leanh::lean_dec_ref(v_a_6316_);
    crate::leanh::lean_dec(v_a_6315_);
    crate::leanh::lean_dec_ref(v_a_6314_);
    crate::leanh::lean_dec(v_a_6313_);
    crate::leanh::lean_dec_ref(v_a_6312_);
    crate::leanh::lean_dec(v_a_6311_);
    crate::leanh::lean_dec_ref(v_a_6310_);
    return v_res_6319_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter(
    mut v_00_u03b1_6320_: *mut crate::leanh::LeanObject,
    mut v_jobs_6321_: *mut crate::leanh::LeanObject,
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v_a_6323_: *mut crate::leanh::LeanObject,
    mut v_a_6324_: *mut crate::leanh::LeanObject,
    mut v_a_6325_: *mut crate::leanh::LeanObject,
    mut v_a_6326_: *mut crate::leanh::LeanObject,
    mut v_a_6327_: *mut crate::leanh::LeanObject,
    mut v_a_6328_: *mut crate::leanh::LeanObject,
    mut v_a_6329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6331_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(
        v_jobs_6321_,
        v_a_6322_,
        v_a_6323_,
        v_a_6324_,
        v_a_6325_,
        v_a_6326_,
        v_a_6327_,
        v_a_6328_,
        v_a_6329_,
    );
    return v___x_6331_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter___boxed(
    mut v_00_u03b1_6332_: *mut crate::leanh::LeanObject,
    mut v_jobs_6333_: *mut crate::leanh::LeanObject,
    mut v_a_6334_: *mut crate::leanh::LeanObject,
    mut v_a_6335_: *mut crate::leanh::LeanObject,
    mut v_a_6336_: *mut crate::leanh::LeanObject,
    mut v_a_6337_: *mut crate::leanh::LeanObject,
    mut v_a_6338_: *mut crate::leanh::LeanObject,
    mut v_a_6339_: *mut crate::leanh::LeanObject,
    mut v_a_6340_: *mut crate::leanh::LeanObject,
    mut v_a_6341_: *mut crate::leanh::LeanObject,
    mut v_a_6342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6343_ = l_Lean_Elab_Tactic_TacticM_parIter(
        v_00_u03b1_6332_,
        v_jobs_6333_,
        v_a_6334_,
        v_a_6335_,
        v_a_6336_,
        v_a_6337_,
        v_a_6338_,
        v_a_6339_,
        v_a_6340_,
        v_a_6341_,
    );
    crate::leanh::lean_dec(v_a_6341_);
    crate::leanh::lean_dec_ref(v_a_6340_);
    crate::leanh::lean_dec(v_a_6339_);
    crate::leanh::lean_dec_ref(v_a_6338_);
    crate::leanh::lean_dec(v_a_6337_);
    crate::leanh::lean_dec_ref(v_a_6336_);
    crate::leanh::lean_dec(v_a_6335_);
    crate::leanh::lean_dec_ref(v_a_6334_);
    return v_res_6343_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
    mut v_jobs_6344_: *mut crate::leanh::LeanObject,
    mut v_a_6345_: *mut crate::leanh::LeanObject,
    mut v_a_6346_: *mut crate::leanh::LeanObject,
    mut v_a_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
    mut v_a_6350_: *mut crate::leanh::LeanObject,
    mut v_a_6351_: *mut crate::leanh::LeanObject,
    mut v_a_6352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut v_a_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6378_: u8 = 0;
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6354_ = crate::leanh::lean_box(0);
                v___x_6355_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_6344_, v___x_6354_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_, v_a_6351_, v_a_6352_);
                if crate::leanh::lean_obj_tag(v___x_6355_) == 0 {
                    v_a_6356_ = crate::leanh::lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6374_ = (!crate::leanh::lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6374_ == 0 {
                        v___x_6358_ = v___x_6355_;
                        v_isShared_6359_ = v_isSharedCheck_6374_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6356_);
                        crate::leanh::lean_dec(v___x_6355_);
                        v___x_6358_ = crate::leanh::lean_box(0);
                        v_isShared_6359_ = v_isSharedCheck_6374_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6375_ = crate::leanh::lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6382_ = (!crate::leanh::lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6382_ == 0 {
                        v___x_6377_ = v___x_6355_;
                        v_isShared_6378_ = v_isSharedCheck_6382_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6375_);
                        crate::leanh::lean_dec(v___x_6355_);
                        v___x_6377_ = crate::leanh::lean_box(0);
                        v_isShared_6378_ = v_isSharedCheck_6382_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6360_ = l_List_unzipTR___redArg(v_a_6356_);
                v_fst_6361_ = crate::leanh::lean_ctor_get(v___x_6360_, 0);
                v_snd_6362_ = crate::leanh::lean_ctor_get(v___x_6360_, 1);
                v_isSharedCheck_6373_ = (!crate::leanh::lean_is_exclusive(v___x_6360_)) as u8;
                if v_isSharedCheck_6373_ == 0 {
                    v___x_6364_ = v___x_6360_;
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6362_);
                    crate::leanh::lean_inc(v_fst_6361_);
                    crate::leanh::lean_dec(v___x_6360_);
                    v___x_6364_ = crate::leanh::lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6366_ = crate::leanh::lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_6366_, 0, v_fst_6361_);
                if v_isShared_6365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6364_, 0, v___x_6366_);
                    v___x_6368_ = v___x_6364_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v___x_6366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 1, v_snd_6362_);
                    v___x_6368_ = v_reuseFailAlloc_6372_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6358_, 0, v___x_6368_);
                    v___x_6370_ = v___x_6358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6371_, 0, v___x_6368_);
                    v___x_6370_ = v_reuseFailAlloc_6371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6370_;
            }
            5 => {
                if v_isShared_6378_ == 0 {
                    v___x_6380_ = v___x_6377_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_a_6375_);
                    v___x_6380_ = v_reuseFailAlloc_6381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(
    mut v_jobs_6383_: *mut crate::leanh::LeanObject,
    mut v_a_6384_: *mut crate::leanh::LeanObject,
    mut v_a_6385_: *mut crate::leanh::LeanObject,
    mut v_a_6386_: *mut crate::leanh::LeanObject,
    mut v_a_6387_: *mut crate::leanh::LeanObject,
    mut v_a_6388_: *mut crate::leanh::LeanObject,
    mut v_a_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6393_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
        v_jobs_6383_,
        v_a_6384_,
        v_a_6385_,
        v_a_6386_,
        v_a_6387_,
        v_a_6388_,
        v_a_6389_,
        v_a_6390_,
        v_a_6391_,
    );
    crate::leanh::lean_dec(v_a_6391_);
    crate::leanh::lean_dec_ref(v_a_6390_);
    crate::leanh::lean_dec(v_a_6389_);
    crate::leanh::lean_dec_ref(v_a_6388_);
    crate::leanh::lean_dec(v_a_6387_);
    crate::leanh::lean_dec_ref(v_a_6386_);
    crate::leanh::lean_dec(v_a_6385_);
    crate::leanh::lean_dec_ref(v_a_6384_);
    return v_res_6393_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(
    mut v_00_u03b1_6394_: *mut crate::leanh::LeanObject,
    mut v_jobs_6395_: *mut crate::leanh::LeanObject,
    mut v_a_6396_: *mut crate::leanh::LeanObject,
    mut v_a_6397_: *mut crate::leanh::LeanObject,
    mut v_a_6398_: *mut crate::leanh::LeanObject,
    mut v_a_6399_: *mut crate::leanh::LeanObject,
    mut v_a_6400_: *mut crate::leanh::LeanObject,
    mut v_a_6401_: *mut crate::leanh::LeanObject,
    mut v_a_6402_: *mut crate::leanh::LeanObject,
    mut v_a_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6405_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
        v_jobs_6395_,
        v_a_6396_,
        v_a_6397_,
        v_a_6398_,
        v_a_6399_,
        v_a_6400_,
        v_a_6401_,
        v_a_6402_,
        v_a_6403_,
    );
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(
    mut v_00_u03b1_6406_: *mut crate::leanh::LeanObject,
    mut v_jobs_6407_: *mut crate::leanh::LeanObject,
    mut v_a_6408_: *mut crate::leanh::LeanObject,
    mut v_a_6409_: *mut crate::leanh::LeanObject,
    mut v_a_6410_: *mut crate::leanh::LeanObject,
    mut v_a_6411_: *mut crate::leanh::LeanObject,
    mut v_a_6412_: *mut crate::leanh::LeanObject,
    mut v_a_6413_: *mut crate::leanh::LeanObject,
    mut v_a_6414_: *mut crate::leanh::LeanObject,
    mut v_a_6415_: *mut crate::leanh::LeanObject,
    mut v_a_6416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6417_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(
        v_00_u03b1_6406_,
        v_jobs_6407_,
        v_a_6408_,
        v_a_6409_,
        v_a_6410_,
        v_a_6411_,
        v_a_6412_,
        v_a_6413_,
        v_a_6414_,
        v_a_6415_,
    );
    crate::leanh::lean_dec(v_a_6415_);
    crate::leanh::lean_dec_ref(v_a_6414_);
    crate::leanh::lean_dec(v_a_6413_);
    crate::leanh::lean_dec_ref(v_a_6412_);
    crate::leanh::lean_dec(v_a_6411_);
    crate::leanh::lean_dec_ref(v_a_6410_);
    crate::leanh::lean_dec(v_a_6409_);
    crate::leanh::lean_dec_ref(v_a_6408_);
    return v_res_6417_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(
    mut v_jobs_6418_: *mut crate::leanh::LeanObject,
    mut v_a_6419_: *mut crate::leanh::LeanObject,
    mut v_a_6420_: *mut crate::leanh::LeanObject,
    mut v_a_6421_: *mut crate::leanh::LeanObject,
    mut v_a_6422_: *mut crate::leanh::LeanObject,
    mut v_a_6423_: *mut crate::leanh::LeanObject,
    mut v_a_6424_: *mut crate::leanh::LeanObject,
    mut v_a_6425_: *mut crate::leanh::LeanObject,
    mut v_a_6426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6432_: u8 = 0;
    let mut v_snd_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6437_: u8 = 0;
    let mut v_a_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6428_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
                    v_jobs_6418_,
                    v_a_6419_,
                    v_a_6420_,
                    v_a_6421_,
                    v_a_6422_,
                    v_a_6423_,
                    v_a_6424_,
                    v_a_6425_,
                    v_a_6426_,
                );
                if crate::leanh::lean_obj_tag(v___x_6428_) == 0 {
                    v_a_6429_ = crate::leanh::lean_ctor_get(v___x_6428_, 0);
                    v_isSharedCheck_6437_ = (!crate::leanh::lean_is_exclusive(v___x_6428_)) as u8;
                    if v_isSharedCheck_6437_ == 0 {
                        v___x_6431_ = v___x_6428_;
                        v_isShared_6432_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6429_);
                        crate::leanh::lean_dec(v___x_6428_);
                        v___x_6431_ = crate::leanh::lean_box(0);
                        v_isShared_6432_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6438_ = crate::leanh::lean_ctor_get(v___x_6428_, 0);
                    v_isSharedCheck_6445_ = (!crate::leanh::lean_is_exclusive(v___x_6428_)) as u8;
                    if v_isSharedCheck_6445_ == 0 {
                        v___x_6440_ = v___x_6428_;
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6438_);
                        crate::leanh::lean_dec(v___x_6428_);
                        v___x_6440_ = crate::leanh::lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6433_ = crate::leanh::lean_ctor_get(v_a_6429_, 1);
                crate::leanh::lean_inc(v_snd_6433_);
                crate::leanh::lean_dec(v_a_6429_);
                if v_isShared_6432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6431_, 0, v_snd_6433_);
                    v___x_6435_ = v___x_6431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_snd_6433_);
                    v___x_6435_ = v_reuseFailAlloc_6436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6435_;
            }
            3 => {
                if v_isShared_6441_ == 0 {
                    v___x_6443_ = v___x_6440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
                    v___x_6443_ = v_reuseFailAlloc_6444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(
    mut v_jobs_6446_: *mut crate::leanh::LeanObject,
    mut v_a_6447_: *mut crate::leanh::LeanObject,
    mut v_a_6448_: *mut crate::leanh::LeanObject,
    mut v_a_6449_: *mut crate::leanh::LeanObject,
    mut v_a_6450_: *mut crate::leanh::LeanObject,
    mut v_a_6451_: *mut crate::leanh::LeanObject,
    mut v_a_6452_: *mut crate::leanh::LeanObject,
    mut v_a_6453_: *mut crate::leanh::LeanObject,
    mut v_a_6454_: *mut crate::leanh::LeanObject,
    mut v_a_6455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6456_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(
        v_jobs_6446_,
        v_a_6447_,
        v_a_6448_,
        v_a_6449_,
        v_a_6450_,
        v_a_6451_,
        v_a_6452_,
        v_a_6453_,
        v_a_6454_,
    );
    crate::leanh::lean_dec(v_a_6454_);
    crate::leanh::lean_dec_ref(v_a_6453_);
    crate::leanh::lean_dec(v_a_6452_);
    crate::leanh::lean_dec_ref(v_a_6451_);
    crate::leanh::lean_dec(v_a_6450_);
    crate::leanh::lean_dec_ref(v_a_6449_);
    crate::leanh::lean_dec(v_a_6448_);
    crate::leanh::lean_dec_ref(v_a_6447_);
    return v_res_6456_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy(
    mut v_00_u03b1_6457_: *mut crate::leanh::LeanObject,
    mut v_jobs_6458_: *mut crate::leanh::LeanObject,
    mut v_a_6459_: *mut crate::leanh::LeanObject,
    mut v_a_6460_: *mut crate::leanh::LeanObject,
    mut v_a_6461_: *mut crate::leanh::LeanObject,
    mut v_a_6462_: *mut crate::leanh::LeanObject,
    mut v_a_6463_: *mut crate::leanh::LeanObject,
    mut v_a_6464_: *mut crate::leanh::LeanObject,
    mut v_a_6465_: *mut crate::leanh::LeanObject,
    mut v_a_6466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6468_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(
        v_jobs_6458_,
        v_a_6459_,
        v_a_6460_,
        v_a_6461_,
        v_a_6462_,
        v_a_6463_,
        v_a_6464_,
        v_a_6465_,
        v_a_6466_,
    );
    return v___x_6468_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(
    mut v_00_u03b1_6469_: *mut crate::leanh::LeanObject,
    mut v_jobs_6470_: *mut crate::leanh::LeanObject,
    mut v_a_6471_: *mut crate::leanh::LeanObject,
    mut v_a_6472_: *mut crate::leanh::LeanObject,
    mut v_a_6473_: *mut crate::leanh::LeanObject,
    mut v_a_6474_: *mut crate::leanh::LeanObject,
    mut v_a_6475_: *mut crate::leanh::LeanObject,
    mut v_a_6476_: *mut crate::leanh::LeanObject,
    mut v_a_6477_: *mut crate::leanh::LeanObject,
    mut v_a_6478_: *mut crate::leanh::LeanObject,
    mut v_a_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6480_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(
        v_00_u03b1_6469_,
        v_jobs_6470_,
        v_a_6471_,
        v_a_6472_,
        v_a_6473_,
        v_a_6474_,
        v_a_6475_,
        v_a_6476_,
        v_a_6477_,
        v_a_6478_,
    );
    crate::leanh::lean_dec(v_a_6478_);
    crate::leanh::lean_dec_ref(v_a_6477_);
    crate::leanh::lean_dec(v_a_6476_);
    crate::leanh::lean_dec_ref(v_a_6475_);
    crate::leanh::lean_dec(v_a_6474_);
    crate::leanh::lean_dec_ref(v_a_6473_);
    crate::leanh::lean_dec(v_a_6472_);
    crate::leanh::lean_dec_ref(v_a_6471_);
    return v_res_6480_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(
    mut v_as_x27_6481_: *mut crate::leanh::LeanObject,
    mut v_b_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
    mut v___y_6487_: *mut crate::leanh::LeanObject,
    mut v___y_6488_: *mut crate::leanh::LeanObject,
    mut v___y_6489_: *mut crate::leanh::LeanObject,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6499_: u8 = 0;
    let mut v___y_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: u8 = 0;
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6510_: u8 = 0;
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6514_: u8 = 0;
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: u8 = 0;
    let mut v___x_2645__overap_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut v_a_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut v_a_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6543_: u8 = 0;
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6481_) == 0 {
                    v___x_6492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6492_, 0, v_b_6482_);
                    return v___x_6492_;
                } else {
                    v_head_6493_ = crate::leanh::lean_ctor_get(v_as_x27_6481_, 0);
                    v_tail_6494_ = crate::leanh::lean_ctor_get(v_as_x27_6481_, 1);
                    v___x_6495_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6484_,
                        v___y_6486_,
                        v___y_6488_,
                        v___y_6490_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6495_) == 0 {
                        v_a_6496_ = crate::leanh::lean_ctor_get(v___x_6495_, 0);
                        v_isSharedCheck_6539_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6495_)) as u8;
                        if v_isSharedCheck_6539_ == 0 {
                            v___x_6498_ = v___x_6495_;
                            v_isShared_6499_ = v_isSharedCheck_6539_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6496_);
                            crate::leanh::lean_dec(v___x_6495_);
                            v___x_6498_ = crate::leanh::lean_box(0);
                            v_isShared_6499_ = v_isSharedCheck_6539_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_6482_);
                        v_a_6540_ = crate::leanh::lean_ctor_get(v___x_6495_, 0);
                        v_isSharedCheck_6547_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6495_)) as u8;
                        if v_isSharedCheck_6547_ == 0 {
                            v___x_6542_ = v___x_6495_;
                            v_isShared_6543_ = v_isSharedCheck_6547_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6540_);
                            crate::leanh::lean_dec(v___x_6495_);
                            v___x_6542_ = crate::leanh::lean_box(0);
                            v_isShared_6543_ = v_isSharedCheck_6547_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_6493_);
                v___x_2645__overap_6522_ = lean_task_get_own(v_head_6493_);
                crate::leanh::lean_inc(v___y_6490_);
                crate::leanh::lean_inc_ref(v___y_6489_);
                crate::leanh::lean_inc(v___y_6488_);
                crate::leanh::lean_inc_ref(v___y_6487_);
                crate::leanh::lean_inc(v___y_6486_);
                crate::leanh::lean_inc_ref(v___y_6485_);
                crate::leanh::lean_inc(v___y_6484_);
                crate::leanh::lean_inc_ref(v___y_6483_);
                v___x_6523_ = crate::leanh::lean_apply_9(
                    v___x_2645__overap_6522_,
                    v___y_6483_,
                    v___y_6484_,
                    v___y_6485_,
                    v___y_6486_,
                    v___y_6487_,
                    v___y_6488_,
                    v___y_6489_,
                    v___y_6490_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6523_) == 0 {
                    v_a_6524_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                    crate::leanh::lean_inc(v_a_6524_);
                    crate::leanh::lean_dec_ref_known(v___x_6523_, 1);
                    v___x_6525_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6484_,
                        v___y_6486_,
                        v___y_6488_,
                        v___y_6490_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6525_) == 0 {
                        crate::leanh::lean_del_object(v___x_6498_);
                        crate::leanh::lean_dec(v_a_6496_);
                        v_a_6526_ = crate::leanh::lean_ctor_get(v___x_6525_, 0);
                        v_isSharedCheck_6536_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6525_)) as u8;
                        if v_isSharedCheck_6536_ == 0 {
                            v___x_6528_ = v___x_6525_;
                            v_isShared_6529_ = v_isSharedCheck_6536_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6526_);
                            crate::leanh::lean_dec(v___x_6525_);
                            v___x_6528_ = crate::leanh::lean_box(0);
                            v_isShared_6529_ = v_isSharedCheck_6536_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6524_);
                        v_a_6537_ = crate::leanh::lean_ctor_get(v___x_6525_, 0);
                        crate::leanh::lean_inc(v_a_6537_);
                        crate::leanh::lean_dec_ref_known(v___x_6525_, 1);
                        v_a_6519_ = v_a_6537_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_6538_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                    crate::leanh::lean_inc(v_a_6538_);
                    crate::leanh::lean_dec_ref_known(v___x_6523_, 1);
                    v_a_6519_ = v_a_6538_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                if v___y_6502_ == 0 {
                    crate::leanh::lean_del_object(v___x_6498_);
                    v___x_6503_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_6496_,
                        v___y_6502_,
                        v___y_6484_,
                        v___y_6485_,
                        v___y_6486_,
                        v___y_6487_,
                        v___y_6488_,
                        v___y_6489_,
                        v___y_6490_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6503_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6503_, 1);
                        v___x_6504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6504_, 0, v___y_6501_);
                        v___x_6505_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6505_, 0, v___x_6504_);
                        crate::leanh::lean_ctor_set(v___x_6505_, 1, v_b_6482_);
                        v_as_x27_6481_ = v_tail_6494_;
                        v_b_6482_ = v___x_6505_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6501_);
                        crate::leanh::lean_dec(v_b_6482_);
                        v_a_6507_ = crate::leanh::lean_ctor_get(v___x_6503_, 0);
                        v_isSharedCheck_6514_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6503_)) as u8;
                        if v_isSharedCheck_6514_ == 0 {
                            v___x_6509_ = v___x_6503_;
                            v_isShared_6510_ = v_isSharedCheck_6514_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6507_);
                            crate::leanh::lean_dec(v___x_6503_);
                            v___x_6509_ = crate::leanh::lean_box(0);
                            v_isShared_6510_ = v_isSharedCheck_6514_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6496_);
                    crate::leanh::lean_dec(v_b_6482_);
                    if v_isShared_6499_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6498_, 1);
                        crate::leanh::lean_ctor_set(v___x_6498_, 0, v___y_6501_);
                        v___x_6516_ = v___x_6498_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6517_, 0, v___y_6501_);
                        v___x_6516_ = v_reuseFailAlloc_6517_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6510_ == 0 {
                    v___x_6512_ = v___x_6509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
                    v___x_6512_ = v_reuseFailAlloc_6513_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6512_;
            }
            5 => {
                return v___x_6516_;
            }
            6 => {
                v___x_6520_ = l_Lean_Exception_isInterrupt(v_a_6519_);
                if v___x_6520_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_6519_);
                    v___x_6521_ = l_Lean_Exception_isRuntime(v_a_6519_);
                    v___y_6501_ = v_a_6519_;
                    v___y_6502_ = v___x_6521_;
                    state = 2;
                    continue;
                } else {
                    v___y_6501_ = v_a_6519_;
                    v___y_6502_ = v___x_6520_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_6530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6530_, 0, v_a_6524_);
                crate::leanh::lean_ctor_set(v___x_6530_, 1, v_a_6526_);
                if v_isShared_6529_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6528_, 1);
                    crate::leanh::lean_ctor_set(v___x_6528_, 0, v___x_6530_);
                    v___x_6532_ = v___x_6528_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6530_);
                    v___x_6532_ = v_reuseFailAlloc_6535_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6533_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6533_, 0, v___x_6532_);
                crate::leanh::lean_ctor_set(v___x_6533_, 1, v_b_6482_);
                v_as_x27_6481_ = v_tail_6494_;
                v_b_6482_ = v___x_6533_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_6543_ == 0 {
                    v___x_6545_ = v___x_6542_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6546_, 0, v_a_6540_);
                    v___x_6545_ = v_reuseFailAlloc_6546_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(
    mut v_as_x27_6548_: *mut crate::leanh::LeanObject,
    mut v_b_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
    mut v___y_6556_: *mut crate::leanh::LeanObject,
    mut v___y_6557_: *mut crate::leanh::LeanObject,
    mut v___y_6558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6559_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(
        v_as_x27_6548_,
        v_b_6549_,
        v___y_6550_,
        v___y_6551_,
        v___y_6552_,
        v___y_6553_,
        v___y_6554_,
        v___y_6555_,
        v___y_6556_,
        v___y_6557_,
    );
    crate::leanh::lean_dec(v___y_6557_);
    crate::leanh::lean_dec_ref(v___y_6556_);
    crate::leanh::lean_dec(v___y_6555_);
    crate::leanh::lean_dec_ref(v___y_6554_);
    crate::leanh::lean_dec(v___y_6553_);
    crate::leanh::lean_dec_ref(v___y_6552_);
    crate::leanh::lean_dec(v___y_6551_);
    crate::leanh::lean_dec_ref(v___y_6550_);
    crate::leanh::lean_dec(v_as_x27_6548_);
    return v_res_6559_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
    mut v_x_6560_: *mut crate::leanh::LeanObject,
    mut v_x_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
    mut v___y_6569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6577_: u8 = 0;
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v_isSharedCheck_6592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6560_) == 0 {
                    v___x_6571_ = l_List_reverse___redArg(v_x_6561_);
                    v___x_6572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6572_, 0, v___x_6571_);
                    return v___x_6572_;
                } else {
                    v_head_6573_ = crate::leanh::lean_ctor_get(v_x_6560_, 0);
                    v_tail_6574_ = crate::leanh::lean_ctor_get(v_x_6560_, 1);
                    v_isSharedCheck_6592_ = (!crate::leanh::lean_is_exclusive(v_x_6560_)) as u8;
                    if v_isSharedCheck_6592_ == 0 {
                        v___x_6576_ = v_x_6560_;
                        v_isShared_6577_ = v_isSharedCheck_6592_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6574_);
                        crate::leanh::lean_inc(v_head_6573_);
                        crate::leanh::lean_dec(v_x_6560_);
                        v___x_6576_ = crate::leanh::lean_box(0);
                        v_isShared_6577_ = v_isSharedCheck_6592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6578_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(
                    v_head_6573_,
                    v___y_6562_,
                    v___y_6563_,
                    v___y_6564_,
                    v___y_6565_,
                    v___y_6566_,
                    v___y_6567_,
                    v___y_6568_,
                    v___y_6569_,
                );
                if crate::leanh::lean_obj_tag(v___x_6578_) == 0 {
                    v_a_6579_ = crate::leanh::lean_ctor_get(v___x_6578_, 0);
                    crate::leanh::lean_inc(v_a_6579_);
                    crate::leanh::lean_dec_ref_known(v___x_6578_, 1);
                    if v_isShared_6577_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6576_, 1, v_x_6561_);
                        crate::leanh::lean_ctor_set(v___x_6576_, 0, v_a_6579_);
                        v___x_6581_ = v___x_6576_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6583_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_a_6579_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 1, v_x_6561_);
                        v___x_6581_ = v_reuseFailAlloc_6583_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6576_);
                    crate::leanh::lean_dec(v_tail_6574_);
                    crate::leanh::lean_dec(v_x_6561_);
                    v_a_6584_ = crate::leanh::lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6591_ = (!crate::leanh::lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6578_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6584_);
                        crate::leanh::lean_dec(v___x_6578_);
                        v___x_6586_ = crate::leanh::lean_box(0);
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6560_ = v_tail_6574_;
                v_x_6561_ = v___x_6581_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6587_ == 0 {
                    v___x_6589_ = v___x_6586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(
    mut v_x_6593_: *mut crate::leanh::LeanObject,
    mut v_x_6594_: *mut crate::leanh::LeanObject,
    mut v___y_6595_: *mut crate::leanh::LeanObject,
    mut v___y_6596_: *mut crate::leanh::LeanObject,
    mut v___y_6597_: *mut crate::leanh::LeanObject,
    mut v___y_6598_: *mut crate::leanh::LeanObject,
    mut v___y_6599_: *mut crate::leanh::LeanObject,
    mut v___y_6600_: *mut crate::leanh::LeanObject,
    mut v___y_6601_: *mut crate::leanh::LeanObject,
    mut v___y_6602_: *mut crate::leanh::LeanObject,
    mut v___y_6603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6604_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
        v_x_6593_,
        v_x_6594_,
        v___y_6595_,
        v___y_6596_,
        v___y_6597_,
        v___y_6598_,
        v___y_6599_,
        v___y_6600_,
        v___y_6601_,
        v___y_6602_,
    );
    crate::leanh::lean_dec(v___y_6602_);
    crate::leanh::lean_dec_ref(v___y_6601_);
    crate::leanh::lean_dec(v___y_6600_);
    crate::leanh::lean_dec_ref(v___y_6599_);
    crate::leanh::lean_dec(v___y_6598_);
    crate::leanh::lean_dec_ref(v___y_6597_);
    crate::leanh::lean_dec(v___y_6596_);
    crate::leanh::lean_dec_ref(v___y_6595_);
    return v_res_6604_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par___redArg(
    mut v_jobs_6605_: *mut crate::leanh::LeanObject,
    mut v_a_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
    mut v_a_6608_: *mut crate::leanh::LeanObject,
    mut v_a_6609_: *mut crate::leanh::LeanObject,
    mut v_a_6610_: *mut crate::leanh::LeanObject,
    mut v_a_6611_: *mut crate::leanh::LeanObject,
    mut v_a_6612_: *mut crate::leanh::LeanObject,
    mut v_a_6613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6629_: u8 = 0;
    let mut v_a_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6615_ = lean_st_ref_get(v_a_6607_);
                v___x_6616_ = crate::leanh::lean_box(0);
                v___x_6617_ =
                    l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
                        v_jobs_6605_,
                        v___x_6616_,
                        v_a_6606_,
                        v_a_6607_,
                        v_a_6608_,
                        v_a_6609_,
                        v_a_6610_,
                        v_a_6611_,
                        v_a_6612_,
                        v_a_6613_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6617_) == 0 {
                    v_a_6618_ = crate::leanh::lean_ctor_get(v___x_6617_, 0);
                    crate::leanh::lean_inc(v_a_6618_);
                    crate::leanh::lean_dec_ref_known(v___x_6617_, 1);
                    v___x_6619_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_6618_, v___x_6616_, v_a_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_);
                    crate::leanh::lean_dec(v_a_6618_);
                    if crate::leanh::lean_obj_tag(v___x_6619_) == 0 {
                        v_a_6620_ = crate::leanh::lean_ctor_get(v___x_6619_, 0);
                        v_isSharedCheck_6629_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6619_)) as u8;
                        if v_isSharedCheck_6629_ == 0 {
                            v___x_6622_ = v___x_6619_;
                            v_isShared_6623_ = v_isSharedCheck_6629_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6620_);
                            crate::leanh::lean_dec(v___x_6619_);
                            v___x_6622_ = crate::leanh::lean_box(0);
                            v_isShared_6623_ = v_isSharedCheck_6629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6615_);
                        return v___x_6619_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6615_);
                    v_a_6630_ = crate::leanh::lean_ctor_get(v___x_6617_, 0);
                    v_isSharedCheck_6637_ = (!crate::leanh::lean_is_exclusive(v___x_6617_)) as u8;
                    if v_isSharedCheck_6637_ == 0 {
                        v___x_6632_ = v___x_6617_;
                        v_isShared_6633_ = v_isSharedCheck_6637_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6630_);
                        crate::leanh::lean_dec(v___x_6617_);
                        v___x_6632_ = crate::leanh::lean_box(0);
                        v_isShared_6633_ = v_isSharedCheck_6637_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6624_ = lean_st_ref_set(v_a_6607_, v___x_6615_);
                v___x_6625_ = l_List_reverse___redArg(v_a_6620_);
                if v_isShared_6623_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6622_, 0, v___x_6625_);
                    v___x_6627_ = v___x_6622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6628_, 0, v___x_6625_);
                    v___x_6627_ = v_reuseFailAlloc_6628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6627_;
            }
            3 => {
                if v_isShared_6633_ == 0 {
                    v___x_6635_ = v___x_6632_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6636_, 0, v_a_6630_);
                    v___x_6635_ = v_reuseFailAlloc_6636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(
    mut v_jobs_6638_: *mut crate::leanh::LeanObject,
    mut v_a_6639_: *mut crate::leanh::LeanObject,
    mut v_a_6640_: *mut crate::leanh::LeanObject,
    mut v_a_6641_: *mut crate::leanh::LeanObject,
    mut v_a_6642_: *mut crate::leanh::LeanObject,
    mut v_a_6643_: *mut crate::leanh::LeanObject,
    mut v_a_6644_: *mut crate::leanh::LeanObject,
    mut v_a_6645_: *mut crate::leanh::LeanObject,
    mut v_a_6646_: *mut crate::leanh::LeanObject,
    mut v_a_6647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6648_ = l_Lean_Elab_Tactic_TacticM_par___redArg(
        v_jobs_6638_,
        v_a_6639_,
        v_a_6640_,
        v_a_6641_,
        v_a_6642_,
        v_a_6643_,
        v_a_6644_,
        v_a_6645_,
        v_a_6646_,
    );
    crate::leanh::lean_dec(v_a_6646_);
    crate::leanh::lean_dec_ref(v_a_6645_);
    crate::leanh::lean_dec(v_a_6644_);
    crate::leanh::lean_dec_ref(v_a_6643_);
    crate::leanh::lean_dec(v_a_6642_);
    crate::leanh::lean_dec_ref(v_a_6641_);
    crate::leanh::lean_dec(v_a_6640_);
    crate::leanh::lean_dec_ref(v_a_6639_);
    return v_res_6648_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par(
    mut v_00_u03b1_6649_: *mut crate::leanh::LeanObject,
    mut v_jobs_6650_: *mut crate::leanh::LeanObject,
    mut v_a_6651_: *mut crate::leanh::LeanObject,
    mut v_a_6652_: *mut crate::leanh::LeanObject,
    mut v_a_6653_: *mut crate::leanh::LeanObject,
    mut v_a_6654_: *mut crate::leanh::LeanObject,
    mut v_a_6655_: *mut crate::leanh::LeanObject,
    mut v_a_6656_: *mut crate::leanh::LeanObject,
    mut v_a_6657_: *mut crate::leanh::LeanObject,
    mut v_a_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6660_ = l_Lean_Elab_Tactic_TacticM_par___redArg(
        v_jobs_6650_,
        v_a_6651_,
        v_a_6652_,
        v_a_6653_,
        v_a_6654_,
        v_a_6655_,
        v_a_6656_,
        v_a_6657_,
        v_a_6658_,
    );
    return v___x_6660_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par___boxed(
    mut v_00_u03b1_6661_: *mut crate::leanh::LeanObject,
    mut v_jobs_6662_: *mut crate::leanh::LeanObject,
    mut v_a_6663_: *mut crate::leanh::LeanObject,
    mut v_a_6664_: *mut crate::leanh::LeanObject,
    mut v_a_6665_: *mut crate::leanh::LeanObject,
    mut v_a_6666_: *mut crate::leanh::LeanObject,
    mut v_a_6667_: *mut crate::leanh::LeanObject,
    mut v_a_6668_: *mut crate::leanh::LeanObject,
    mut v_a_6669_: *mut crate::leanh::LeanObject,
    mut v_a_6670_: *mut crate::leanh::LeanObject,
    mut v_a_6671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6672_ = l_Lean_Elab_Tactic_TacticM_par(
        v_00_u03b1_6661_,
        v_jobs_6662_,
        v_a_6663_,
        v_a_6664_,
        v_a_6665_,
        v_a_6666_,
        v_a_6667_,
        v_a_6668_,
        v_a_6669_,
        v_a_6670_,
    );
    crate::leanh::lean_dec(v_a_6670_);
    crate::leanh::lean_dec_ref(v_a_6669_);
    crate::leanh::lean_dec(v_a_6668_);
    crate::leanh::lean_dec_ref(v_a_6667_);
    crate::leanh::lean_dec(v_a_6666_);
    crate::leanh::lean_dec_ref(v_a_6665_);
    crate::leanh::lean_dec(v_a_6664_);
    crate::leanh::lean_dec_ref(v_a_6663_);
    return v_res_6672_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(
    mut v_00_u03b1_6673_: *mut crate::leanh::LeanObject,
    mut v_x_6674_: *mut crate::leanh::LeanObject,
    mut v_x_6675_: *mut crate::leanh::LeanObject,
    mut v___y_6676_: *mut crate::leanh::LeanObject,
    mut v___y_6677_: *mut crate::leanh::LeanObject,
    mut v___y_6678_: *mut crate::leanh::LeanObject,
    mut v___y_6679_: *mut crate::leanh::LeanObject,
    mut v___y_6680_: *mut crate::leanh::LeanObject,
    mut v___y_6681_: *mut crate::leanh::LeanObject,
    mut v___y_6682_: *mut crate::leanh::LeanObject,
    mut v___y_6683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6685_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
        v_x_6674_,
        v_x_6675_,
        v___y_6676_,
        v___y_6677_,
        v___y_6678_,
        v___y_6679_,
        v___y_6680_,
        v___y_6681_,
        v___y_6682_,
        v___y_6683_,
    );
    return v___x_6685_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(
    mut v_00_u03b1_6686_: *mut crate::leanh::LeanObject,
    mut v_x_6687_: *mut crate::leanh::LeanObject,
    mut v_x_6688_: *mut crate::leanh::LeanObject,
    mut v___y_6689_: *mut crate::leanh::LeanObject,
    mut v___y_6690_: *mut crate::leanh::LeanObject,
    mut v___y_6691_: *mut crate::leanh::LeanObject,
    mut v___y_6692_: *mut crate::leanh::LeanObject,
    mut v___y_6693_: *mut crate::leanh::LeanObject,
    mut v___y_6694_: *mut crate::leanh::LeanObject,
    mut v___y_6695_: *mut crate::leanh::LeanObject,
    mut v___y_6696_: *mut crate::leanh::LeanObject,
    mut v___y_6697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6698_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(
        v_00_u03b1_6686_,
        v_x_6687_,
        v_x_6688_,
        v___y_6689_,
        v___y_6690_,
        v___y_6691_,
        v___y_6692_,
        v___y_6693_,
        v___y_6694_,
        v___y_6695_,
        v___y_6696_,
    );
    crate::leanh::lean_dec(v___y_6696_);
    crate::leanh::lean_dec_ref(v___y_6695_);
    crate::leanh::lean_dec(v___y_6694_);
    crate::leanh::lean_dec_ref(v___y_6693_);
    crate::leanh::lean_dec(v___y_6692_);
    crate::leanh::lean_dec_ref(v___y_6691_);
    crate::leanh::lean_dec(v___y_6690_);
    crate::leanh::lean_dec_ref(v___y_6689_);
    return v_res_6698_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(
    mut v_00_u03b1_6699_: *mut crate::leanh::LeanObject,
    mut v_as_6700_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6701_: *mut crate::leanh::LeanObject,
    mut v_b_6702_: *mut crate::leanh::LeanObject,
    mut v_a_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
    mut v___y_6705_: *mut crate::leanh::LeanObject,
    mut v___y_6706_: *mut crate::leanh::LeanObject,
    mut v___y_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v___y_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
    mut v___y_6711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6713_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(
        v_as_x27_6701_,
        v_b_6702_,
        v___y_6704_,
        v___y_6705_,
        v___y_6706_,
        v___y_6707_,
        v___y_6708_,
        v___y_6709_,
        v___y_6710_,
        v___y_6711_,
    );
    return v___x_6713_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(
    mut v_00_u03b1_6714_: *mut crate::leanh::LeanObject,
    mut v_as_6715_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6716_: *mut crate::leanh::LeanObject,
    mut v_b_6717_: *mut crate::leanh::LeanObject,
    mut v_a_6718_: *mut crate::leanh::LeanObject,
    mut v___y_6719_: *mut crate::leanh::LeanObject,
    mut v___y_6720_: *mut crate::leanh::LeanObject,
    mut v___y_6721_: *mut crate::leanh::LeanObject,
    mut v___y_6722_: *mut crate::leanh::LeanObject,
    mut v___y_6723_: *mut crate::leanh::LeanObject,
    mut v___y_6724_: *mut crate::leanh::LeanObject,
    mut v___y_6725_: *mut crate::leanh::LeanObject,
    mut v___y_6726_: *mut crate::leanh::LeanObject,
    mut v___y_6727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6728_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(
        v_00_u03b1_6714_,
        v_as_6715_,
        v_as_x27_6716_,
        v_b_6717_,
        v_a_6718_,
        v___y_6719_,
        v___y_6720_,
        v___y_6721_,
        v___y_6722_,
        v___y_6723_,
        v___y_6724_,
        v___y_6725_,
        v___y_6726_,
    );
    crate::leanh::lean_dec(v___y_6726_);
    crate::leanh::lean_dec_ref(v___y_6725_);
    crate::leanh::lean_dec(v___y_6724_);
    crate::leanh::lean_dec_ref(v___y_6723_);
    crate::leanh::lean_dec(v___y_6722_);
    crate::leanh::lean_dec_ref(v___y_6721_);
    crate::leanh::lean_dec(v___y_6720_);
    crate::leanh::lean_dec_ref(v___y_6719_);
    crate::leanh::lean_dec(v_as_x27_6716_);
    crate::leanh::lean_dec(v_as_6715_);
    return v_res_6728_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(
    mut v_as_x27_6729_: *mut crate::leanh::LeanObject,
    mut v_b_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
    mut v___y_6737_: *mut crate::leanh::LeanObject,
    mut v___y_6738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330__overap_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___y_6756_: u8 = 0;
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: u8 = 0;
    let mut v___x_6773_: u8 = 0;
    let mut v_isSharedCheck_6774_: u8 = 0;
    let mut v_a_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6778_: u8 = 0;
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6729_) == 0 {
                    v___x_6740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6740_, 0, v_b_6730_);
                    return v___x_6740_;
                } else {
                    v_head_6741_ = crate::leanh::lean_ctor_get(v_as_x27_6729_, 0);
                    v_tail_6742_ = crate::leanh::lean_ctor_get(v_as_x27_6729_, 1);
                    v___x_6743_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6732_,
                        v___y_6734_,
                        v___y_6736_,
                        v___y_6738_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6743_) == 0 {
                        v_a_6744_ = crate::leanh::lean_ctor_get(v___x_6743_, 0);
                        crate::leanh::lean_inc(v_a_6744_);
                        crate::leanh::lean_dec_ref_known(v___x_6743_, 1);
                        crate::leanh::lean_inc(v_head_6741_);
                        v___x_2330__overap_6745_ = lean_task_get_own(v_head_6741_);
                        crate::leanh::lean_inc(v___y_6738_);
                        crate::leanh::lean_inc_ref(v___y_6737_);
                        crate::leanh::lean_inc(v___y_6736_);
                        crate::leanh::lean_inc_ref(v___y_6735_);
                        crate::leanh::lean_inc(v___y_6734_);
                        crate::leanh::lean_inc_ref(v___y_6733_);
                        crate::leanh::lean_inc(v___y_6732_);
                        crate::leanh::lean_inc_ref(v___y_6731_);
                        v___x_6746_ = crate::leanh::lean_apply_9(
                            v___x_2330__overap_6745_,
                            v___y_6731_,
                            v___y_6732_,
                            v___y_6733_,
                            v___y_6734_,
                            v___y_6735_,
                            v___y_6736_,
                            v___y_6737_,
                            v___y_6738_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6746_) == 0 {
                            crate::leanh::lean_dec(v_a_6744_);
                            v_a_6747_ = crate::leanh::lean_ctor_get(v___x_6746_, 0);
                            crate::leanh::lean_inc(v_a_6747_);
                            crate::leanh::lean_dec_ref_known(v___x_6746_, 1);
                            v___x_6748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6748_, 0, v_a_6747_);
                            v___x_6749_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6749_, 0, v___x_6748_);
                            crate::leanh::lean_ctor_set(v___x_6749_, 1, v_b_6730_);
                            v_as_x27_6729_ = v_tail_6742_;
                            v_b_6730_ = v___x_6749_;
                            state = 0;
                            continue;
                        } else {
                            v_a_6751_ = crate::leanh::lean_ctor_get(v___x_6746_, 0);
                            v_isSharedCheck_6774_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6746_)) as u8;
                            if v_isSharedCheck_6774_ == 0 {
                                v___x_6753_ = v___x_6746_;
                                v_isShared_6754_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6751_);
                                crate::leanh::lean_dec(v___x_6746_);
                                v___x_6753_ = crate::leanh::lean_box(0);
                                v_isShared_6754_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_6730_);
                        v_a_6775_ = crate::leanh::lean_ctor_get(v___x_6743_, 0);
                        v_isSharedCheck_6782_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6743_)) as u8;
                        if v_isSharedCheck_6782_ == 0 {
                            v___x_6777_ = v___x_6743_;
                            v_isShared_6778_ = v_isSharedCheck_6782_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6775_);
                            crate::leanh::lean_dec(v___x_6743_);
                            v___x_6777_ = crate::leanh::lean_box(0);
                            v_isShared_6778_ = v_isSharedCheck_6782_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6772_ = l_Lean_Exception_isInterrupt(v_a_6751_);
                if v___x_6772_ == 0 {
                    crate::leanh::lean_inc(v_a_6751_);
                    v___x_6773_ = l_Lean_Exception_isRuntime(v_a_6751_);
                    v___y_6756_ = v___x_6773_;
                    state = 2;
                    continue;
                } else {
                    v___y_6756_ = v___x_6772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_6756_ == 0 {
                    crate::leanh::lean_del_object(v___x_6753_);
                    v___x_6757_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_6744_,
                        v___y_6756_,
                        v___y_6732_,
                        v___y_6733_,
                        v___y_6734_,
                        v___y_6735_,
                        v___y_6736_,
                        v___y_6737_,
                        v___y_6738_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6757_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6757_, 1);
                        v___x_6758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6758_, 0, v_a_6751_);
                        v___x_6759_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6759_, 0, v___x_6758_);
                        crate::leanh::lean_ctor_set(v___x_6759_, 1, v_b_6730_);
                        v_as_x27_6729_ = v_tail_6742_;
                        v_b_6730_ = v___x_6759_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6751_);
                        crate::leanh::lean_dec(v_b_6730_);
                        v_a_6761_ = crate::leanh::lean_ctor_get(v___x_6757_, 0);
                        v_isSharedCheck_6768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6757_)) as u8;
                        if v_isSharedCheck_6768_ == 0 {
                            v___x_6763_ = v___x_6757_;
                            v_isShared_6764_ = v_isSharedCheck_6768_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6761_);
                            crate::leanh::lean_dec(v___x_6757_);
                            v___x_6763_ = crate::leanh::lean_box(0);
                            v_isShared_6764_ = v_isSharedCheck_6768_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6744_);
                    crate::leanh::lean_dec(v_b_6730_);
                    if v_isShared_6754_ == 0 {
                        v___x_6770_ = v___x_6753_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6751_);
                        v___x_6770_ = v_reuseFailAlloc_6771_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6764_ == 0 {
                    v___x_6766_ = v___x_6763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6761_);
                    v___x_6766_ = v_reuseFailAlloc_6767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6766_;
            }
            5 => {
                return v___x_6770_;
            }
            6 => {
                if v_isShared_6778_ == 0 {
                    v___x_6780_ = v___x_6777_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6781_, 0, v_a_6775_);
                    v___x_6780_ = v_reuseFailAlloc_6781_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg___boxed(
    mut v_as_x27_6783_: *mut crate::leanh::LeanObject,
    mut v_b_6784_: *mut crate::leanh::LeanObject,
    mut v___y_6785_: *mut crate::leanh::LeanObject,
    mut v___y_6786_: *mut crate::leanh::LeanObject,
    mut v___y_6787_: *mut crate::leanh::LeanObject,
    mut v___y_6788_: *mut crate::leanh::LeanObject,
    mut v___y_6789_: *mut crate::leanh::LeanObject,
    mut v___y_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6794_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(
        v_as_x27_6783_,
        v_b_6784_,
        v___y_6785_,
        v___y_6786_,
        v___y_6787_,
        v___y_6788_,
        v___y_6789_,
        v___y_6790_,
        v___y_6791_,
        v___y_6792_,
    );
    crate::leanh::lean_dec(v___y_6792_);
    crate::leanh::lean_dec_ref(v___y_6791_);
    crate::leanh::lean_dec(v___y_6790_);
    crate::leanh::lean_dec_ref(v___y_6789_);
    crate::leanh::lean_dec(v___y_6788_);
    crate::leanh::lean_dec_ref(v___y_6787_);
    crate::leanh::lean_dec(v___y_6786_);
    crate::leanh::lean_dec_ref(v___y_6785_);
    crate::leanh::lean_dec(v_as_x27_6783_);
    return v_res_6794_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27___redArg(
    mut v_jobs_6795_: *mut crate::leanh::LeanObject,
    mut v_a_6796_: *mut crate::leanh::LeanObject,
    mut v_a_6797_: *mut crate::leanh::LeanObject,
    mut v_a_6798_: *mut crate::leanh::LeanObject,
    mut v_a_6799_: *mut crate::leanh::LeanObject,
    mut v_a_6800_: *mut crate::leanh::LeanObject,
    mut v_a_6801_: *mut crate::leanh::LeanObject,
    mut v_a_6802_: *mut crate::leanh::LeanObject,
    mut v_a_6803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6813_: u8 = 0;
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6819_: u8 = 0;
    let mut v_a_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6823_: u8 = 0;
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6805_ = lean_st_ref_get(v_a_6797_);
                v___x_6806_ = crate::leanh::lean_box(0);
                v___x_6807_ =
                    l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
                        v_jobs_6795_,
                        v___x_6806_,
                        v_a_6796_,
                        v_a_6797_,
                        v_a_6798_,
                        v_a_6799_,
                        v_a_6800_,
                        v_a_6801_,
                        v_a_6802_,
                        v_a_6803_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6807_) == 0 {
                    v_a_6808_ = crate::leanh::lean_ctor_get(v___x_6807_, 0);
                    crate::leanh::lean_inc(v_a_6808_);
                    crate::leanh::lean_dec_ref_known(v___x_6807_, 1);
                    v___x_6809_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_a_6808_, v___x_6806_, v_a_6796_, v_a_6797_, v_a_6798_, v_a_6799_, v_a_6800_, v_a_6801_, v_a_6802_, v_a_6803_);
                    crate::leanh::lean_dec(v_a_6808_);
                    if crate::leanh::lean_obj_tag(v___x_6809_) == 0 {
                        v_a_6810_ = crate::leanh::lean_ctor_get(v___x_6809_, 0);
                        v_isSharedCheck_6819_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6809_)) as u8;
                        if v_isSharedCheck_6819_ == 0 {
                            v___x_6812_ = v___x_6809_;
                            v_isShared_6813_ = v_isSharedCheck_6819_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6810_);
                            crate::leanh::lean_dec(v___x_6809_);
                            v___x_6812_ = crate::leanh::lean_box(0);
                            v_isShared_6813_ = v_isSharedCheck_6819_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6805_);
                        return v___x_6809_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6805_);
                    v_a_6820_ = crate::leanh::lean_ctor_get(v___x_6807_, 0);
                    v_isSharedCheck_6827_ = (!crate::leanh::lean_is_exclusive(v___x_6807_)) as u8;
                    if v_isSharedCheck_6827_ == 0 {
                        v___x_6822_ = v___x_6807_;
                        v_isShared_6823_ = v_isSharedCheck_6827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6820_);
                        crate::leanh::lean_dec(v___x_6807_);
                        v___x_6822_ = crate::leanh::lean_box(0);
                        v_isShared_6823_ = v_isSharedCheck_6827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6814_ = lean_st_ref_set(v_a_6797_, v___x_6805_);
                v___x_6815_ = l_List_reverse___redArg(v_a_6810_);
                if v_isShared_6813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6812_, 0, v___x_6815_);
                    v___x_6817_ = v___x_6812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6818_, 0, v___x_6815_);
                    v___x_6817_ = v_reuseFailAlloc_6818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6817_;
            }
            3 => {
                if v_isShared_6823_ == 0 {
                    v___x_6825_ = v___x_6822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_a_6820_);
                    v___x_6825_ = v_reuseFailAlloc_6826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27___redArg___boxed(
    mut v_jobs_6828_: *mut crate::leanh::LeanObject,
    mut v_a_6829_: *mut crate::leanh::LeanObject,
    mut v_a_6830_: *mut crate::leanh::LeanObject,
    mut v_a_6831_: *mut crate::leanh::LeanObject,
    mut v_a_6832_: *mut crate::leanh::LeanObject,
    mut v_a_6833_: *mut crate::leanh::LeanObject,
    mut v_a_6834_: *mut crate::leanh::LeanObject,
    mut v_a_6835_: *mut crate::leanh::LeanObject,
    mut v_a_6836_: *mut crate::leanh::LeanObject,
    mut v_a_6837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6838_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(
        v_jobs_6828_,
        v_a_6829_,
        v_a_6830_,
        v_a_6831_,
        v_a_6832_,
        v_a_6833_,
        v_a_6834_,
        v_a_6835_,
        v_a_6836_,
    );
    crate::leanh::lean_dec(v_a_6836_);
    crate::leanh::lean_dec_ref(v_a_6835_);
    crate::leanh::lean_dec(v_a_6834_);
    crate::leanh::lean_dec_ref(v_a_6833_);
    crate::leanh::lean_dec(v_a_6832_);
    crate::leanh::lean_dec_ref(v_a_6831_);
    crate::leanh::lean_dec(v_a_6830_);
    crate::leanh::lean_dec_ref(v_a_6829_);
    return v_res_6838_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27(
    mut v_00_u03b1_6839_: *mut crate::leanh::LeanObject,
    mut v_jobs_6840_: *mut crate::leanh::LeanObject,
    mut v_a_6841_: *mut crate::leanh::LeanObject,
    mut v_a_6842_: *mut crate::leanh::LeanObject,
    mut v_a_6843_: *mut crate::leanh::LeanObject,
    mut v_a_6844_: *mut crate::leanh::LeanObject,
    mut v_a_6845_: *mut crate::leanh::LeanObject,
    mut v_a_6846_: *mut crate::leanh::LeanObject,
    mut v_a_6847_: *mut crate::leanh::LeanObject,
    mut v_a_6848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6850_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(
        v_jobs_6840_,
        v_a_6841_,
        v_a_6842_,
        v_a_6843_,
        v_a_6844_,
        v_a_6845_,
        v_a_6846_,
        v_a_6847_,
        v_a_6848_,
    );
    return v___x_6850_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27___boxed(
    mut v_00_u03b1_6851_: *mut crate::leanh::LeanObject,
    mut v_jobs_6852_: *mut crate::leanh::LeanObject,
    mut v_a_6853_: *mut crate::leanh::LeanObject,
    mut v_a_6854_: *mut crate::leanh::LeanObject,
    mut v_a_6855_: *mut crate::leanh::LeanObject,
    mut v_a_6856_: *mut crate::leanh::LeanObject,
    mut v_a_6857_: *mut crate::leanh::LeanObject,
    mut v_a_6858_: *mut crate::leanh::LeanObject,
    mut v_a_6859_: *mut crate::leanh::LeanObject,
    mut v_a_6860_: *mut crate::leanh::LeanObject,
    mut v_a_6861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6862_ = l_Lean_Elab_Tactic_TacticM_par_x27(
        v_00_u03b1_6851_,
        v_jobs_6852_,
        v_a_6853_,
        v_a_6854_,
        v_a_6855_,
        v_a_6856_,
        v_a_6857_,
        v_a_6858_,
        v_a_6859_,
        v_a_6860_,
    );
    crate::leanh::lean_dec(v_a_6860_);
    crate::leanh::lean_dec_ref(v_a_6859_);
    crate::leanh::lean_dec(v_a_6858_);
    crate::leanh::lean_dec_ref(v_a_6857_);
    crate::leanh::lean_dec(v_a_6856_);
    crate::leanh::lean_dec_ref(v_a_6855_);
    crate::leanh::lean_dec(v_a_6854_);
    crate::leanh::lean_dec_ref(v_a_6853_);
    return v_res_6862_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(
    mut v_00_u03b1_6863_: *mut crate::leanh::LeanObject,
    mut v_as_6864_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6865_: *mut crate::leanh::LeanObject,
    mut v_b_6866_: *mut crate::leanh::LeanObject,
    mut v_a_6867_: *mut crate::leanh::LeanObject,
    mut v___y_6868_: *mut crate::leanh::LeanObject,
    mut v___y_6869_: *mut crate::leanh::LeanObject,
    mut v___y_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6877_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(
        v_as_x27_6865_,
        v_b_6866_,
        v___y_6868_,
        v___y_6869_,
        v___y_6870_,
        v___y_6871_,
        v___y_6872_,
        v___y_6873_,
        v___y_6874_,
        v___y_6875_,
    );
    return v___x_6877_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___boxed(
    mut v_00_u03b1_6878_: *mut crate::leanh::LeanObject,
    mut v_as_6879_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6880_: *mut crate::leanh::LeanObject,
    mut v_b_6881_: *mut crate::leanh::LeanObject,
    mut v_a_6882_: *mut crate::leanh::LeanObject,
    mut v___y_6883_: *mut crate::leanh::LeanObject,
    mut v___y_6884_: *mut crate::leanh::LeanObject,
    mut v___y_6885_: *mut crate::leanh::LeanObject,
    mut v___y_6886_: *mut crate::leanh::LeanObject,
    mut v___y_6887_: *mut crate::leanh::LeanObject,
    mut v___y_6888_: *mut crate::leanh::LeanObject,
    mut v___y_6889_: *mut crate::leanh::LeanObject,
    mut v___y_6890_: *mut crate::leanh::LeanObject,
    mut v___y_6891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6892_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(
        v_00_u03b1_6878_,
        v_as_6879_,
        v_as_x27_6880_,
        v_b_6881_,
        v_a_6882_,
        v___y_6883_,
        v___y_6884_,
        v___y_6885_,
        v___y_6886_,
        v___y_6887_,
        v___y_6888_,
        v___y_6889_,
        v___y_6890_,
    );
    crate::leanh::lean_dec(v___y_6890_);
    crate::leanh::lean_dec_ref(v___y_6889_);
    crate::leanh::lean_dec(v___y_6888_);
    crate::leanh::lean_dec_ref(v___y_6887_);
    crate::leanh::lean_dec(v___y_6886_);
    crate::leanh::lean_dec_ref(v___y_6885_);
    crate::leanh::lean_dec(v___y_6884_);
    crate::leanh::lean_dec_ref(v___y_6883_);
    crate::leanh::lean_dec(v_as_x27_6880_);
    crate::leanh::lean_dec(v_as_6879_);
    return v_res_6892_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(
    mut v_a_6893_: *mut crate::leanh::LeanObject,
    mut v___x_6894_: *mut crate::leanh::LeanObject,
    mut v_____r_6895_: *mut crate::leanh::LeanObject,
    mut v___y_6896_: *mut crate::leanh::LeanObject,
    mut v___y_6897_: *mut crate::leanh::LeanObject,
    mut v___y_6898_: *mut crate::leanh::LeanObject,
    mut v___y_6899_: *mut crate::leanh::LeanObject,
    mut v___y_6900_: *mut crate::leanh::LeanObject,
    mut v___y_6901_: *mut crate::leanh::LeanObject,
    mut v___y_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6905_, 0, v_a_6893_);
    v___x_6906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6906_, 0, v___x_6905_);
    crate::leanh::lean_ctor_set(v___x_6906_, 1, v___x_6894_);
    v___x_6907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6907_, 0, v___x_6906_);
    v___x_6908_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6908_, 0, v___x_6907_);
    return v___x_6908_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_6909_: *mut crate::leanh::LeanObject,
    mut v___x_6910_: *mut crate::leanh::LeanObject,
    mut v_____r_6911_: *mut crate::leanh::LeanObject,
    mut v___y_6912_: *mut crate::leanh::LeanObject,
    mut v___y_6913_: *mut crate::leanh::LeanObject,
    mut v___y_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
    mut v___y_6916_: *mut crate::leanh::LeanObject,
    mut v___y_6917_: *mut crate::leanh::LeanObject,
    mut v___y_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
    mut v___y_6920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6921_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6909_, v___x_6910_, v_____r_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_);
    crate::leanh::lean_dec(v___y_6919_);
    crate::leanh::lean_dec_ref(v___y_6918_);
    crate::leanh::lean_dec(v___y_6917_);
    crate::leanh::lean_dec_ref(v___y_6916_);
    crate::leanh::lean_dec(v___y_6915_);
    crate::leanh::lean_dec_ref(v___y_6914_);
    crate::leanh::lean_dec(v___y_6913_);
    crate::leanh::lean_dec_ref(v___y_6912_);
    return v_res_6921_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(
    mut v_cancel_6922_: u8,
    mut v_fst_6923_: *mut crate::leanh::LeanObject,
    mut v_a_6924_: *mut crate::leanh::LeanObject,
    mut v_b_6925_: *mut crate::leanh::LeanObject,
    mut v___y_6926_: *mut crate::leanh::LeanObject,
    mut v___y_6927_: *mut crate::leanh::LeanObject,
    mut v___y_6928_: *mut crate::leanh::LeanObject,
    mut v___y_6929_: *mut crate::leanh::LeanObject,
    mut v___y_6930_: *mut crate::leanh::LeanObject,
    mut v___y_6931_: *mut crate::leanh::LeanObject,
    mut v___y_6932_: *mut crate::leanh::LeanObject,
    mut v___y_6933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v_a_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6951_: u8 = 0;
    let mut v_a_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6972_: u8 = 0;
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6975_: u8 = 0;
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6981_: u8 = 0;
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6985_: u8 = 0;
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: u8 = 0;
    let mut v___x_6990_: u8 = 0;
    let mut v_isSharedCheck_6991_: u8 = 0;
    let mut v_a_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6995_: u8 = 0;
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6924_) == 0 {
                    crate::leanh::lean_dec_ref(v_fst_6923_);
                    v___x_6935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6935_, 0, v_b_6925_);
                    return v___x_6935_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_6925_);
                    v___x_6936_ = l_IO_waitAny_x27___redArg(v_a_6924_);
                    v_fst_6937_ = crate::leanh::lean_ctor_get(v___x_6936_, 0);
                    crate::leanh::lean_inc(v_fst_6937_);
                    v_snd_6938_ = crate::leanh::lean_ctor_get(v___x_6936_, 1);
                    crate::leanh::lean_inc(v_snd_6938_);
                    crate::leanh::lean_dec_ref(v___x_6936_);
                    v___x_6960_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6927_,
                        v___y_6929_,
                        v___y_6931_,
                        v___y_6933_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6960_) == 0 {
                        v_a_6961_ = crate::leanh::lean_ctor_get(v___x_6960_, 0);
                        crate::leanh::lean_inc(v_a_6961_);
                        crate::leanh::lean_dec_ref_known(v___x_6960_, 1);
                        v___x_6962_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v___y_6933_);
                        crate::leanh::lean_inc_ref(v___y_6932_);
                        crate::leanh::lean_inc(v___y_6931_);
                        crate::leanh::lean_inc_ref(v___y_6930_);
                        crate::leanh::lean_inc(v___y_6929_);
                        crate::leanh::lean_inc_ref(v___y_6928_);
                        crate::leanh::lean_inc(v___y_6927_);
                        crate::leanh::lean_inc_ref(v___y_6926_);
                        v___x_6963_ = crate::leanh::lean_apply_9(
                            v_fst_6937_,
                            v___y_6926_,
                            v___y_6927_,
                            v___y_6928_,
                            v___y_6929_,
                            v___y_6930_,
                            v___y_6931_,
                            v___y_6932_,
                            v___y_6933_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6963_) == 0 {
                            crate::leanh::lean_dec(v_a_6961_);
                            if v_cancel_6922_ == 0 {
                                v_a_6964_ = crate::leanh::lean_ctor_get(v___x_6963_, 0);
                                crate::leanh::lean_inc(v_a_6964_);
                                crate::leanh::lean_dec_ref_known(v___x_6963_, 1);
                                v___x_6965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6964_, v___x_6962_, v___x_6962_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_);
                                v___y_6940_ = v___x_6965_;
                                state = 1;
                                continue;
                            } else {
                                v_a_6966_ = crate::leanh::lean_ctor_get(v___x_6963_, 0);
                                crate::leanh::lean_inc(v_a_6966_);
                                crate::leanh::lean_dec_ref_known(v___x_6963_, 1);
                                crate::leanh::lean_inc_ref(v_fst_6923_);
                                v___x_6967_ = crate::leanh::lean_apply_1(
                                    v_fst_6923_,
                                    crate::leanh::lean_box(0),
                                );
                                v___x_6968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6966_, v___x_6962_, v___x_6967_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_);
                                v___y_6940_ = v___x_6968_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6969_ = crate::leanh::lean_ctor_get(v___x_6963_, 0);
                            v_isSharedCheck_6991_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6963_)) as u8;
                            if v_isSharedCheck_6991_ == 0 {
                                v___x_6971_ = v___x_6963_;
                                v_isShared_6972_ = v_isSharedCheck_6991_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6969_);
                                crate::leanh::lean_dec(v___x_6963_);
                                v___x_6971_ = crate::leanh::lean_box(0);
                                v_isShared_6972_ = v_isSharedCheck_6991_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_6938_);
                        crate::leanh::lean_dec(v_fst_6937_);
                        crate::leanh::lean_dec_ref(v_fst_6923_);
                        v_a_6992_ = crate::leanh::lean_ctor_get(v___x_6960_, 0);
                        v_isSharedCheck_6999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6960_)) as u8;
                        if v_isSharedCheck_6999_ == 0 {
                            v___x_6994_ = v___x_6960_;
                            v_isShared_6995_ = v_isSharedCheck_6999_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6992_);
                            crate::leanh::lean_dec(v___x_6960_);
                            v___x_6994_ = crate::leanh::lean_box(0);
                            v_isShared_6995_ = v_isSharedCheck_6999_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6940_) == 0 {
                    v_a_6941_ = crate::leanh::lean_ctor_get(v___y_6940_, 0);
                    v_isSharedCheck_6951_ = (!crate::leanh::lean_is_exclusive(v___y_6940_)) as u8;
                    if v_isSharedCheck_6951_ == 0 {
                        v___x_6943_ = v___y_6940_;
                        v_isShared_6944_ = v_isSharedCheck_6951_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6941_);
                        crate::leanh::lean_dec(v___y_6940_);
                        v___x_6943_ = crate::leanh::lean_box(0);
                        v_isShared_6944_ = v_isSharedCheck_6951_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_6938_);
                    crate::leanh::lean_dec_ref(v_fst_6923_);
                    v_a_6952_ = crate::leanh::lean_ctor_get(v___y_6940_, 0);
                    v_isSharedCheck_6959_ = (!crate::leanh::lean_is_exclusive(v___y_6940_)) as u8;
                    if v_isSharedCheck_6959_ == 0 {
                        v___x_6954_ = v___y_6940_;
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6952_);
                        crate::leanh::lean_dec(v___y_6940_);
                        v___x_6954_ = crate::leanh::lean_box(0);
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6941_) == 0 {
                    crate::leanh::lean_dec(v_snd_6938_);
                    crate::leanh::lean_dec_ref(v_fst_6923_);
                    v_a_6945_ = crate::leanh::lean_ctor_get(v_a_6941_, 0);
                    crate::leanh::lean_inc(v_a_6945_);
                    crate::leanh::lean_dec_ref_known(v_a_6941_, 1);
                    if v_isShared_6944_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6943_, 0, v_a_6945_);
                        v___x_6947_ = v___x_6943_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_a_6945_);
                        v___x_6947_ = v_reuseFailAlloc_6948_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6943_);
                    v_a_6949_ = crate::leanh::lean_ctor_get(v_a_6941_, 0);
                    crate::leanh::lean_inc(v_a_6949_);
                    crate::leanh::lean_dec_ref_known(v_a_6941_, 1);
                    v_a_6924_ = v_snd_6938_;
                    v_b_6925_ = v_a_6949_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_6947_;
            }
            4 => {
                if v_isShared_6955_ == 0 {
                    v___x_6957_ = v___x_6954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
                    v___x_6957_ = v_reuseFailAlloc_6958_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6957_;
            }
            6 => {
                v___x_6973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                v___x_6989_ = l_Lean_Exception_isInterrupt(v_a_6969_);
                if v___x_6989_ == 0 {
                    crate::leanh::lean_inc(v_a_6969_);
                    v___x_6990_ = l_Lean_Exception_isRuntime(v_a_6969_);
                    v___y_6975_ = v___x_6990_;
                    state = 7;
                    continue;
                } else {
                    v___y_6975_ = v___x_6989_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_6975_ == 0 {
                    crate::leanh::lean_del_object(v___x_6971_);
                    crate::leanh::lean_dec(v_a_6969_);
                    v___x_6976_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_6961_,
                        v___y_6975_,
                        v___y_6927_,
                        v___y_6928_,
                        v___y_6929_,
                        v___y_6930_,
                        v___y_6931_,
                        v___y_6932_,
                        v___y_6933_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6976_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6976_, 1);
                        v_a_6924_ = v_snd_6938_;
                        v_b_6925_ = v___x_6973_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_6938_);
                        crate::leanh::lean_dec_ref(v_fst_6923_);
                        v_a_6978_ = crate::leanh::lean_ctor_get(v___x_6976_, 0);
                        v_isSharedCheck_6985_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6976_)) as u8;
                        if v_isSharedCheck_6985_ == 0 {
                            v___x_6980_ = v___x_6976_;
                            v_isShared_6981_ = v_isSharedCheck_6985_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6978_);
                            crate::leanh::lean_dec(v___x_6976_);
                            v___x_6980_ = crate::leanh::lean_box(0);
                            v_isShared_6981_ = v_isSharedCheck_6985_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6961_);
                    crate::leanh::lean_dec(v_snd_6938_);
                    crate::leanh::lean_dec_ref(v_fst_6923_);
                    if v_isShared_6972_ == 0 {
                        v___x_6987_ = v___x_6971_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6988_, 0, v_a_6969_);
                        v___x_6987_ = v_reuseFailAlloc_6988_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_6981_ == 0 {
                    v___x_6983_ = v___x_6980_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_a_6978_);
                    v___x_6983_ = v_reuseFailAlloc_6984_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6983_;
            }
            10 => {
                return v___x_6987_;
            }
            11 => {
                if v_isShared_6995_ == 0 {
                    v___x_6997_ = v___x_6994_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6998_, 0, v_a_6992_);
                    v___x_6997_ = v_reuseFailAlloc_6998_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(
    mut v_cancel_7000_: *mut crate::leanh::LeanObject,
    mut v_fst_7001_: *mut crate::leanh::LeanObject,
    mut v_a_7002_: *mut crate::leanh::LeanObject,
    mut v_b_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v___y_7005_: *mut crate::leanh::LeanObject,
    mut v___y_7006_: *mut crate::leanh::LeanObject,
    mut v___y_7007_: *mut crate::leanh::LeanObject,
    mut v___y_7008_: *mut crate::leanh::LeanObject,
    mut v___y_7009_: *mut crate::leanh::LeanObject,
    mut v___y_7010_: *mut crate::leanh::LeanObject,
    mut v___y_7011_: *mut crate::leanh::LeanObject,
    mut v___y_7012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_7013_: u8 = 0;
    let mut v_res_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7013_ = (crate::leanh::lean_unbox(v_cancel_7000_) as u8);
    v_res_7014_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(
            v_cancel_boxed_7013_,
            v_fst_7001_,
            v_a_7002_,
            v_b_7003_,
            v___y_7004_,
            v___y_7005_,
            v___y_7006_,
            v___y_7007_,
            v___y_7008_,
            v___y_7009_,
            v___y_7010_,
            v___y_7011_,
        );
    crate::leanh::lean_dec(v___y_7011_);
    crate::leanh::lean_dec_ref(v___y_7010_);
    crate::leanh::lean_dec(v___y_7009_);
    crate::leanh::lean_dec_ref(v___y_7008_);
    crate::leanh::lean_dec(v___y_7007_);
    crate::leanh::lean_dec_ref(v___y_7006_);
    crate::leanh::lean_dec(v___y_7005_);
    crate::leanh::lean_dec_ref(v___y_7004_);
    return v_res_7014_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(
    mut v_msg_7015_: *mut crate::leanh::LeanObject,
    mut v___y_7016_: *mut crate::leanh::LeanObject,
    mut v___y_7017_: *mut crate::leanh::LeanObject,
    mut v___y_7018_: *mut crate::leanh::LeanObject,
    mut v___y_7019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7026_: u8 = 0;
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7021_ = crate::leanh::lean_ctor_get(v___y_7018_, 5);
                v___x_7022_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_);
                v_a_7023_ = crate::leanh::lean_ctor_get(v___x_7022_, 0);
                v_isSharedCheck_7031_ = (!crate::leanh::lean_is_exclusive(v___x_7022_)) as u8;
                if v_isSharedCheck_7031_ == 0 {
                    v___x_7025_ = v___x_7022_;
                    v_isShared_7026_ = v_isSharedCheck_7031_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7023_);
                    crate::leanh::lean_dec(v___x_7022_);
                    v___x_7025_ = crate::leanh::lean_box(0);
                    v_isShared_7026_ = v_isSharedCheck_7031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_7021_);
                v___x_7027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7027_, 0, v_ref_7021_);
                crate::leanh::lean_ctor_set(v___x_7027_, 1, v_a_7023_);
                if v_isShared_7026_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7025_, 1);
                    crate::leanh::lean_ctor_set(v___x_7025_, 0, v___x_7027_);
                    v___x_7029_ = v___x_7025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 0, v___x_7027_);
                    v___x_7029_ = v_reuseFailAlloc_7030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(
    mut v_msg_7032_: *mut crate::leanh::LeanObject,
    mut v___y_7033_: *mut crate::leanh::LeanObject,
    mut v___y_7034_: *mut crate::leanh::LeanObject,
    mut v___y_7035_: *mut crate::leanh::LeanObject,
    mut v___y_7036_: *mut crate::leanh::LeanObject,
    mut v___y_7037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7038_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(
        v_msg_7032_,
        v___y_7033_,
        v___y_7034_,
        v___y_7035_,
        v___y_7036_,
    );
    crate::leanh::lean_dec(v___y_7036_);
    crate::leanh::lean_dec_ref(v___y_7035_);
    crate::leanh::lean_dec(v___y_7034_);
    crate::leanh::lean_dec_ref(v___y_7033_);
    return v_res_7038_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst___redArg(
    mut v_jobs_7039_: *mut crate::leanh::LeanObject,
    mut v_cancel_7040_: u8,
    mut v_a_7041_: *mut crate::leanh::LeanObject,
    mut v_a_7042_: *mut crate::leanh::LeanObject,
    mut v_a_7043_: *mut crate::leanh::LeanObject,
    mut v_a_7044_: *mut crate::leanh::LeanObject,
    mut v_a_7045_: *mut crate::leanh::LeanObject,
    mut v_a_7046_: *mut crate::leanh::LeanObject,
    mut v_a_7047_: *mut crate::leanh::LeanObject,
    mut v_a_7048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7059_: u8 = 0;
    let mut v_fst_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7067_: u8 = 0;
    let mut v_a_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7071_: u8 = 0;
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut v_a_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7050_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
                    v_jobs_7039_,
                    v_a_7041_,
                    v_a_7042_,
                    v_a_7043_,
                    v_a_7044_,
                    v_a_7045_,
                    v_a_7046_,
                    v_a_7047_,
                    v_a_7048_,
                );
                if crate::leanh::lean_obj_tag(v___x_7050_) == 0 {
                    v_a_7051_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    crate::leanh::lean_inc(v_a_7051_);
                    crate::leanh::lean_dec_ref_known(v___x_7050_, 1);
                    v_fst_7052_ = crate::leanh::lean_ctor_get(v_a_7051_, 0);
                    crate::leanh::lean_inc(v_fst_7052_);
                    v_snd_7053_ = crate::leanh::lean_ctor_get(v_a_7051_, 1);
                    crate::leanh::lean_inc(v_snd_7053_);
                    crate::leanh::lean_dec(v_a_7051_);
                    v___x_7054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_7055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_7040_, v_fst_7052_, v_snd_7053_, v___x_7054_, v_a_7041_, v_a_7042_, v_a_7043_, v_a_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
                    if crate::leanh::lean_obj_tag(v___x_7055_) == 0 {
                        v_a_7056_ = crate::leanh::lean_ctor_get(v___x_7055_, 0);
                        v_isSharedCheck_7067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7055_)) as u8;
                        if v_isSharedCheck_7067_ == 0 {
                            v___x_7058_ = v___x_7055_;
                            v_isShared_7059_ = v_isSharedCheck_7067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7056_);
                            crate::leanh::lean_dec(v___x_7055_);
                            v___x_7058_ = crate::leanh::lean_box(0);
                            v_isShared_7059_ = v_isSharedCheck_7067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7068_ = crate::leanh::lean_ctor_get(v___x_7055_, 0);
                        v_isSharedCheck_7075_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7055_)) as u8;
                        if v_isSharedCheck_7075_ == 0 {
                            v___x_7070_ = v___x_7055_;
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7068_);
                            crate::leanh::lean_dec(v___x_7055_);
                            v___x_7070_ = crate::leanh::lean_box(0);
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_7076_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7083_ = (!crate::leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7083_ == 0 {
                        v___x_7078_ = v___x_7050_;
                        v_isShared_7079_ = v_isSharedCheck_7083_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7076_);
                        crate::leanh::lean_dec(v___x_7050_);
                        v___x_7078_ = crate::leanh::lean_box(0);
                        v_isShared_7079_ = v_isSharedCheck_7083_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7060_ = crate::leanh::lean_ctor_get(v_a_7056_, 0);
                crate::leanh::lean_inc(v_fst_7060_);
                crate::leanh::lean_dec(v_a_7056_);
                if crate::leanh::lean_obj_tag(v_fst_7060_) == 0 {
                    crate::leanh::lean_del_object(v___x_7058_);
                    v___x_7061_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_7062_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_7061_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
                    return v___x_7062_;
                } else {
                    v_val_7063_ = crate::leanh::lean_ctor_get(v_fst_7060_, 0);
                    crate::leanh::lean_inc(v_val_7063_);
                    crate::leanh::lean_dec_ref_known(v_fst_7060_, 1);
                    if v_isShared_7059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7058_, 0, v_val_7063_);
                        v___x_7065_ = v___x_7058_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7066_, 0, v_val_7063_);
                        v___x_7065_ = v_reuseFailAlloc_7066_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7065_;
            }
            3 => {
                if v_isShared_7071_ == 0 {
                    v___x_7073_ = v___x_7070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_a_7068_);
                    v___x_7073_ = v_reuseFailAlloc_7074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7073_;
            }
            5 => {
                if v_isShared_7079_ == 0 {
                    v___x_7081_ = v___x_7078_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7076_);
                    v___x_7081_ = v_reuseFailAlloc_7082_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(
    mut v_jobs_7084_: *mut crate::leanh::LeanObject,
    mut v_cancel_7085_: *mut crate::leanh::LeanObject,
    mut v_a_7086_: *mut crate::leanh::LeanObject,
    mut v_a_7087_: *mut crate::leanh::LeanObject,
    mut v_a_7088_: *mut crate::leanh::LeanObject,
    mut v_a_7089_: *mut crate::leanh::LeanObject,
    mut v_a_7090_: *mut crate::leanh::LeanObject,
    mut v_a_7091_: *mut crate::leanh::LeanObject,
    mut v_a_7092_: *mut crate::leanh::LeanObject,
    mut v_a_7093_: *mut crate::leanh::LeanObject,
    mut v_a_7094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_7095_: u8 = 0;
    let mut v_res_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7095_ = (crate::leanh::lean_unbox(v_cancel_7085_) as u8);
    v_res_7096_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(
        v_jobs_7084_,
        v_cancel_boxed_7095_,
        v_a_7086_,
        v_a_7087_,
        v_a_7088_,
        v_a_7089_,
        v_a_7090_,
        v_a_7091_,
        v_a_7092_,
        v_a_7093_,
    );
    crate::leanh::lean_dec(v_a_7093_);
    crate::leanh::lean_dec_ref(v_a_7092_);
    crate::leanh::lean_dec(v_a_7091_);
    crate::leanh::lean_dec_ref(v_a_7090_);
    crate::leanh::lean_dec(v_a_7089_);
    crate::leanh::lean_dec_ref(v_a_7088_);
    crate::leanh::lean_dec(v_a_7087_);
    crate::leanh::lean_dec_ref(v_a_7086_);
    return v_res_7096_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst(
    mut v_00_u03b1_7097_: *mut crate::leanh::LeanObject,
    mut v_jobs_7098_: *mut crate::leanh::LeanObject,
    mut v_cancel_7099_: u8,
    mut v_a_7100_: *mut crate::leanh::LeanObject,
    mut v_a_7101_: *mut crate::leanh::LeanObject,
    mut v_a_7102_: *mut crate::leanh::LeanObject,
    mut v_a_7103_: *mut crate::leanh::LeanObject,
    mut v_a_7104_: *mut crate::leanh::LeanObject,
    mut v_a_7105_: *mut crate::leanh::LeanObject,
    mut v_a_7106_: *mut crate::leanh::LeanObject,
    mut v_a_7107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7109_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(
        v_jobs_7098_,
        v_cancel_7099_,
        v_a_7100_,
        v_a_7101_,
        v_a_7102_,
        v_a_7103_,
        v_a_7104_,
        v_a_7105_,
        v_a_7106_,
        v_a_7107_,
    );
    return v___x_7109_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst___boxed(
    mut v_00_u03b1_7110_: *mut crate::leanh::LeanObject,
    mut v_jobs_7111_: *mut crate::leanh::LeanObject,
    mut v_cancel_7112_: *mut crate::leanh::LeanObject,
    mut v_a_7113_: *mut crate::leanh::LeanObject,
    mut v_a_7114_: *mut crate::leanh::LeanObject,
    mut v_a_7115_: *mut crate::leanh::LeanObject,
    mut v_a_7116_: *mut crate::leanh::LeanObject,
    mut v_a_7117_: *mut crate::leanh::LeanObject,
    mut v_a_7118_: *mut crate::leanh::LeanObject,
    mut v_a_7119_: *mut crate::leanh::LeanObject,
    mut v_a_7120_: *mut crate::leanh::LeanObject,
    mut v_a_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancel_boxed_7122_: u8 = 0;
    let mut v_res_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7122_ = (crate::leanh::lean_unbox(v_cancel_7112_) as u8);
    v_res_7123_ = l_Lean_Elab_Tactic_TacticM_parFirst(
        v_00_u03b1_7110_,
        v_jobs_7111_,
        v_cancel_boxed_7122_,
        v_a_7113_,
        v_a_7114_,
        v_a_7115_,
        v_a_7116_,
        v_a_7117_,
        v_a_7118_,
        v_a_7119_,
        v_a_7120_,
    );
    crate::leanh::lean_dec(v_a_7120_);
    crate::leanh::lean_dec_ref(v_a_7119_);
    crate::leanh::lean_dec(v_a_7118_);
    crate::leanh::lean_dec_ref(v_a_7117_);
    crate::leanh::lean_dec(v_a_7116_);
    crate::leanh::lean_dec_ref(v_a_7115_);
    crate::leanh::lean_dec(v_a_7114_);
    crate::leanh::lean_dec_ref(v_a_7113_);
    return v_res_7123_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(
    mut v_00_u03b1_7124_: *mut crate::leanh::LeanObject,
    mut v_cancel_7125_: u8,
    mut v_fst_7126_: *mut crate::leanh::LeanObject,
    mut v_inst_7127_: *mut crate::leanh::LeanObject,
    mut v_R_7128_: *mut crate::leanh::LeanObject,
    mut v_a_7129_: *mut crate::leanh::LeanObject,
    mut v_b_7130_: *mut crate::leanh::LeanObject,
    mut v_c_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
    mut v___y_7134_: *mut crate::leanh::LeanObject,
    mut v___y_7135_: *mut crate::leanh::LeanObject,
    mut v___y_7136_: *mut crate::leanh::LeanObject,
    mut v___y_7137_: *mut crate::leanh::LeanObject,
    mut v___y_7138_: *mut crate::leanh::LeanObject,
    mut v___y_7139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7141_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(
            v_cancel_7125_,
            v_fst_7126_,
            v_a_7129_,
            v_b_7130_,
            v___y_7132_,
            v___y_7133_,
            v___y_7134_,
            v___y_7135_,
            v___y_7136_,
            v___y_7137_,
            v___y_7138_,
            v___y_7139_,
        );
    return v___x_7141_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_7142_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_cancel_7143_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_fst_7144_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_7145_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_R_7146_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_7147_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_7148_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_c_7149_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_7150_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_7151_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_7152_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_7153_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_7154_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7155_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7156_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7157_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7158_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_cancel_boxed_7159_: u8 = 0;
    let mut v_res_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7159_ = (crate::leanh::lean_unbox(v_cancel_7143_) as u8);
    v_res_7160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(
        v_00_u03b1_7142_,
        v_cancel_boxed_7159_,
        v_fst_7144_,
        v_inst_7145_,
        v_R_7146_,
        v_a_7147_,
        v_b_7148_,
        v_c_7149_,
        v___y_7150_,
        v___y_7151_,
        v___y_7152_,
        v___y_7153_,
        v___y_7154_,
        v___y_7155_,
        v___y_7156_,
        v___y_7157_,
    );
    crate::leanh::lean_dec(v___y_7157_);
    crate::leanh::lean_dec_ref(v___y_7156_);
    crate::leanh::lean_dec(v___y_7155_);
    crate::leanh::lean_dec_ref(v___y_7154_);
    crate::leanh::lean_dec(v___y_7153_);
    crate::leanh::lean_dec_ref(v___y_7152_);
    crate::leanh::lean_dec(v___y_7151_);
    crate::leanh::lean_dec_ref(v___y_7150_);
    return v_res_7160_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(
    mut v_00_u03b1_7161_: *mut crate::leanh::LeanObject,
    mut v_msg_7162_: *mut crate::leanh::LeanObject,
    mut v___y_7163_: *mut crate::leanh::LeanObject,
    mut v___y_7164_: *mut crate::leanh::LeanObject,
    mut v___y_7165_: *mut crate::leanh::LeanObject,
    mut v___y_7166_: *mut crate::leanh::LeanObject,
    mut v___y_7167_: *mut crate::leanh::LeanObject,
    mut v___y_7168_: *mut crate::leanh::LeanObject,
    mut v___y_7169_: *mut crate::leanh::LeanObject,
    mut v___y_7170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7172_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(
        v_msg_7162_,
        v___y_7167_,
        v___y_7168_,
        v___y_7169_,
        v___y_7170_,
    );
    return v___x_7172_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(
    mut v_00_u03b1_7173_: *mut crate::leanh::LeanObject,
    mut v_msg_7174_: *mut crate::leanh::LeanObject,
    mut v___y_7175_: *mut crate::leanh::LeanObject,
    mut v___y_7176_: *mut crate::leanh::LeanObject,
    mut v___y_7177_: *mut crate::leanh::LeanObject,
    mut v___y_7178_: *mut crate::leanh::LeanObject,
    mut v___y_7179_: *mut crate::leanh::LeanObject,
    mut v___y_7180_: *mut crate::leanh::LeanObject,
    mut v___y_7181_: *mut crate::leanh::LeanObject,
    mut v___y_7182_: *mut crate::leanh::LeanObject,
    mut v___y_7183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7184_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(
        v_00_u03b1_7173_,
        v_msg_7174_,
        v___y_7175_,
        v___y_7176_,
        v___y_7177_,
        v___y_7178_,
        v___y_7179_,
        v___y_7180_,
        v___y_7181_,
        v___y_7182_,
    );
    crate::leanh::lean_dec(v___y_7182_);
    crate::leanh::lean_dec_ref(v___y_7181_);
    crate::leanh::lean_dec(v___y_7180_);
    crate::leanh::lean_dec_ref(v___y_7179_);
    crate::leanh::lean_dec(v___y_7178_);
    crate::leanh::lean_dec_ref(v___y_7177_);
    crate::leanh::lean_dec(v___y_7176_);
    crate::leanh::lean_dec_ref(v___y_7175_);
    return v_res_7184_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Parallel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Parallel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Parallel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Parallel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Parallel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Parallel(builtin);
}

// Lean compiler output
// Module: Lean.Elab.Parallel
// Imports: Lean.Elab.Task
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
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_apply_5, lean_apply_7, lean_apply_9, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_usize,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Core_CoreM_parFirst___redArg___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Core_CoreM_parFirst___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_CoreM_parFirst___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(
    mut v_it_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_3593_) == 0 {
                    v___x_3595_ = lean_box(2);
                    return v___x_3595_;
                } else {
                    v___x_3596_ = l_IO_waitAny_x27___redArg(v_it_3593_);
                    v_fst_3597_ = lean_ctor_get(v___x_3596_, 0);
                    v_snd_3598_ = lean_ctor_get(v___x_3596_, 1);
                    v_isSharedCheck_3605_ = (!lean_is_exclusive(v___x_3596_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3596_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3598_);
                        lean_inc(v_fst_3597_);
                        lean_dec(v___x_3596_);
                        v___x_3600_ = lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3601_ == 0 {
                    lean_ctor_set(v___x_3600_, 1, v_fst_3597_);
                    lean_ctor_set(v___x_3600_, 0, v_snd_3598_);
                    v___x_3603_ = v___x_3600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_snd_3598_);
                    lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_fst_3597_);
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
    mut v_it_3606_: *mut LeanObject,
    mut v___y_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3608_: *mut LeanObject = core::ptr::null_mut();
    v_res_3608_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(v_it_3606_);
    return v_res_3608_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO(
    mut v_00_u03b1_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3611_: *mut LeanObject = core::ptr::null_mut();
    v___f_3611_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0;
    return v___f_3611_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(
    mut v_tasks_3612_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_tasks_3612_);
    return v_tasks_3612_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(
    mut v_tasks_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3614_: *mut LeanObject = core::ptr::null_mut();
    v_res_3614_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(v_tasks_3613_);
    lean_dec(v_tasks_3613_);
    return v_res_3614_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks(
    mut v_00_u03b1_3615_: *mut LeanObject,
    mut v_tasks_3616_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_tasks_3616_);
    return v_tasks_3616_;
}
pub unsafe fn l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(
    mut v_00_u03b1_3617_: *mut LeanObject,
    mut v_tasks_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3619_: *mut LeanObject = core::ptr::null_mut();
    v_res_3619_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks(v_00_u03b1_3617_, v_tasks_3618_);
    lean_dec(v_tasks_3618_);
    return v_res_3619_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
    mut v_x_3620_: *mut LeanObject,
    mut v_x_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3620_) == 0 {
                    v___x_3625_ = l_List_reverse___redArg(v_x_3621_);
                    v___x_3626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3626_, 0, v___x_3625_);
                    return v___x_3626_;
                } else {
                    v_head_3627_ = lean_ctor_get(v_x_3620_, 0);
                    v_tail_3628_ = lean_ctor_get(v_x_3620_, 1);
                    v_isSharedCheck_3646_ = (!lean_is_exclusive(v_x_3620_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3630_ = v_x_3620_;
                        v_isShared_3631_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3628_);
                        lean_inc(v_head_3627_);
                        lean_dec(v_x_3620_);
                        v___x_3630_ = lean_box(0);
                        v_isShared_3631_ = v_isSharedCheck_3646_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3632_ =
                    l_Lean_Core_CoreM_asTask___redArg(v_head_3627_, v___y_3622_, v___y_3623_);
                if lean_obj_tag(v___x_3632_) == 0 {
                    v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
                    lean_inc(v_a_3633_);
                    lean_dec_ref_known(v___x_3632_, 1);
                    if v_isShared_3631_ == 0 {
                        lean_ctor_set(v___x_3630_, 1, v_x_3621_);
                        lean_ctor_set(v___x_3630_, 0, v_a_3633_);
                        v___x_3635_ = v___x_3630_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3633_);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_x_3621_);
                        v___x_3635_ = v_reuseFailAlloc_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3630_);
                    lean_dec(v_tail_3628_);
                    lean_dec(v_x_3621_);
                    v_a_3638_ = lean_ctor_get(v___x_3632_, 0);
                    v_isSharedCheck_3645_ = (!lean_is_exclusive(v___x_3632_)) as u8;
                    if v_isSharedCheck_3645_ == 0 {
                        v___x_3640_ = v___x_3632_;
                        v_isShared_3641_ = v_isSharedCheck_3645_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3638_);
                        lean_dec(v___x_3632_);
                        v___x_3640_ = lean_box(0);
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
                    v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
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
    mut v_x_3647_: *mut LeanObject,
    mut v_x_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
        v_x_3647_,
        v_x_3648_,
        v___y_3649_,
        v___y_3650_,
    );
    lean_dec(v___y_3650_);
    lean_dec_ref(v___y_3649_);
    return v_res_3652_;
}
pub unsafe fn l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(
    mut v_as_3653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3653_) == 0 {
                    v___x_3655_ = lean_box(0);
                    return v___x_3655_;
                } else {
                    v_head_3656_ = lean_ctor_get(v_as_3653_, 0);
                    lean_inc(v_head_3656_);
                    v_tail_3657_ = lean_ctor_get(v_as_3653_, 1);
                    lean_inc(v_tail_3657_);
                    lean_dec_ref_known(v_as_3653_, 2);
                    v___x_3658_ = lean_apply_1(v_head_3656_, lean_box(0));
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
    mut v_as_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3662_: *mut LeanObject = core::ptr::null_mut();
    v_res_3662_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_3660_);
    return v_res_3662_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel___redArg(
    mut v_jobs_3663_: *mut LeanObject,
    mut v_a_3664_: *mut LeanObject,
    mut v_a_3665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_a_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3691_: u8 = 0;
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3667_ = lean_box(0);
                v___x_3668_ =
                    l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
                        v_jobs_3663_,
                        v___x_3667_,
                        v_a_3664_,
                        v_a_3665_,
                    );
                if lean_obj_tag(v___x_3668_) == 0 {
                    v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3687_ = (!lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3671_ = v___x_3668_;
                        v_isShared_3672_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3669_);
                        lean_dec(v___x_3668_);
                        v___x_3671_ = lean_box(0);
                        v_isShared_3672_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3688_ = lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3695_ = (!lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3690_ = v___x_3668_;
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3688_);
                        lean_dec(v___x_3668_);
                        v___x_3690_ = lean_box(0);
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3673_ = l_List_unzipTR___redArg(v_a_3669_);
                v_fst_3674_ = lean_ctor_get(v___x_3673_, 0);
                v_snd_3675_ = lean_ctor_get(v___x_3673_, 1);
                v_isSharedCheck_3686_ = (!lean_is_exclusive(v___x_3673_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v___x_3677_ = v___x_3673_;
                    v_isShared_3678_ = v_isSharedCheck_3686_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3675_);
                    lean_inc(v_fst_3674_);
                    lean_dec(v___x_3673_);
                    v___x_3677_ = lean_box(0);
                    v_isShared_3678_ = v_isSharedCheck_3686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3679_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_3679_, 0, v_fst_3674_);
                if v_isShared_3678_ == 0 {
                    lean_ctor_set(v___x_3677_, 0, v___x_3679_);
                    v___x_3681_ = v___x_3677_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_snd_3675_);
                    v___x_3681_ = v_reuseFailAlloc_3685_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3672_ == 0 {
                    lean_ctor_set(v___x_3671_, 0, v___x_3681_);
                    v___x_3683_ = v___x_3671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
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
                    v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
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
    mut v_jobs_3696_: *mut LeanObject,
    mut v_a_3697_: *mut LeanObject,
    mut v_a_3698_: *mut LeanObject,
    mut v_a_3699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3700_: *mut LeanObject = core::ptr::null_mut();
    v_res_3700_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_3696_, v_a_3697_, v_a_3698_);
    lean_dec(v_a_3698_);
    lean_dec_ref(v_a_3697_);
    return v_res_3700_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel(
    mut v_00_u03b1_3701_: *mut LeanObject,
    mut v_jobs_3702_: *mut LeanObject,
    mut v_a_3703_: *mut LeanObject,
    mut v_a_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    v___x_3706_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_3702_, v_a_3703_, v_a_3704_);
    return v___x_3706_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterWithCancel___boxed(
    mut v_00_u03b1_3707_: *mut LeanObject,
    mut v_jobs_3708_: *mut LeanObject,
    mut v_a_3709_: *mut LeanObject,
    mut v_a_3710_: *mut LeanObject,
    mut v_a_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3712_: *mut LeanObject = core::ptr::null_mut();
    v_res_3712_ =
        l_Lean_Core_CoreM_parIterWithCancel(v_00_u03b1_3707_, v_jobs_3708_, v_a_3709_, v_a_3710_);
    lean_dec(v_a_3710_);
    lean_dec_ref(v_a_3709_);
    return v_res_3712_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(
    mut v_00_u03b1_3713_: *mut LeanObject,
    mut v_x_3714_: *mut LeanObject,
    mut v_x_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v___x_3719_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
        v_x_3714_,
        v_x_3715_,
        v___y_3716_,
        v___y_3717_,
    );
    return v___x_3719_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(
    mut v_00_u03b1_3720_: *mut LeanObject,
    mut v_x_3721_: *mut LeanObject,
    mut v_x_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3726_: *mut LeanObject = core::ptr::null_mut();
    v_res_3726_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(
        v_00_u03b1_3720_,
        v_x_3721_,
        v_x_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    lean_dec(v___y_3724_);
    lean_dec_ref(v___y_3723_);
    return v_res_3726_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter___redArg(
    mut v_jobs_3727_: *mut LeanObject,
    mut v_a_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v_snd_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_a_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3744_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3731_) == 0 {
                    v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3740_ = (!lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3734_ = v___x_3731_;
                        v_isShared_3735_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3732_);
                        lean_dec(v___x_3731_);
                        v___x_3734_ = lean_box(0);
                        v_isShared_3735_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3741_ = lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3748_ = (!lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v___x_3743_ = v___x_3731_;
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3741_);
                        lean_dec(v___x_3731_);
                        v___x_3743_ = lean_box(0);
                        v_isShared_3744_ = v_isSharedCheck_3748_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3736_ = lean_ctor_get(v_a_3732_, 1);
                lean_inc(v_snd_3736_);
                lean_dec(v_a_3732_);
                if v_isShared_3735_ == 0 {
                    lean_ctor_set(v___x_3734_, 0, v_snd_3736_);
                    v___x_3738_ = v___x_3734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_snd_3736_);
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
                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
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
    mut v_jobs_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3753_: *mut LeanObject = core::ptr::null_mut();
    v_res_3753_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_3749_, v_a_3750_, v_a_3751_);
    lean_dec(v_a_3751_);
    lean_dec_ref(v_a_3750_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter(
    mut v_00_u03b1_3754_: *mut LeanObject,
    mut v_jobs_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    v___x_3759_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_3755_, v_a_3756_, v_a_3757_);
    return v___x_3759_;
}
pub unsafe fn l_Lean_Core_CoreM_parIter___boxed(
    mut v_00_u03b1_3760_: *mut LeanObject,
    mut v_jobs_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_a_3763_: *mut LeanObject,
    mut v_a_3764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3765_: *mut LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_Core_CoreM_parIter(v_00_u03b1_3760_, v_jobs_3761_, v_a_3762_, v_a_3763_);
    lean_dec(v_a_3763_);
    lean_dec_ref(v_a_3762_);
    return v_res_3765_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(
    mut v_jobs_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_a_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = lean_box(0);
                v___x_3771_ =
                    l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(
                        v_jobs_3766_,
                        v___x_3770_,
                        v_a_3767_,
                        v_a_3768_,
                    );
                if lean_obj_tag(v___x_3771_) == 0 {
                    v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
                    v_isSharedCheck_3790_ = (!lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3774_ = v___x_3771_;
                        v_isShared_3775_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3772_);
                        lean_dec(v___x_3771_);
                        v___x_3774_ = lean_box(0);
                        v_isShared_3775_ = v_isSharedCheck_3790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3791_ = lean_ctor_get(v___x_3771_, 0);
                    v_isSharedCheck_3798_ = (!lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3798_ == 0 {
                        v___x_3793_ = v___x_3771_;
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3791_);
                        lean_dec(v___x_3771_);
                        v___x_3793_ = lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3798_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3776_ = l_List_unzipTR___redArg(v_a_3772_);
                v_fst_3777_ = lean_ctor_get(v___x_3776_, 0);
                v_snd_3778_ = lean_ctor_get(v___x_3776_, 1);
                v_isSharedCheck_3789_ = (!lean_is_exclusive(v___x_3776_)) as u8;
                if v_isSharedCheck_3789_ == 0 {
                    v___x_3780_ = v___x_3776_;
                    v_isShared_3781_ = v_isSharedCheck_3789_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3778_);
                    lean_inc(v_fst_3777_);
                    lean_dec(v___x_3776_);
                    v___x_3780_ = lean_box(0);
                    v_isShared_3781_ = v_isSharedCheck_3789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3782_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_3782_, 0, v_fst_3777_);
                if v_isShared_3781_ == 0 {
                    lean_ctor_set(v___x_3780_, 0, v___x_3782_);
                    v___x_3784_ = v___x_3780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3782_);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_snd_3778_);
                    v___x_3784_ = v_reuseFailAlloc_3788_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3775_ == 0 {
                    lean_ctor_set(v___x_3774_, 0, v___x_3784_);
                    v___x_3786_ = v___x_3774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
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
                    v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
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
    mut v_jobs_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
    mut v_a_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3803_: *mut LeanObject = core::ptr::null_mut();
    v_res_3803_ =
        l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_3799_, v_a_3800_, v_a_3801_);
    lean_dec(v_a_3801_);
    lean_dec_ref(v_a_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel(
    mut v_00_u03b1_3804_: *mut LeanObject,
    mut v_jobs_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
    mut v_a_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    v___x_3809_ =
        l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_3805_, v_a_3806_, v_a_3807_);
    return v___x_3809_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(
    mut v_00_u03b1_3810_: *mut LeanObject,
    mut v_jobs_3811_: *mut LeanObject,
    mut v_a_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3815_: *mut LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(
        v_00_u03b1_3810_,
        v_jobs_3811_,
        v_a_3812_,
        v_a_3813_,
    );
    lean_dec(v_a_3813_);
    lean_dec_ref(v_a_3812_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy___redArg(
    mut v_jobs_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v_snd_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_a_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3820_) == 0 {
                    v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3829_ = (!lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3829_ == 0 {
                        v___x_3823_ = v___x_3820_;
                        v_isShared_3824_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3821_);
                        lean_dec(v___x_3820_);
                        v___x_3823_ = lean_box(0);
                        v_isShared_3824_ = v_isSharedCheck_3829_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3830_ = lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3837_ = (!lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3837_ == 0 {
                        v___x_3832_ = v___x_3820_;
                        v_isShared_3833_ = v_isSharedCheck_3837_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3830_);
                        lean_dec(v___x_3820_);
                        v___x_3832_ = lean_box(0);
                        v_isShared_3833_ = v_isSharedCheck_3837_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3825_ = lean_ctor_get(v_a_3821_, 1);
                lean_inc(v_snd_3825_);
                lean_dec(v_a_3821_);
                if v_isShared_3824_ == 0 {
                    lean_ctor_set(v___x_3823_, 0, v_snd_3825_);
                    v___x_3827_ = v___x_3823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_snd_3825_);
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
                    v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
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
    mut v_jobs_3838_: *mut LeanObject,
    mut v_a_3839_: *mut LeanObject,
    mut v_a_3840_: *mut LeanObject,
    mut v_a_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_res_3842_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_3838_, v_a_3839_, v_a_3840_);
    lean_dec(v_a_3840_);
    lean_dec_ref(v_a_3839_);
    return v_res_3842_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy(
    mut v_00_u03b1_3843_: *mut LeanObject,
    mut v_jobs_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    v___x_3848_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_3844_, v_a_3845_, v_a_3846_);
    return v___x_3848_;
}
pub unsafe fn l_Lean_Core_CoreM_parIterGreedy___boxed(
    mut v_00_u03b1_3849_: *mut LeanObject,
    mut v_jobs_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3854_: *mut LeanObject = core::ptr::null_mut();
    v_res_3854_ =
        l_Lean_Core_CoreM_parIterGreedy(v_00_u03b1_3849_, v_jobs_3850_, v_a_3851_, v_a_3852_);
    lean_dec(v_a_3852_);
    lean_dec_ref(v_a_3851_);
    return v_res_3854_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
    mut v_as_x27_3855_: *mut LeanObject,
    mut v_b_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: u8 = 0;
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: u8 = 0;
    let mut v___x_1781__overap_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3855_) == 0 {
                    v___x_3860_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3860_, 0, v_b_3856_);
                    return v___x_3860_;
                } else {
                    v_head_3861_ = lean_ctor_get(v_as_x27_3855_, 0);
                    v_tail_3862_ = lean_ctor_get(v_as_x27_3855_, 1);
                    lean_inc(v_head_3861_);
                    v___x_1781__overap_3876_ = lean_task_get_own(v_head_3861_);
                    lean_inc(v___y_3858_);
                    lean_inc_ref(v___y_3857_);
                    v___x_3877_ = lean_apply_3(
                        v___x_1781__overap_3876_,
                        v___y_3857_,
                        v___y_3858_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3877_) == 0 {
                        v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
                        lean_inc(v_a_3878_);
                        lean_dec_ref_known(v___x_3877_, 1);
                        v___x_3879_ = l_Lean_Core_saveState___redArg(v___y_3858_);
                        if lean_obj_tag(v___x_3879_) == 0 {
                            v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
                            v_isSharedCheck_3888_ = (!lean_is_exclusive(v___x_3879_)) as u8;
                            if v_isSharedCheck_3888_ == 0 {
                                v___x_3882_ = v___x_3879_;
                                v_isShared_3883_ = v_isSharedCheck_3888_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3880_);
                                lean_dec(v___x_3879_);
                                v___x_3882_ = lean_box(0);
                                v_isShared_3883_ = v_isSharedCheck_3888_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3878_);
                            v_a_3889_ = lean_ctor_get(v___x_3879_, 0);
                            lean_inc(v_a_3889_);
                            lean_dec_ref_known(v___x_3879_, 1);
                            v_a_3873_ = v_a_3889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3890_ = lean_ctor_get(v___x_3877_, 0);
                        lean_inc(v_a_3890_);
                        lean_dec_ref_known(v___x_3877_, 1);
                        v_a_3873_ = v_a_3890_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3865_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3865_, 0, v_a_3864_);
                lean_ctor_set(v___x_3865_, 1, v_b_3856_);
                v_as_x27_3855_ = v_tail_3862_;
                v_b_3856_ = v___x_3865_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3869_ == 0 {
                    v___x_3870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3870_, 0, v___y_3868_);
                    v_a_3864_ = v___x_3870_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_b_3856_);
                    v___x_3871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3871_, 0, v___y_3868_);
                    return v___x_3871_;
                }
            }
            3 => {
                v___x_3874_ = l_Lean_Exception_isInterrupt(v_a_3873_);
                if v___x_3874_ == 0 {
                    lean_inc_ref(v_a_3873_);
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
                v___x_3884_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3884_, 0, v_a_3878_);
                lean_ctor_set(v___x_3884_, 1, v_a_3880_);
                if v_isShared_3883_ == 0 {
                    lean_ctor_set_tag(v___x_3882_, 1);
                    lean_ctor_set(v___x_3882_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
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
    mut v_as_x27_3891_: *mut LeanObject,
    mut v_b_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
        v_as_x27_3891_,
        v_b_3892_,
        v___y_3893_,
        v___y_3894_,
    );
    lean_dec(v___y_3894_);
    lean_dec_ref(v___y_3893_);
    lean_dec(v_as_x27_3891_);
    return v_res_3896_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
    mut v_x_3897_: *mut LeanObject,
    mut v_x_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3908_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3897_) == 0 {
                    v___x_3902_ = l_List_reverse___redArg(v_x_3898_);
                    v___x_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3903_, 0, v___x_3902_);
                    return v___x_3903_;
                } else {
                    v_head_3904_ = lean_ctor_get(v_x_3897_, 0);
                    v_tail_3905_ = lean_ctor_get(v_x_3897_, 1);
                    v_isSharedCheck_3923_ = (!lean_is_exclusive(v_x_3897_)) as u8;
                    if v_isSharedCheck_3923_ == 0 {
                        v___x_3907_ = v_x_3897_;
                        v_isShared_3908_ = v_isSharedCheck_3923_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3905_);
                        lean_inc(v_head_3904_);
                        lean_dec(v_x_3897_);
                        v___x_3907_ = lean_box(0);
                        v_isShared_3908_ = v_isSharedCheck_3923_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3909_ =
                    l_Lean_Core_CoreM_asTask_x27___redArg(v_head_3904_, v___y_3899_, v___y_3900_);
                if lean_obj_tag(v___x_3909_) == 0 {
                    v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
                    lean_inc(v_a_3910_);
                    lean_dec_ref_known(v___x_3909_, 1);
                    if v_isShared_3908_ == 0 {
                        lean_ctor_set(v___x_3907_, 1, v_x_3898_);
                        lean_ctor_set(v___x_3907_, 0, v_a_3910_);
                        v___x_3912_ = v___x_3907_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3910_);
                        lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_x_3898_);
                        v___x_3912_ = v_reuseFailAlloc_3914_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3907_);
                    lean_dec(v_tail_3905_);
                    lean_dec(v_x_3898_);
                    v_a_3915_ = lean_ctor_get(v___x_3909_, 0);
                    v_isSharedCheck_3922_ = (!lean_is_exclusive(v___x_3909_)) as u8;
                    if v_isSharedCheck_3922_ == 0 {
                        v___x_3917_ = v___x_3909_;
                        v_isShared_3918_ = v_isSharedCheck_3922_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3915_);
                        lean_dec(v___x_3909_);
                        v___x_3917_ = lean_box(0);
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
                    v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
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
    mut v_x_3924_: *mut LeanObject,
    mut v_x_3925_: *mut LeanObject,
    mut v___y_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3929_: *mut LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
        v_x_3924_,
        v_x_3925_,
        v___y_3926_,
        v___y_3927_,
    );
    lean_dec(v___y_3927_);
    lean_dec_ref(v___y_3926_);
    return v_res_3929_;
}
pub unsafe fn l_Lean_Core_CoreM_par___redArg(
    mut v_jobs_3930_: *mut LeanObject,
    mut v_a_3931_: *mut LeanObject,
    mut v_a_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v_a_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3952_: u8 = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3934_ = lean_st_ref_get(v_a_3932_);
                v___x_3935_ = lean_box(0);
                v___x_3936_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
                    v_jobs_3930_,
                    v___x_3935_,
                    v_a_3931_,
                    v_a_3932_,
                );
                if lean_obj_tag(v___x_3936_) == 0 {
                    v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
                    lean_inc(v_a_3937_);
                    lean_dec_ref_known(v___x_3936_, 1);
                    v___x_3938_ =
                        l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
                            v_a_3937_,
                            v___x_3935_,
                            v_a_3931_,
                            v_a_3932_,
                        );
                    lean_dec(v_a_3937_);
                    if lean_obj_tag(v___x_3938_) == 0 {
                        v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
                        v_isSharedCheck_3948_ = (!lean_is_exclusive(v___x_3938_)) as u8;
                        if v_isSharedCheck_3948_ == 0 {
                            v___x_3941_ = v___x_3938_;
                            v_isShared_3942_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3939_);
                            lean_dec(v___x_3938_);
                            v___x_3941_ = lean_box(0);
                            v_isShared_3942_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3934_);
                        return v___x_3938_;
                    }
                } else {
                    lean_dec(v___x_3934_);
                    v_a_3949_ = lean_ctor_get(v___x_3936_, 0);
                    v_isSharedCheck_3956_ = (!lean_is_exclusive(v___x_3936_)) as u8;
                    if v_isSharedCheck_3956_ == 0 {
                        v___x_3951_ = v___x_3936_;
                        v_isShared_3952_ = v_isSharedCheck_3956_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3949_);
                        lean_dec(v___x_3936_);
                        v___x_3951_ = lean_box(0);
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
                    lean_ctor_set(v___x_3941_, 0, v___x_3944_);
                    v___x_3946_ = v___x_3941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
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
                    v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
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
    mut v_jobs_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
    mut v_a_3959_: *mut LeanObject,
    mut v_a_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3961_: *mut LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_Core_CoreM_par___redArg(v_jobs_3957_, v_a_3958_, v_a_3959_);
    lean_dec(v_a_3959_);
    lean_dec_ref(v_a_3958_);
    return v_res_3961_;
}
pub unsafe fn l_Lean_Core_CoreM_par(
    mut v_00_u03b1_3962_: *mut LeanObject,
    mut v_jobs_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Lean_Core_CoreM_par___redArg(v_jobs_3963_, v_a_3964_, v_a_3965_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Core_CoreM_par___boxed(
    mut v_00_u03b1_3968_: *mut LeanObject,
    mut v_jobs_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3973_: *mut LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lean_Core_CoreM_par(v_00_u03b1_3968_, v_jobs_3969_, v_a_3970_, v_a_3971_);
    lean_dec(v_a_3971_);
    lean_dec_ref(v_a_3970_);
    return v_res_3973_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(
    mut v_00_u03b1_3974_: *mut LeanObject,
    mut v_x_3975_: *mut LeanObject,
    mut v_x_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    v___x_3980_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
        v_x_3975_,
        v_x_3976_,
        v___y_3977_,
        v___y_3978_,
    );
    return v___x_3980_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(
    mut v_00_u03b1_3981_: *mut LeanObject,
    mut v_x_3982_: *mut LeanObject,
    mut v_x_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(
        v_00_u03b1_3981_,
        v_x_3982_,
        v_x_3983_,
        v___y_3984_,
        v___y_3985_,
    );
    lean_dec(v___y_3985_);
    lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(
    mut v_00_u03b1_3988_: *mut LeanObject,
    mut v_as_3989_: *mut LeanObject,
    mut v_as_x27_3990_: *mut LeanObject,
    mut v_b_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    v___x_3996_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(
        v_as_x27_3990_,
        v_b_3991_,
        v___y_3993_,
        v___y_3994_,
    );
    return v___x_3996_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(
    mut v_00_u03b1_3997_: *mut LeanObject,
    mut v_as_3998_: *mut LeanObject,
    mut v_as_x27_3999_: *mut LeanObject,
    mut v_b_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v___y_4002_: *mut LeanObject,
    mut v___y_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4005_: *mut LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(
        v_00_u03b1_3997_,
        v_as_3998_,
        v_as_x27_3999_,
        v_b_4000_,
        v_a_4001_,
        v___y_4002_,
        v___y_4003_,
    );
    lean_dec(v___y_4003_);
    lean_dec_ref(v___y_4002_);
    lean_dec(v_as_x27_3999_);
    lean_dec(v_as_3998_);
    return v_res_4005_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
    mut v_as_x27_4006_: *mut LeanObject,
    mut v_b_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591__overap_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___y_4025_: u8 = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    let mut v___x_4033_: u8 = 0;
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4006_) == 0 {
                    v___x_4011_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4011_, 0, v_b_4007_);
                    return v___x_4011_;
                } else {
                    v_head_4012_ = lean_ctor_get(v_as_x27_4006_, 0);
                    v_tail_4013_ = lean_ctor_get(v_as_x27_4006_, 1);
                    lean_inc(v_head_4012_);
                    v___x_1591__overap_4014_ = lean_task_get_own(v_head_4012_);
                    lean_inc(v___y_4009_);
                    lean_inc_ref(v___y_4008_);
                    v___x_4015_ = lean_apply_3(
                        v___x_1591__overap_4014_,
                        v___y_4008_,
                        v___y_4009_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4015_) == 0 {
                        v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
                        lean_inc(v_a_4016_);
                        lean_dec_ref_known(v___x_4015_, 1);
                        v___x_4017_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4017_, 0, v_a_4016_);
                        v___x_4018_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                        lean_ctor_set(v___x_4018_, 1, v_b_4007_);
                        v_as_x27_4006_ = v_tail_4013_;
                        v_b_4007_ = v___x_4018_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4020_ = lean_ctor_get(v___x_4015_, 0);
                        v_isSharedCheck_4034_ = (!lean_is_exclusive(v___x_4015_)) as u8;
                        if v_isSharedCheck_4034_ == 0 {
                            v___x_4022_ = v___x_4015_;
                            v_isShared_4023_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4020_);
                            lean_dec(v___x_4015_);
                            v___x_4022_ = lean_box(0);
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
                    lean_inc(v_a_4020_);
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
                    lean_del_object(v___x_4022_);
                    v___x_4026_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4026_, 0, v_a_4020_);
                    v___x_4027_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4027_, 0, v___x_4026_);
                    lean_ctor_set(v___x_4027_, 1, v_b_4007_);
                    v_as_x27_4006_ = v_tail_4013_;
                    v_b_4007_ = v___x_4027_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_b_4007_);
                    if v_isShared_4023_ == 0 {
                        v___x_4030_ = v___x_4022_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4020_);
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
    mut v_as_x27_4035_: *mut LeanObject,
    mut v_b_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
    mut v___y_4038_: *mut LeanObject,
    mut v___y_4039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4040_: *mut LeanObject = core::ptr::null_mut();
    v_res_4040_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
        v_as_x27_4035_,
        v_b_4036_,
        v___y_4037_,
        v___y_4038_,
    );
    lean_dec(v___y_4038_);
    lean_dec_ref(v___y_4037_);
    lean_dec(v_as_x27_4035_);
    return v_res_4040_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27___redArg(
    mut v_jobs_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4059_: u8 = 0;
    let mut v_a_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4045_ = lean_st_ref_get(v_a_4043_);
                v___x_4046_ = lean_box(0);
                v___x_4047_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(
                    v_jobs_4041_,
                    v___x_4046_,
                    v_a_4042_,
                    v_a_4043_,
                );
                if lean_obj_tag(v___x_4047_) == 0 {
                    v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
                    lean_inc(v_a_4048_);
                    lean_dec_ref_known(v___x_4047_, 1);
                    v___x_4049_ =
                        l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
                            v_a_4048_,
                            v___x_4046_,
                            v_a_4042_,
                            v_a_4043_,
                        );
                    lean_dec(v_a_4048_);
                    if lean_obj_tag(v___x_4049_) == 0 {
                        v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4059_ = (!lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4059_ == 0 {
                            v___x_4052_ = v___x_4049_;
                            v_isShared_4053_ = v_isSharedCheck_4059_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4050_);
                            lean_dec(v___x_4049_);
                            v___x_4052_ = lean_box(0);
                            v_isShared_4053_ = v_isSharedCheck_4059_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4045_);
                        return v___x_4049_;
                    }
                } else {
                    lean_dec(v___x_4045_);
                    v_a_4060_ = lean_ctor_get(v___x_4047_, 0);
                    v_isSharedCheck_4067_ = (!lean_is_exclusive(v___x_4047_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4062_ = v___x_4047_;
                        v_isShared_4063_ = v_isSharedCheck_4067_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4060_);
                        lean_dec(v___x_4047_);
                        v___x_4062_ = lean_box(0);
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
                    lean_ctor_set(v___x_4052_, 0, v___x_4055_);
                    v___x_4057_ = v___x_4052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4055_);
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
                    v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
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
    mut v_jobs_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4072_: *mut LeanObject = core::ptr::null_mut();
    v_res_4072_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_4068_, v_a_4069_, v_a_4070_);
    lean_dec(v_a_4070_);
    lean_dec_ref(v_a_4069_);
    return v_res_4072_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27(
    mut v_00_u03b1_4073_: *mut LeanObject,
    mut v_jobs_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    v___x_4078_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_4074_, v_a_4075_, v_a_4076_);
    return v___x_4078_;
}
pub unsafe fn l_Lean_Core_CoreM_par_x27___boxed(
    mut v_00_u03b1_4079_: *mut LeanObject,
    mut v_jobs_4080_: *mut LeanObject,
    mut v_a_4081_: *mut LeanObject,
    mut v_a_4082_: *mut LeanObject,
    mut v_a_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4084_: *mut LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_4079_, v_jobs_4080_, v_a_4081_, v_a_4082_);
    lean_dec(v_a_4082_);
    lean_dec_ref(v_a_4081_);
    return v_res_4084_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(
    mut v_00_u03b1_4085_: *mut LeanObject,
    mut v_as_4086_: *mut LeanObject,
    mut v_as_x27_4087_: *mut LeanObject,
    mut v_b_4088_: *mut LeanObject,
    mut v_a_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    v___x_4093_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(
        v_as_x27_4087_,
        v_b_4088_,
        v___y_4090_,
        v___y_4091_,
    );
    return v___x_4093_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(
    mut v_00_u03b1_4094_: *mut LeanObject,
    mut v_as_4095_: *mut LeanObject,
    mut v_as_x27_4096_: *mut LeanObject,
    mut v_b_4097_: *mut LeanObject,
    mut v_a_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4102_: *mut LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(
        v_00_u03b1_4094_,
        v_as_4095_,
        v_as_x27_4096_,
        v_b_4097_,
        v_a_4098_,
        v___y_4099_,
        v___y_4100_,
    );
    lean_dec(v___y_4100_);
    lean_dec_ref(v___y_4099_);
    lean_dec(v_as_x27_4096_);
    lean_dec(v_as_4095_);
    return v_res_4102_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(
    mut v_a_4103_: *mut LeanObject,
    mut v___x_4104_: *mut LeanObject,
    mut v_____r_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    v___x_4109_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4109_, 0, v_a_4103_);
    v___x_4110_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4110_, 0, v___x_4109_);
    lean_ctor_set(v___x_4110_, 1, v___x_4104_);
    v___x_4111_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4111_, 0, v___x_4110_);
    v___x_4112_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4112_, 0, v___x_4111_);
    return v___x_4112_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_4113_: *mut LeanObject,
    mut v___x_4114_: *mut LeanObject,
    mut v_____r_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(
            v_a_4113_,
            v___x_4114_,
            v_____r_4115_,
            v___y_4116_,
            v___y_4117_,
        );
    lean_dec(v___y_4117_);
    lean_dec_ref(v___y_4116_);
    return v_res_4119_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(
    mut v_cancel_4123_: u8,
    mut v_fst_4124_: *mut LeanObject,
    mut v_a_4125_: *mut LeanObject,
    mut v_b_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v_a_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v_a_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: u8 = 0;
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4125_) == 0 {
                    lean_dec_ref(v_fst_4124_);
                    v___x_4130_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4130_, 0, v_b_4126_);
                    return v___x_4130_;
                } else {
                    lean_dec_ref(v_b_4126_);
                    v___x_4131_ = l_IO_waitAny_x27___redArg(v_a_4125_);
                    v_fst_4132_ = lean_ctor_get(v___x_4131_, 0);
                    lean_inc(v_fst_4132_);
                    v_snd_4133_ = lean_ctor_get(v___x_4131_, 1);
                    lean_inc(v_snd_4133_);
                    lean_dec_ref(v___x_4131_);
                    v___x_4155_ = lean_box(0);
                    lean_inc(v___y_4128_);
                    lean_inc_ref(v___y_4127_);
                    v___x_4156_ = lean_apply_3(v_fst_4132_, v___y_4127_, v___y_4128_, lean_box(0));
                    if lean_obj_tag(v___x_4156_) == 0 {
                        if v_cancel_4123_ == 0 {
                            v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
                            lean_inc(v_a_4157_);
                            lean_dec_ref_known(v___x_4156_, 1);
                            v___x_4158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_4157_, v___x_4155_, v___x_4155_, v___y_4127_, v___y_4128_);
                            v___y_4135_ = v___x_4158_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4159_ = lean_ctor_get(v___x_4156_, 0);
                            lean_inc(v_a_4159_);
                            lean_dec_ref_known(v___x_4156_, 1);
                            lean_inc_ref(v_fst_4124_);
                            v___x_4160_ = lean_apply_1(v_fst_4124_, lean_box(0));
                            v___x_4161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_4159_, v___x_4155_, v___x_4160_, v___y_4127_, v___y_4128_);
                            v___y_4135_ = v___x_4161_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4162_ = lean_ctor_get(v___x_4156_, 0);
                        v_isSharedCheck_4175_ = (!lean_is_exclusive(v___x_4156_)) as u8;
                        if v_isSharedCheck_4175_ == 0 {
                            v___x_4164_ = v___x_4156_;
                            v_isShared_4165_ = v_isSharedCheck_4175_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4162_);
                            lean_dec(v___x_4156_);
                            v___x_4164_ = lean_box(0);
                            v_isShared_4165_ = v_isSharedCheck_4175_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4135_) == 0 {
                    v_a_4136_ = lean_ctor_get(v___y_4135_, 0);
                    v_isSharedCheck_4146_ = (!lean_is_exclusive(v___y_4135_)) as u8;
                    if v_isSharedCheck_4146_ == 0 {
                        v___x_4138_ = v___y_4135_;
                        v_isShared_4139_ = v_isSharedCheck_4146_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4136_);
                        lean_dec(v___y_4135_);
                        v___x_4138_ = lean_box(0);
                        v_isShared_4139_ = v_isSharedCheck_4146_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4133_);
                    lean_dec_ref(v_fst_4124_);
                    v_a_4147_ = lean_ctor_get(v___y_4135_, 0);
                    v_isSharedCheck_4154_ = (!lean_is_exclusive(v___y_4135_)) as u8;
                    if v_isSharedCheck_4154_ == 0 {
                        v___x_4149_ = v___y_4135_;
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4147_);
                        lean_dec(v___y_4135_);
                        v___x_4149_ = lean_box(0);
                        v_isShared_4150_ = v_isSharedCheck_4154_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4136_) == 0 {
                    lean_dec(v_snd_4133_);
                    lean_dec_ref(v_fst_4124_);
                    v_a_4140_ = lean_ctor_get(v_a_4136_, 0);
                    lean_inc(v_a_4140_);
                    lean_dec_ref_known(v_a_4136_, 1);
                    if v_isShared_4139_ == 0 {
                        lean_ctor_set(v___x_4138_, 0, v_a_4140_);
                        v___x_4142_ = v___x_4138_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4140_);
                        v___x_4142_ = v_reuseFailAlloc_4143_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4138_);
                    v_a_4144_ = lean_ctor_get(v_a_4136_, 0);
                    lean_inc(v_a_4144_);
                    lean_dec_ref_known(v_a_4136_, 1);
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
                    v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
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
                    lean_inc(v_a_4162_);
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
                    lean_del_object(v___x_4164_);
                    lean_dec(v_a_4162_);
                    v_a_4125_ = v_snd_4133_;
                    v_b_4126_ = v___x_4166_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_snd_4133_);
                    lean_dec_ref(v_fst_4124_);
                    if v_isShared_4165_ == 0 {
                        v___x_4171_ = v___x_4164_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4162_);
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
    mut v_cancel_4176_: *mut LeanObject,
    mut v_fst_4177_: *mut LeanObject,
    mut v_a_4178_: *mut LeanObject,
    mut v_b_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_4183_: u8 = 0;
    let mut v_res_4184_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4183_ = (lean_unbox(v_cancel_4176_) as u8);
    v_res_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(
        v_cancel_boxed_4183_,
        v_fst_4177_,
        v_a_4178_,
        v_b_4179_,
        v___y_4180_,
        v___y_4181_,
    );
    lean_dec(v___y_4181_);
    lean_dec_ref(v___y_4180_);
    return v_res_4184_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4185_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    v___x_4186_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0);
    v___x_4187_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4187_, 0, v___x_4186_);
    return v___x_4187_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    v___x_4188_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
    v___x_4189_ = lean_unsigned_to_nat(0);
    v___x_4190_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4190_, 0, v___x_4189_);
    lean_ctor_set(v___x_4190_, 1, v___x_4189_);
    lean_ctor_set(v___x_4190_, 2, v___x_4189_);
    lean_ctor_set(v___x_4190_, 3, v___x_4189_);
    lean_ctor_set(v___x_4190_, 4, v___x_4188_);
    lean_ctor_set(v___x_4190_, 5, v___x_4188_);
    lean_ctor_set(v___x_4190_, 6, v___x_4188_);
    lean_ctor_set(v___x_4190_, 7, v___x_4188_);
    lean_ctor_set(v___x_4190_, 8, v___x_4188_);
    lean_ctor_set(v___x_4190_, 9, v___x_4188_);
    return v___x_4190_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v___x_4191_ = lean_unsigned_to_nat(32);
    v___x_4192_ = lean_mk_empty_array_with_capacity(v___x_4191_);
    v___x_4193_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4193_, 0, v___x_4192_);
    return v___x_4193_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    v___x_4194_ = 5usize;
    v___x_4195_ = lean_unsigned_to_nat(0);
    v___x_4196_ = lean_unsigned_to_nat(32);
    v___x_4197_ = lean_mk_empty_array_with_capacity(v___x_4196_);
    v___x_4198_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
    v___x_4199_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4199_, 0, v___x_4198_);
    lean_ctor_set(v___x_4199_, 1, v___x_4197_);
    lean_ctor_set(v___x_4199_, 2, v___x_4195_);
    lean_ctor_set(v___x_4199_, 3, v___x_4195_);
    lean_ctor_set_usize(v___x_4199_, 4, v___x_4194_);
    return v___x_4199_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    v___x_4200_ = lean_box(1);
    v___x_4201_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
    v___x_4202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
    v___x_4203_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4203_, 0, v___x_4202_);
    lean_ctor_set(v___x_4203_, 1, v___x_4201_);
    lean_ctor_set(v___x_4203_, 2, v___x_4200_);
    return v___x_4203_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(
    mut v_msgData_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
    mut v___y_4206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    v___x_4208_ = lean_st_ref_get(v___y_4206_);
    v_env_4209_ = lean_ctor_get(v___x_4208_, 0);
    lean_inc_ref(v_env_4209_);
    lean_dec(v___x_4208_);
    v_options_4210_ = lean_ctor_get(v___y_4205_, 2);
    v___x_4211_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
    v___x_4212_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
    lean_inc_ref(v_options_4210_);
    v___x_4213_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4213_, 0, v_env_4209_);
    lean_ctor_set(v___x_4213_, 1, v___x_4211_);
    lean_ctor_set(v___x_4213_, 2, v___x_4212_);
    lean_ctor_set(v___x_4213_, 3, v_options_4210_);
    v___x_4214_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4214_, 0, v___x_4213_);
    lean_ctor_set(v___x_4214_, 1, v_msgData_4204_);
    v___x_4215_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4215_, 0, v___x_4214_);
    return v___x_4215_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4220_: *mut LeanObject = core::ptr::null_mut();
    v_res_4220_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_4216_, v___y_4217_, v___y_4218_);
    lean_dec(v___y_4218_);
    lean_dec_ref(v___y_4217_);
    return v_res_4220_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
    mut v_msg_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4225_ = lean_ctor_get(v___y_4222_, 5);
                v___x_4226_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_4221_, v___y_4222_, v___y_4223_);
                v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
                v_isSharedCheck_4235_ = (!lean_is_exclusive(v___x_4226_)) as u8;
                if v_isSharedCheck_4235_ == 0 {
                    v___x_4229_ = v___x_4226_;
                    v_isShared_4230_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4227_);
                    lean_dec(v___x_4226_);
                    v___x_4229_ = lean_box(0);
                    v_isShared_4230_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4225_);
                v___x_4231_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4231_, 0, v_ref_4225_);
                lean_ctor_set(v___x_4231_, 1, v_a_4227_);
                if v_isShared_4230_ == 0 {
                    lean_ctor_set_tag(v___x_4229_, 1);
                    lean_ctor_set(v___x_4229_, 0, v___x_4231_);
                    v___x_4233_ = v___x_4229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
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
    mut v_msg_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4240_: *mut LeanObject = core::ptr::null_mut();
    v_res_4240_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
        v_msg_4236_,
        v___y_4237_,
        v___y_4238_,
    );
    lean_dec(v___y_4238_);
    lean_dec_ref(v___y_4237_);
    return v_res_4240_;
}
pub unsafe fn _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Lean_Core_CoreM_parFirst___redArg___closed__0;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst___redArg(
    mut v_jobs_4244_: *mut LeanObject,
    mut v_cancel_4245_: u8,
    mut v_a_4246_: *mut LeanObject,
    mut v_a_4247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v_fst_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_a_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4274_: u8 = 0;
    let mut v_a_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4249_) == 0 {
                    v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
                    lean_inc(v_a_4250_);
                    lean_dec_ref_known(v___x_4249_, 1);
                    v_fst_4251_ = lean_ctor_get(v_a_4250_, 0);
                    lean_inc(v_fst_4251_);
                    v_snd_4252_ = lean_ctor_get(v_a_4250_, 1);
                    lean_inc(v_snd_4252_);
                    lean_dec(v_a_4250_);
                    v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_4254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_4245_, v_fst_4251_, v_snd_4252_, v___x_4253_, v_a_4246_, v_a_4247_);
                    if lean_obj_tag(v___x_4254_) == 0 {
                        v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
                        v_isSharedCheck_4266_ = (!lean_is_exclusive(v___x_4254_)) as u8;
                        if v_isSharedCheck_4266_ == 0 {
                            v___x_4257_ = v___x_4254_;
                            v_isShared_4258_ = v_isSharedCheck_4266_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4255_);
                            lean_dec(v___x_4254_);
                            v___x_4257_ = lean_box(0);
                            v_isShared_4258_ = v_isSharedCheck_4266_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4267_ = lean_ctor_get(v___x_4254_, 0);
                        v_isSharedCheck_4274_ = (!lean_is_exclusive(v___x_4254_)) as u8;
                        if v_isSharedCheck_4274_ == 0 {
                            v___x_4269_ = v___x_4254_;
                            v_isShared_4270_ = v_isSharedCheck_4274_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4267_);
                            lean_dec(v___x_4254_);
                            v___x_4269_ = lean_box(0);
                            v_isShared_4270_ = v_isSharedCheck_4274_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4275_ = lean_ctor_get(v___x_4249_, 0);
                    v_isSharedCheck_4282_ = (!lean_is_exclusive(v___x_4249_)) as u8;
                    if v_isSharedCheck_4282_ == 0 {
                        v___x_4277_ = v___x_4249_;
                        v_isShared_4278_ = v_isSharedCheck_4282_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4275_);
                        lean_dec(v___x_4249_);
                        v___x_4277_ = lean_box(0);
                        v_isShared_4278_ = v_isSharedCheck_4282_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4259_ = lean_ctor_get(v_a_4255_, 0);
                lean_inc(v_fst_4259_);
                lean_dec(v_a_4255_);
                if lean_obj_tag(v_fst_4259_) == 0 {
                    lean_del_object(v___x_4257_);
                    v___x_4260_ = lean_obj_once(
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
                    v_val_4262_ = lean_ctor_get(v_fst_4259_, 0);
                    lean_inc(v_val_4262_);
                    lean_dec_ref_known(v_fst_4259_, 1);
                    if v_isShared_4258_ == 0 {
                        lean_ctor_set(v___x_4257_, 0, v_val_4262_);
                        v___x_4264_ = v___x_4257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_val_4262_);
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
                    v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
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
                    v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
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
    mut v_jobs_4283_: *mut LeanObject,
    mut v_cancel_4284_: *mut LeanObject,
    mut v_a_4285_: *mut LeanObject,
    mut v_a_4286_: *mut LeanObject,
    mut v_a_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_4288_: u8 = 0;
    let mut v_res_4289_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4288_ = (lean_unbox(v_cancel_4284_) as u8);
    v_res_4289_ = l_Lean_Core_CoreM_parFirst___redArg(
        v_jobs_4283_,
        v_cancel_boxed_4288_,
        v_a_4285_,
        v_a_4286_,
    );
    lean_dec(v_a_4286_);
    lean_dec_ref(v_a_4285_);
    return v_res_4289_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst(
    mut v_00_u03b1_4290_: *mut LeanObject,
    mut v_jobs_4291_: *mut LeanObject,
    mut v_cancel_4292_: u8,
    mut v_a_4293_: *mut LeanObject,
    mut v_a_4294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4296_ =
        l_Lean_Core_CoreM_parFirst___redArg(v_jobs_4291_, v_cancel_4292_, v_a_4293_, v_a_4294_);
    return v___x_4296_;
}
pub unsafe fn l_Lean_Core_CoreM_parFirst___boxed(
    mut v_00_u03b1_4297_: *mut LeanObject,
    mut v_jobs_4298_: *mut LeanObject,
    mut v_cancel_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_4303_: u8 = 0;
    let mut v_res_4304_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4303_ = (lean_unbox(v_cancel_4299_) as u8);
    v_res_4304_ = l_Lean_Core_CoreM_parFirst(
        v_00_u03b1_4297_,
        v_jobs_4298_,
        v_cancel_boxed_4303_,
        v_a_4300_,
        v_a_4301_,
    );
    lean_dec(v_a_4301_);
    lean_dec_ref(v_a_4300_);
    return v_res_4304_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(
    mut v_00_u03b1_4305_: *mut LeanObject,
    mut v_cancel_4306_: u8,
    mut v_fst_4307_: *mut LeanObject,
    mut v_inst_4308_: *mut LeanObject,
    mut v_R_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_b_4311_: *mut LeanObject,
    mut v_c_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4317_: *mut LeanObject,
    mut v_cancel_4318_: *mut LeanObject,
    mut v_fst_4319_: *mut LeanObject,
    mut v_inst_4320_: *mut LeanObject,
    mut v_R_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_b_4323_: *mut LeanObject,
    mut v_c_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_4328_: u8 = 0;
    let mut v_res_4329_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4328_ = (lean_unbox(v_cancel_4318_) as u8);
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
    lean_dec(v___y_4326_);
    lean_dec_ref(v___y_4325_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(
    mut v_00_u03b1_4330_: *mut LeanObject,
    mut v_msg_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(
        v_msg_4331_,
        v___y_4332_,
        v___y_4333_,
    );
    return v___x_4335_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(
    mut v_00_u03b1_4336_: *mut LeanObject,
    mut v_msg_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4341_: *mut LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(
        v_00_u03b1_4336_,
        v_msg_4337_,
        v___y_4338_,
        v___y_4339_,
    );
    lean_dec(v___y_4339_);
    lean_dec_ref(v___y_4338_);
    return v_res_4341_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
    mut v_x_4342_: *mut LeanObject,
    mut v_x_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4342_) == 0 {
                    v___x_4349_ = l_List_reverse___redArg(v_x_4343_);
                    v___x_4350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4350_, 0, v___x_4349_);
                    return v___x_4350_;
                } else {
                    v_head_4351_ = lean_ctor_get(v_x_4342_, 0);
                    v_tail_4352_ = lean_ctor_get(v_x_4342_, 1);
                    v_isSharedCheck_4370_ = (!lean_is_exclusive(v_x_4342_)) as u8;
                    if v_isSharedCheck_4370_ == 0 {
                        v___x_4354_ = v_x_4342_;
                        v_isShared_4355_ = v_isSharedCheck_4370_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4352_);
                        lean_inc(v_head_4351_);
                        lean_dec(v_x_4342_);
                        v___x_4354_ = lean_box(0);
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
                if lean_obj_tag(v___x_4356_) == 0 {
                    v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
                    lean_inc(v_a_4357_);
                    lean_dec_ref_known(v___x_4356_, 1);
                    if v_isShared_4355_ == 0 {
                        lean_ctor_set(v___x_4354_, 1, v_x_4343_);
                        lean_ctor_set(v___x_4354_, 0, v_a_4357_);
                        v___x_4359_ = v___x_4354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4357_);
                        lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_x_4343_);
                        v___x_4359_ = v_reuseFailAlloc_4361_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4354_);
                    lean_dec(v_tail_4352_);
                    lean_dec(v_x_4343_);
                    v_a_4362_ = lean_ctor_get(v___x_4356_, 0);
                    v_isSharedCheck_4369_ = (!lean_is_exclusive(v___x_4356_)) as u8;
                    if v_isSharedCheck_4369_ == 0 {
                        v___x_4364_ = v___x_4356_;
                        v_isShared_4365_ = v_isSharedCheck_4369_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4362_);
                        lean_dec(v___x_4356_);
                        v___x_4364_ = lean_box(0);
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
                    v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
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
    mut v_x_4371_: *mut LeanObject,
    mut v_x_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4378_: *mut LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
        v_x_4371_,
        v_x_4372_,
        v___y_4373_,
        v___y_4374_,
        v___y_4375_,
        v___y_4376_,
    );
    lean_dec(v___y_4376_);
    lean_dec_ref(v___y_4375_);
    lean_dec(v___y_4374_);
    lean_dec_ref(v___y_4373_);
    return v_res_4378_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
    mut v_as_x27_4379_: *mut LeanObject,
    mut v_b_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4395_: u8 = 0;
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4401_: u8 = 0;
    let mut v___x_2329__overap_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_a_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4379_) == 0 {
                    v___x_4386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4386_, 0, v_b_4380_);
                    return v___x_4386_;
                } else {
                    v_head_4387_ = lean_ctor_get(v_as_x27_4379_, 0);
                    v_tail_4388_ = lean_ctor_get(v_as_x27_4379_, 1);
                    lean_inc(v_head_4387_);
                    v___x_2329__overap_4402_ = lean_task_get_own(v_head_4387_);
                    lean_inc(v___y_4384_);
                    lean_inc_ref(v___y_4383_);
                    lean_inc(v___y_4382_);
                    lean_inc_ref(v___y_4381_);
                    v___x_4403_ = lean_apply_5(
                        v___x_2329__overap_4402_,
                        v___y_4381_,
                        v___y_4382_,
                        v___y_4383_,
                        v___y_4384_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4403_) == 0 {
                        v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
                        lean_inc(v_a_4404_);
                        lean_dec_ref_known(v___x_4403_, 1);
                        v___x_4405_ = l_Lean_Meta_saveState___redArg(v___y_4382_, v___y_4384_);
                        if lean_obj_tag(v___x_4405_) == 0 {
                            v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
                            v_isSharedCheck_4414_ = (!lean_is_exclusive(v___x_4405_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4408_ = v___x_4405_;
                                v_isShared_4409_ = v_isSharedCheck_4414_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4406_);
                                lean_dec(v___x_4405_);
                                v___x_4408_ = lean_box(0);
                                v_isShared_4409_ = v_isSharedCheck_4414_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4404_);
                            v_a_4415_ = lean_ctor_get(v___x_4405_, 0);
                            lean_inc(v_a_4415_);
                            lean_dec_ref_known(v___x_4405_, 1);
                            v_a_4399_ = v_a_4415_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4416_ = lean_ctor_get(v___x_4403_, 0);
                        lean_inc(v_a_4416_);
                        lean_dec_ref_known(v___x_4403_, 1);
                        v_a_4399_ = v_a_4416_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4391_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4391_, 0, v_a_4390_);
                lean_ctor_set(v___x_4391_, 1, v_b_4380_);
                v_as_x27_4379_ = v_tail_4388_;
                v_b_4380_ = v___x_4391_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_4395_ == 0 {
                    v___x_4396_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4396_, 0, v___y_4394_);
                    v_a_4390_ = v___x_4396_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_b_4380_);
                    v___x_4397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4397_, 0, v___y_4394_);
                    return v___x_4397_;
                }
            }
            3 => {
                v___x_4400_ = l_Lean_Exception_isInterrupt(v_a_4399_);
                if v___x_4400_ == 0 {
                    lean_inc_ref(v_a_4399_);
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
                v___x_4410_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4410_, 0, v_a_4404_);
                lean_ctor_set(v___x_4410_, 1, v_a_4406_);
                if v_isShared_4409_ == 0 {
                    lean_ctor_set_tag(v___x_4408_, 1);
                    lean_ctor_set(v___x_4408_, 0, v___x_4410_);
                    v___x_4412_ = v___x_4408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
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
    mut v_as_x27_4417_: *mut LeanObject,
    mut v_b_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
    mut v___y_4420_: *mut LeanObject,
    mut v___y_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4424_: *mut LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
        v_as_x27_4417_,
        v_b_4418_,
        v___y_4419_,
        v___y_4420_,
        v___y_4421_,
        v___y_4422_,
    );
    lean_dec(v___y_4422_);
    lean_dec_ref(v___y_4421_);
    lean_dec(v___y_4420_);
    lean_dec_ref(v___y_4419_);
    lean_dec(v_as_x27_4417_);
    return v_res_4424_;
}
pub unsafe fn l_Lean_Meta_MetaM_par___redArg(
    mut v_jobs_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
    mut v_a_4429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v_a_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4431_ = lean_st_ref_get(v_a_4427_);
                v___x_4432_ = lean_box(0);
                v___x_4433_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
                    v_jobs_4425_,
                    v___x_4432_,
                    v_a_4426_,
                    v_a_4427_,
                    v_a_4428_,
                    v_a_4429_,
                );
                if lean_obj_tag(v___x_4433_) == 0 {
                    v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
                    lean_inc(v_a_4434_);
                    lean_dec_ref_known(v___x_4433_, 1);
                    v___x_4435_ =
                        l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(
                            v_a_4434_,
                            v___x_4432_,
                            v_a_4426_,
                            v_a_4427_,
                            v_a_4428_,
                            v_a_4429_,
                        );
                    lean_dec(v_a_4434_);
                    if lean_obj_tag(v___x_4435_) == 0 {
                        v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
                        v_isSharedCheck_4445_ = (!lean_is_exclusive(v___x_4435_)) as u8;
                        if v_isSharedCheck_4445_ == 0 {
                            v___x_4438_ = v___x_4435_;
                            v_isShared_4439_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4436_);
                            lean_dec(v___x_4435_);
                            v___x_4438_ = lean_box(0);
                            v_isShared_4439_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4431_);
                        return v___x_4435_;
                    }
                } else {
                    lean_dec(v___x_4431_);
                    v_a_4446_ = lean_ctor_get(v___x_4433_, 0);
                    v_isSharedCheck_4453_ = (!lean_is_exclusive(v___x_4433_)) as u8;
                    if v_isSharedCheck_4453_ == 0 {
                        v___x_4448_ = v___x_4433_;
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4446_);
                        lean_dec(v___x_4433_);
                        v___x_4448_ = lean_box(0);
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
                    lean_ctor_set(v___x_4438_, 0, v___x_4441_);
                    v___x_4443_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
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
                    v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
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
    mut v_jobs_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4460_: *mut LeanObject = core::ptr::null_mut();
    v_res_4460_ =
        l_Lean_Meta_MetaM_par___redArg(v_jobs_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
    lean_dec(v_a_4458_);
    lean_dec_ref(v_a_4457_);
    lean_dec(v_a_4456_);
    lean_dec_ref(v_a_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_Meta_MetaM_par(
    mut v_00_u03b1_4461_: *mut LeanObject,
    mut v_jobs_4462_: *mut LeanObject,
    mut v_a_4463_: *mut LeanObject,
    mut v_a_4464_: *mut LeanObject,
    mut v_a_4465_: *mut LeanObject,
    mut v_a_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4468_ =
        l_Lean_Meta_MetaM_par___redArg(v_jobs_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
    return v___x_4468_;
}
pub unsafe fn l_Lean_Meta_MetaM_par___boxed(
    mut v_00_u03b1_4469_: *mut LeanObject,
    mut v_jobs_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
    mut v_a_4473_: *mut LeanObject,
    mut v_a_4474_: *mut LeanObject,
    mut v_a_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_Meta_MetaM_par(
        v_00_u03b1_4469_,
        v_jobs_4470_,
        v_a_4471_,
        v_a_4472_,
        v_a_4473_,
        v_a_4474_,
    );
    lean_dec(v_a_4474_);
    lean_dec_ref(v_a_4473_);
    lean_dec(v_a_4472_);
    lean_dec_ref(v_a_4471_);
    return v_res_4476_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(
    mut v_00_u03b1_4477_: *mut LeanObject,
    mut v_x_4478_: *mut LeanObject,
    mut v_x_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4486_: *mut LeanObject,
    mut v_x_4487_: *mut LeanObject,
    mut v_x_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4494_: *mut LeanObject = core::ptr::null_mut();
    v_res_4494_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(
        v_00_u03b1_4486_,
        v_x_4487_,
        v_x_4488_,
        v___y_4489_,
        v___y_4490_,
        v___y_4491_,
        v___y_4492_,
    );
    lean_dec(v___y_4492_);
    lean_dec_ref(v___y_4491_);
    lean_dec(v___y_4490_);
    lean_dec_ref(v___y_4489_);
    return v_res_4494_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(
    mut v_00_u03b1_4495_: *mut LeanObject,
    mut v_as_4496_: *mut LeanObject,
    mut v_as_x27_4497_: *mut LeanObject,
    mut v_b_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4506_: *mut LeanObject,
    mut v_as_4507_: *mut LeanObject,
    mut v_as_x27_4508_: *mut LeanObject,
    mut v_b_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4516_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4514_);
    lean_dec_ref(v___y_4513_);
    lean_dec(v___y_4512_);
    lean_dec_ref(v___y_4511_);
    lean_dec(v_as_x27_4508_);
    lean_dec(v_as_4507_);
    return v_res_4516_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
    mut v_as_x27_4517_: *mut LeanObject,
    mut v_b_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032__overap_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4536_: u8 = 0;
    let mut v___y_4538_: u8 = 0;
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: u8 = 0;
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4517_) == 0 {
                    v___x_4524_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4524_, 0, v_b_4518_);
                    return v___x_4524_;
                } else {
                    v_head_4525_ = lean_ctor_get(v_as_x27_4517_, 0);
                    v_tail_4526_ = lean_ctor_get(v_as_x27_4517_, 1);
                    lean_inc(v_head_4525_);
                    v___x_2032__overap_4527_ = lean_task_get_own(v_head_4525_);
                    lean_inc(v___y_4522_);
                    lean_inc_ref(v___y_4521_);
                    lean_inc(v___y_4520_);
                    lean_inc_ref(v___y_4519_);
                    v___x_4528_ = lean_apply_5(
                        v___x_2032__overap_4527_,
                        v___y_4519_,
                        v___y_4520_,
                        v___y_4521_,
                        v___y_4522_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4528_) == 0 {
                        v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
                        lean_inc(v_a_4529_);
                        lean_dec_ref_known(v___x_4528_, 1);
                        v___x_4530_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4530_, 0, v_a_4529_);
                        v___x_4531_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4531_, 0, v___x_4530_);
                        lean_ctor_set(v___x_4531_, 1, v_b_4518_);
                        v_as_x27_4517_ = v_tail_4526_;
                        v_b_4518_ = v___x_4531_;
                        state = 0;
                        continue;
                    } else {
                        v_a_4533_ = lean_ctor_get(v___x_4528_, 0);
                        v_isSharedCheck_4547_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                        if v_isSharedCheck_4547_ == 0 {
                            v___x_4535_ = v___x_4528_;
                            v_isShared_4536_ = v_isSharedCheck_4547_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4533_);
                            lean_dec(v___x_4528_);
                            v___x_4535_ = lean_box(0);
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
                    lean_inc(v_a_4533_);
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
                    lean_del_object(v___x_4535_);
                    v___x_4539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4539_, 0, v_a_4533_);
                    v___x_4540_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4540_, 0, v___x_4539_);
                    lean_ctor_set(v___x_4540_, 1, v_b_4518_);
                    v_as_x27_4517_ = v_tail_4526_;
                    v_b_4518_ = v___x_4540_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_b_4518_);
                    if v_isShared_4536_ == 0 {
                        v___x_4543_ = v___x_4535_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4533_);
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
    mut v_as_x27_4548_: *mut LeanObject,
    mut v_b_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4555_: *mut LeanObject = core::ptr::null_mut();
    v_res_4555_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
        v_as_x27_4548_,
        v_b_4549_,
        v___y_4550_,
        v___y_4551_,
        v___y_4552_,
        v___y_4553_,
    );
    lean_dec(v___y_4553_);
    lean_dec_ref(v___y_4552_);
    lean_dec(v___y_4551_);
    lean_dec_ref(v___y_4550_);
    lean_dec(v_as_x27_4548_);
    return v_res_4555_;
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27___redArg(
    mut v_jobs_4556_: *mut LeanObject,
    mut v_a_4557_: *mut LeanObject,
    mut v_a_4558_: *mut LeanObject,
    mut v_a_4559_: *mut LeanObject,
    mut v_a_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4562_ = lean_st_ref_get(v_a_4558_);
                v___x_4563_ = lean_box(0);
                v___x_4564_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(
                    v_jobs_4556_,
                    v___x_4563_,
                    v_a_4557_,
                    v_a_4558_,
                    v_a_4559_,
                    v_a_4560_,
                );
                if lean_obj_tag(v___x_4564_) == 0 {
                    v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
                    lean_inc(v_a_4565_);
                    lean_dec_ref_known(v___x_4564_, 1);
                    v___x_4566_ =
                        l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(
                            v_a_4565_,
                            v___x_4563_,
                            v_a_4557_,
                            v_a_4558_,
                            v_a_4559_,
                            v_a_4560_,
                        );
                    lean_dec(v_a_4565_);
                    if lean_obj_tag(v___x_4566_) == 0 {
                        v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
                        v_isSharedCheck_4576_ = (!lean_is_exclusive(v___x_4566_)) as u8;
                        if v_isSharedCheck_4576_ == 0 {
                            v___x_4569_ = v___x_4566_;
                            v_isShared_4570_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4567_);
                            lean_dec(v___x_4566_);
                            v___x_4569_ = lean_box(0);
                            v_isShared_4570_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4562_);
                        return v___x_4566_;
                    }
                } else {
                    lean_dec(v___x_4562_);
                    v_a_4577_ = lean_ctor_get(v___x_4564_, 0);
                    v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4564_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4564_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4577_);
                        lean_dec(v___x_4564_);
                        v___x_4579_ = lean_box(0);
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
                    lean_ctor_set(v___x_4569_, 0, v___x_4572_);
                    v___x_4574_ = v___x_4569_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
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
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
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
    mut v_jobs_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
    mut v_a_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4591_: *mut LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lean_Meta_MetaM_par_x27___redArg(
        v_jobs_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
    );
    lean_dec(v_a_4589_);
    lean_dec_ref(v_a_4588_);
    lean_dec(v_a_4587_);
    lean_dec_ref(v_a_4586_);
    return v_res_4591_;
}
pub unsafe fn l_Lean_Meta_MetaM_par_x27(
    mut v_00_u03b1_4592_: *mut LeanObject,
    mut v_jobs_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
    mut v_a_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
    mut v_a_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4600_: *mut LeanObject,
    mut v_jobs_4601_: *mut LeanObject,
    mut v_a_4602_: *mut LeanObject,
    mut v_a_4603_: *mut LeanObject,
    mut v_a_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4607_: *mut LeanObject = core::ptr::null_mut();
    v_res_4607_ = l_Lean_Meta_MetaM_par_x27(
        v_00_u03b1_4600_,
        v_jobs_4601_,
        v_a_4602_,
        v_a_4603_,
        v_a_4604_,
        v_a_4605_,
    );
    lean_dec(v_a_4605_);
    lean_dec_ref(v_a_4604_);
    lean_dec(v_a_4603_);
    lean_dec_ref(v_a_4602_);
    return v_res_4607_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(
    mut v_00_u03b1_4608_: *mut LeanObject,
    mut v_as_4609_: *mut LeanObject,
    mut v_as_x27_4610_: *mut LeanObject,
    mut v_b_4611_: *mut LeanObject,
    mut v_a_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4619_: *mut LeanObject,
    mut v_as_4620_: *mut LeanObject,
    mut v_as_x27_4621_: *mut LeanObject,
    mut v_b_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4629_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4627_);
    lean_dec_ref(v___y_4626_);
    lean_dec(v___y_4625_);
    lean_dec_ref(v___y_4624_);
    lean_dec(v_as_x27_4621_);
    lean_dec(v_as_4620_);
    return v_res_4629_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
    mut v_x_4630_: *mut LeanObject,
    mut v_x_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_isSharedCheck_4658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4630_) == 0 {
                    v___x_4637_ = l_List_reverse___redArg(v_x_4631_);
                    v___x_4638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4638_, 0, v___x_4637_);
                    return v___x_4638_;
                } else {
                    v_head_4639_ = lean_ctor_get(v_x_4630_, 0);
                    v_tail_4640_ = lean_ctor_get(v_x_4630_, 1);
                    v_isSharedCheck_4658_ = (!lean_is_exclusive(v_x_4630_)) as u8;
                    if v_isSharedCheck_4658_ == 0 {
                        v___x_4642_ = v_x_4630_;
                        v_isShared_4643_ = v_isSharedCheck_4658_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4640_);
                        lean_inc(v_head_4639_);
                        lean_dec(v_x_4630_);
                        v___x_4642_ = lean_box(0);
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
                if lean_obj_tag(v___x_4644_) == 0 {
                    v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
                    lean_inc(v_a_4645_);
                    lean_dec_ref_known(v___x_4644_, 1);
                    if v_isShared_4643_ == 0 {
                        lean_ctor_set(v___x_4642_, 1, v_x_4631_);
                        lean_ctor_set(v___x_4642_, 0, v_a_4645_);
                        v___x_4647_ = v___x_4642_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4645_);
                        lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_x_4631_);
                        v___x_4647_ = v_reuseFailAlloc_4649_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4642_);
                    lean_dec(v_tail_4640_);
                    lean_dec(v_x_4631_);
                    v_a_4650_ = lean_ctor_get(v___x_4644_, 0);
                    v_isSharedCheck_4657_ = (!lean_is_exclusive(v___x_4644_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4652_ = v___x_4644_;
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4650_);
                        lean_dec(v___x_4644_);
                        v___x_4652_ = lean_box(0);
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
                    v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
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
    mut v_x_4659_: *mut LeanObject,
    mut v_x_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4666_: *mut LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
        v_x_4659_,
        v_x_4660_,
        v___y_4661_,
        v___y_4662_,
        v___y_4663_,
        v___y_4664_,
    );
    lean_dec(v___y_4664_);
    lean_dec_ref(v___y_4663_);
    lean_dec(v___y_4662_);
    lean_dec_ref(v___y_4661_);
    return v_res_4666_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel___redArg(
    mut v_jobs_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_a_4669_: *mut LeanObject,
    mut v_a_4670_: *mut LeanObject,
    mut v_a_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_isSharedCheck_4693_: u8 = 0;
    let mut v_a_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4673_ = lean_box(0);
                v___x_4674_ =
                    l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
                        v_jobs_4667_,
                        v___x_4673_,
                        v_a_4668_,
                        v_a_4669_,
                        v_a_4670_,
                        v_a_4671_,
                    );
                if lean_obj_tag(v___x_4674_) == 0 {
                    v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
                    v_isSharedCheck_4693_ = (!lean_is_exclusive(v___x_4674_)) as u8;
                    if v_isSharedCheck_4693_ == 0 {
                        v___x_4677_ = v___x_4674_;
                        v_isShared_4678_ = v_isSharedCheck_4693_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4675_);
                        lean_dec(v___x_4674_);
                        v___x_4677_ = lean_box(0);
                        v_isShared_4678_ = v_isSharedCheck_4693_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4694_ = lean_ctor_get(v___x_4674_, 0);
                    v_isSharedCheck_4701_ = (!lean_is_exclusive(v___x_4674_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v___x_4696_ = v___x_4674_;
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4694_);
                        lean_dec(v___x_4674_);
                        v___x_4696_ = lean_box(0);
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4679_ = l_List_unzipTR___redArg(v_a_4675_);
                v_fst_4680_ = lean_ctor_get(v___x_4679_, 0);
                v_snd_4681_ = lean_ctor_get(v___x_4679_, 1);
                v_isSharedCheck_4692_ = (!lean_is_exclusive(v___x_4679_)) as u8;
                if v_isSharedCheck_4692_ == 0 {
                    v___x_4683_ = v___x_4679_;
                    v_isShared_4684_ = v_isSharedCheck_4692_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4681_);
                    lean_inc(v_fst_4680_);
                    lean_dec(v___x_4679_);
                    v___x_4683_ = lean_box(0);
                    v_isShared_4684_ = v_isSharedCheck_4692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4685_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_4685_, 0, v_fst_4680_);
                if v_isShared_4684_ == 0 {
                    lean_ctor_set(v___x_4683_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4683_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4685_);
                    lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_snd_4681_);
                    v___x_4687_ = v_reuseFailAlloc_4691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4678_ == 0 {
                    lean_ctor_set(v___x_4677_, 0, v___x_4687_);
                    v___x_4689_ = v___x_4677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
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
                    v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
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
    mut v_jobs_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4708_: *mut LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(
        v_jobs_4702_,
        v_a_4703_,
        v_a_4704_,
        v_a_4705_,
        v_a_4706_,
    );
    lean_dec(v_a_4706_);
    lean_dec_ref(v_a_4705_);
    lean_dec(v_a_4704_);
    lean_dec_ref(v_a_4703_);
    return v_res_4708_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterWithCancel(
    mut v_00_u03b1_4709_: *mut LeanObject,
    mut v_jobs_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4717_: *mut LeanObject,
    mut v_jobs_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
    mut v_a_4722_: *mut LeanObject,
    mut v_a_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4724_: *mut LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Lean_Meta_MetaM_parIterWithCancel(
        v_00_u03b1_4717_,
        v_jobs_4718_,
        v_a_4719_,
        v_a_4720_,
        v_a_4721_,
        v_a_4722_,
    );
    lean_dec(v_a_4722_);
    lean_dec_ref(v_a_4721_);
    lean_dec(v_a_4720_);
    lean_dec_ref(v_a_4719_);
    return v_res_4724_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(
    mut v_00_u03b1_4725_: *mut LeanObject,
    mut v_x_4726_: *mut LeanObject,
    mut v_x_4727_: *mut LeanObject,
    mut v___y_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4734_: *mut LeanObject,
    mut v_x_4735_: *mut LeanObject,
    mut v_x_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4742_: *mut LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(
        v_00_u03b1_4734_,
        v_x_4735_,
        v_x_4736_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
    );
    lean_dec(v___y_4740_);
    lean_dec_ref(v___y_4739_);
    lean_dec(v___y_4738_);
    lean_dec_ref(v___y_4737_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIter___redArg(
    mut v_jobs_4743_: *mut LeanObject,
    mut v_a_4744_: *mut LeanObject,
    mut v_a_4745_: *mut LeanObject,
    mut v_a_4746_: *mut LeanObject,
    mut v_a_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4753_: u8 = 0;
    let mut v_snd_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut v_a_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4749_) == 0 {
                    v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
                    v_isSharedCheck_4758_ = (!lean_is_exclusive(v___x_4749_)) as u8;
                    if v_isSharedCheck_4758_ == 0 {
                        v___x_4752_ = v___x_4749_;
                        v_isShared_4753_ = v_isSharedCheck_4758_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4750_);
                        lean_dec(v___x_4749_);
                        v___x_4752_ = lean_box(0);
                        v_isShared_4753_ = v_isSharedCheck_4758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4759_ = lean_ctor_get(v___x_4749_, 0);
                    v_isSharedCheck_4766_ = (!lean_is_exclusive(v___x_4749_)) as u8;
                    if v_isSharedCheck_4766_ == 0 {
                        v___x_4761_ = v___x_4749_;
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4759_);
                        lean_dec(v___x_4749_);
                        v___x_4761_ = lean_box(0);
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4754_ = lean_ctor_get(v_a_4750_, 1);
                lean_inc(v_snd_4754_);
                lean_dec(v_a_4750_);
                if v_isShared_4753_ == 0 {
                    lean_ctor_set(v___x_4752_, 0, v_snd_4754_);
                    v___x_4756_ = v___x_4752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_snd_4754_);
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
                    v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
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
    mut v_jobs_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4773_: *mut LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Meta_MetaM_parIter___redArg(
        v_jobs_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
    );
    lean_dec(v_a_4771_);
    lean_dec_ref(v_a_4770_);
    lean_dec(v_a_4769_);
    lean_dec_ref(v_a_4768_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIter(
    mut v_00_u03b1_4774_: *mut LeanObject,
    mut v_jobs_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4782_: *mut LeanObject,
    mut v_jobs_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_a_4785_: *mut LeanObject,
    mut v_a_4786_: *mut LeanObject,
    mut v_a_4787_: *mut LeanObject,
    mut v_a_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4789_: *mut LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Lean_Meta_MetaM_parIter(
        v_00_u03b1_4782_,
        v_jobs_4783_,
        v_a_4784_,
        v_a_4785_,
        v_a_4786_,
        v_a_4787_,
    );
    lean_dec(v_a_4787_);
    lean_dec_ref(v_a_4786_);
    lean_dec(v_a_4785_);
    lean_dec_ref(v_a_4784_);
    return v_res_4789_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
    mut v_jobs_4790_: *mut LeanObject,
    mut v_a_4791_: *mut LeanObject,
    mut v_a_4792_: *mut LeanObject,
    mut v_a_4793_: *mut LeanObject,
    mut v_a_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut v_a_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4820_: u8 = 0;
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = lean_box(0);
                v___x_4797_ =
                    l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(
                        v_jobs_4790_,
                        v___x_4796_,
                        v_a_4791_,
                        v_a_4792_,
                        v_a_4793_,
                        v_a_4794_,
                    );
                if lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4816_ = (!lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4816_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4798_);
                        lean_dec(v___x_4797_);
                        v___x_4800_ = lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4817_ = lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4824_ = (!lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v___x_4819_ = v___x_4797_;
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4817_);
                        lean_dec(v___x_4797_);
                        v___x_4819_ = lean_box(0);
                        v_isShared_4820_ = v_isSharedCheck_4824_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4802_ = l_List_unzipTR___redArg(v_a_4798_);
                v_fst_4803_ = lean_ctor_get(v___x_4802_, 0);
                v_snd_4804_ = lean_ctor_get(v___x_4802_, 1);
                v_isSharedCheck_4815_ = (!lean_is_exclusive(v___x_4802_)) as u8;
                if v_isSharedCheck_4815_ == 0 {
                    v___x_4806_ = v___x_4802_;
                    v_isShared_4807_ = v_isSharedCheck_4815_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4804_);
                    lean_inc(v_fst_4803_);
                    lean_dec(v___x_4802_);
                    v___x_4806_ = lean_box(0);
                    v_isShared_4807_ = v_isSharedCheck_4815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4808_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_4808_, 0, v_fst_4803_);
                if v_isShared_4807_ == 0 {
                    lean_ctor_set(v___x_4806_, 0, v___x_4808_);
                    v___x_4810_ = v___x_4806_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4808_);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_snd_4804_);
                    v___x_4810_ = v_reuseFailAlloc_4814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4801_ == 0 {
                    lean_ctor_set(v___x_4800_, 0, v___x_4810_);
                    v___x_4812_ = v___x_4800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
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
                    v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
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
    mut v_jobs_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4831_: *mut LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(
        v_jobs_4825_,
        v_a_4826_,
        v_a_4827_,
        v_a_4828_,
        v_a_4829_,
    );
    lean_dec(v_a_4829_);
    lean_dec_ref(v_a_4828_);
    lean_dec(v_a_4827_);
    lean_dec_ref(v_a_4826_);
    return v_res_4831_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedyWithCancel(
    mut v_00_u03b1_4832_: *mut LeanObject,
    mut v_jobs_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
    mut v_a_4836_: *mut LeanObject,
    mut v_a_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4840_: *mut LeanObject,
    mut v_jobs_4841_: *mut LeanObject,
    mut v_a_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
    mut v_a_4845_: *mut LeanObject,
    mut v_a_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4847_: *mut LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(
        v_00_u03b1_4840_,
        v_jobs_4841_,
        v_a_4842_,
        v_a_4843_,
        v_a_4844_,
        v_a_4845_,
    );
    lean_dec(v_a_4845_);
    lean_dec_ref(v_a_4844_);
    lean_dec(v_a_4843_);
    lean_dec_ref(v_a_4842_);
    return v_res_4847_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy___redArg(
    mut v_jobs_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
    mut v_a_4850_: *mut LeanObject,
    mut v_a_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v_snd_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v_a_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4854_) == 0 {
                    v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
                    v_isSharedCheck_4863_ = (!lean_is_exclusive(v___x_4854_)) as u8;
                    if v_isSharedCheck_4863_ == 0 {
                        v___x_4857_ = v___x_4854_;
                        v_isShared_4858_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4855_);
                        lean_dec(v___x_4854_);
                        v___x_4857_ = lean_box(0);
                        v_isShared_4858_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4864_ = lean_ctor_get(v___x_4854_, 0);
                    v_isSharedCheck_4871_ = (!lean_is_exclusive(v___x_4854_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4866_ = v___x_4854_;
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4864_);
                        lean_dec(v___x_4854_);
                        v___x_4866_ = lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4859_ = lean_ctor_get(v_a_4855_, 1);
                lean_inc(v_snd_4859_);
                lean_dec(v_a_4855_);
                if v_isShared_4858_ == 0 {
                    lean_ctor_set(v___x_4857_, 0, v_snd_4859_);
                    v___x_4861_ = v___x_4857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_snd_4859_);
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
                    v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
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
    mut v_jobs_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
    mut v_a_4876_: *mut LeanObject,
    mut v_a_4877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4878_: *mut LeanObject = core::ptr::null_mut();
    v_res_4878_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(
        v_jobs_4872_,
        v_a_4873_,
        v_a_4874_,
        v_a_4875_,
        v_a_4876_,
    );
    lean_dec(v_a_4876_);
    lean_dec_ref(v_a_4875_);
    lean_dec(v_a_4874_);
    lean_dec_ref(v_a_4873_);
    return v_res_4878_;
}
pub unsafe fn l_Lean_Meta_MetaM_parIterGreedy(
    mut v_00_u03b1_4879_: *mut LeanObject,
    mut v_jobs_4880_: *mut LeanObject,
    mut v_a_4881_: *mut LeanObject,
    mut v_a_4882_: *mut LeanObject,
    mut v_a_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4887_: *mut LeanObject,
    mut v_jobs_4888_: *mut LeanObject,
    mut v_a_4889_: *mut LeanObject,
    mut v_a_4890_: *mut LeanObject,
    mut v_a_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4894_: *mut LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Lean_Meta_MetaM_parIterGreedy(
        v_00_u03b1_4887_,
        v_jobs_4888_,
        v_a_4889_,
        v_a_4890_,
        v_a_4891_,
        v_a_4892_,
    );
    lean_dec(v_a_4892_);
    lean_dec_ref(v_a_4891_);
    lean_dec(v_a_4890_);
    lean_dec_ref(v_a_4889_);
    return v_res_4894_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(
    mut v_a_4895_: *mut LeanObject,
    mut v___x_4896_: *mut LeanObject,
    mut v_____r_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4903_, 0, v_a_4895_);
    v___x_4904_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    lean_ctor_set(v___x_4904_, 1, v___x_4896_);
    v___x_4905_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4905_, 0, v___x_4904_);
    v___x_4906_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4906_, 0, v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_4907_: *mut LeanObject,
    mut v___x_4908_: *mut LeanObject,
    mut v_____r_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4915_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4913_);
    lean_dec_ref(v___y_4912_);
    lean_dec(v___y_4911_);
    lean_dec_ref(v___y_4910_);
    return v_res_4915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(
    mut v_cancel_4916_: u8,
    mut v_fst_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_b_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
    mut v___y_4921_: *mut LeanObject,
    mut v___y_4922_: *mut LeanObject,
    mut v___y_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v_a_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4941_: u8 = 0;
    let mut v_a_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4960_: u8 = 0;
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4963_: u8 = 0;
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: u8 = 0;
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4918_) == 0 {
                    lean_dec_ref(v_fst_4917_);
                    v___x_4925_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4925_, 0, v_b_4919_);
                    return v___x_4925_;
                } else {
                    lean_dec_ref(v_b_4919_);
                    v___x_4926_ = l_IO_waitAny_x27___redArg(v_a_4918_);
                    v_fst_4927_ = lean_ctor_get(v___x_4926_, 0);
                    lean_inc(v_fst_4927_);
                    v_snd_4928_ = lean_ctor_get(v___x_4926_, 1);
                    lean_inc(v_snd_4928_);
                    lean_dec_ref(v___x_4926_);
                    v___x_4950_ = lean_box(0);
                    lean_inc(v___y_4923_);
                    lean_inc_ref(v___y_4922_);
                    lean_inc(v___y_4921_);
                    lean_inc_ref(v___y_4920_);
                    v___x_4951_ = lean_apply_5(
                        v_fst_4927_,
                        v___y_4920_,
                        v___y_4921_,
                        v___y_4922_,
                        v___y_4923_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4951_) == 0 {
                        if v_cancel_4916_ == 0 {
                            v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
                            lean_inc(v_a_4952_);
                            lean_dec_ref_known(v___x_4951_, 1);
                            v___x_4953_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_4952_, v___x_4950_, v___x_4950_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
                            v___y_4930_ = v___x_4953_;
                            state = 1;
                            continue;
                        } else {
                            v_a_4954_ = lean_ctor_get(v___x_4951_, 0);
                            lean_inc(v_a_4954_);
                            lean_dec_ref_known(v___x_4951_, 1);
                            lean_inc_ref(v_fst_4917_);
                            v___x_4955_ = lean_apply_1(v_fst_4917_, lean_box(0));
                            v___x_4956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_4954_, v___x_4950_, v___x_4955_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
                            v___y_4930_ = v___x_4956_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4957_ = lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4970_ = (!lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4970_ == 0 {
                            v___x_4959_ = v___x_4951_;
                            v_isShared_4960_ = v_isSharedCheck_4970_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4957_);
                            lean_dec(v___x_4951_);
                            v___x_4959_ = lean_box(0);
                            v_isShared_4960_ = v_isSharedCheck_4970_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4930_) == 0 {
                    v_a_4931_ = lean_ctor_get(v___y_4930_, 0);
                    v_isSharedCheck_4941_ = (!lean_is_exclusive(v___y_4930_)) as u8;
                    if v_isSharedCheck_4941_ == 0 {
                        v___x_4933_ = v___y_4930_;
                        v_isShared_4934_ = v_isSharedCheck_4941_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4931_);
                        lean_dec(v___y_4930_);
                        v___x_4933_ = lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4941_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4928_);
                    lean_dec_ref(v_fst_4917_);
                    v_a_4942_ = lean_ctor_get(v___y_4930_, 0);
                    v_isSharedCheck_4949_ = (!lean_is_exclusive(v___y_4930_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4944_ = v___y_4930_;
                        v_isShared_4945_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4942_);
                        lean_dec(v___y_4930_);
                        v___x_4944_ = lean_box(0);
                        v_isShared_4945_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4931_) == 0 {
                    lean_dec(v_snd_4928_);
                    lean_dec_ref(v_fst_4917_);
                    v_a_4935_ = lean_ctor_get(v_a_4931_, 0);
                    lean_inc(v_a_4935_);
                    lean_dec_ref_known(v_a_4931_, 1);
                    if v_isShared_4934_ == 0 {
                        lean_ctor_set(v___x_4933_, 0, v_a_4935_);
                        v___x_4937_ = v___x_4933_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4935_);
                        v___x_4937_ = v_reuseFailAlloc_4938_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4933_);
                    v_a_4939_ = lean_ctor_get(v_a_4931_, 0);
                    lean_inc(v_a_4939_);
                    lean_dec_ref_known(v_a_4931_, 1);
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
                    v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
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
                    lean_inc(v_a_4957_);
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
                    lean_del_object(v___x_4959_);
                    lean_dec(v_a_4957_);
                    v_a_4918_ = v_snd_4928_;
                    v_b_4919_ = v___x_4961_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_snd_4928_);
                    lean_dec_ref(v_fst_4917_);
                    if v_isShared_4960_ == 0 {
                        v___x_4966_ = v___x_4959_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4957_);
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
    mut v_cancel_4971_: *mut LeanObject,
    mut v_fst_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
    mut v_b_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_4980_: u8 = 0;
    let mut v_res_4981_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_4980_ = (lean_unbox(v_cancel_4971_) as u8);
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
    lean_dec(v___y_4978_);
    lean_dec_ref(v___y_4977_);
    lean_dec(v___y_4976_);
    lean_dec_ref(v___y_4975_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(
    mut v_msgData_4982_: *mut LeanObject,
    mut v___y_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
    mut v___y_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    v___x_4988_ = lean_st_ref_get(v___y_4986_);
    v_env_4989_ = lean_ctor_get(v___x_4988_, 0);
    lean_inc_ref(v_env_4989_);
    lean_dec(v___x_4988_);
    v___x_4990_ = lean_st_ref_get(v___y_4984_);
    v_mctx_4991_ = lean_ctor_get(v___x_4990_, 0);
    lean_inc_ref(v_mctx_4991_);
    lean_dec(v___x_4990_);
    v_lctx_4992_ = lean_ctor_get(v___y_4983_, 2);
    v_options_4993_ = lean_ctor_get(v___y_4985_, 2);
    lean_inc_ref(v_options_4993_);
    lean_inc_ref(v_lctx_4992_);
    v___x_4994_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4994_, 0, v_env_4989_);
    lean_ctor_set(v___x_4994_, 1, v_mctx_4991_);
    lean_ctor_set(v___x_4994_, 2, v_lctx_4992_);
    lean_ctor_set(v___x_4994_, 3, v_options_4993_);
    v___x_4995_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4995_, 0, v___x_4994_);
    lean_ctor_set(v___x_4995_, 1, v_msgData_4982_);
    v___x_4996_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4996_, 0, v___x_4995_);
    return v___x_4996_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_4997_: *mut LeanObject,
    mut v___y_4998_: *mut LeanObject,
    mut v___y_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5003_: *mut LeanObject = core::ptr::null_mut();
    v_res_5003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
    lean_dec(v___y_5001_);
    lean_dec_ref(v___y_5000_);
    lean_dec(v___y_4999_);
    lean_dec_ref(v___y_4998_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
    mut v_msg_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5010_ = lean_ctor_get(v___y_5007_, 5);
                v___x_5011_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
                v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
                v_isSharedCheck_5020_ = (!lean_is_exclusive(v___x_5011_)) as u8;
                if v_isSharedCheck_5020_ == 0 {
                    v___x_5014_ = v___x_5011_;
                    v_isShared_5015_ = v_isSharedCheck_5020_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5012_);
                    lean_dec(v___x_5011_);
                    v___x_5014_ = lean_box(0);
                    v_isShared_5015_ = v_isSharedCheck_5020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5010_);
                v___x_5016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5016_, 0, v_ref_5010_);
                lean_ctor_set(v___x_5016_, 1, v_a_5012_);
                if v_isShared_5015_ == 0 {
                    lean_ctor_set_tag(v___x_5014_, 1);
                    lean_ctor_set(v___x_5014_, 0, v___x_5016_);
                    v___x_5018_ = v___x_5014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5016_);
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
    mut v_msg_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5027_: *mut LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(
        v_msg_5021_,
        v___y_5022_,
        v___y_5023_,
        v___y_5024_,
        v___y_5025_,
    );
    lean_dec(v___y_5025_);
    lean_dec_ref(v___y_5024_);
    lean_dec(v___y_5023_);
    lean_dec_ref(v___y_5022_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst___redArg(
    mut v_jobs_5028_: *mut LeanObject,
    mut v_cancel_5029_: u8,
    mut v_a_5030_: *mut LeanObject,
    mut v_a_5031_: *mut LeanObject,
    mut v_a_5032_: *mut LeanObject,
    mut v_a_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v_fst_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut v_a_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5067_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5035_) == 0 {
                    v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
                    lean_inc(v_a_5036_);
                    lean_dec_ref_known(v___x_5035_, 1);
                    v_fst_5037_ = lean_ctor_get(v_a_5036_, 0);
                    lean_inc(v_fst_5037_);
                    v_snd_5038_ = lean_ctor_get(v_a_5036_, 1);
                    lean_inc(v_snd_5038_);
                    lean_dec(v_a_5036_);
                    v___x_5039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_5040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_5029_, v_fst_5037_, v_snd_5038_, v___x_5039_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
                    if lean_obj_tag(v___x_5040_) == 0 {
                        v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5052_ = (!lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5052_ == 0 {
                            v___x_5043_ = v___x_5040_;
                            v_isShared_5044_ = v_isSharedCheck_5052_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5041_);
                            lean_dec(v___x_5040_);
                            v___x_5043_ = lean_box(0);
                            v_isShared_5044_ = v_isSharedCheck_5052_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5053_ = lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5060_ = (!lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5060_ == 0 {
                            v___x_5055_ = v___x_5040_;
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5053_);
                            lean_dec(v___x_5040_);
                            v___x_5055_ = lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5061_ = lean_ctor_get(v___x_5035_, 0);
                    v_isSharedCheck_5068_ = (!lean_is_exclusive(v___x_5035_)) as u8;
                    if v_isSharedCheck_5068_ == 0 {
                        v___x_5063_ = v___x_5035_;
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5061_);
                        lean_dec(v___x_5035_);
                        v___x_5063_ = lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5045_ = lean_ctor_get(v_a_5041_, 0);
                lean_inc(v_fst_5045_);
                lean_dec(v_a_5041_);
                if lean_obj_tag(v_fst_5045_) == 0 {
                    lean_del_object(v___x_5043_);
                    v___x_5046_ = lean_obj_once(
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
                    v_val_5048_ = lean_ctor_get(v_fst_5045_, 0);
                    lean_inc(v_val_5048_);
                    lean_dec_ref_known(v_fst_5045_, 1);
                    if v_isShared_5044_ == 0 {
                        lean_ctor_set(v___x_5043_, 0, v_val_5048_);
                        v___x_5050_ = v___x_5043_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_val_5048_);
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
                    v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
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
                    v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
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
    mut v_jobs_5069_: *mut LeanObject,
    mut v_cancel_5070_: *mut LeanObject,
    mut v_a_5071_: *mut LeanObject,
    mut v_a_5072_: *mut LeanObject,
    mut v_a_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_5076_: u8 = 0;
    let mut v_res_5077_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5076_ = (lean_unbox(v_cancel_5070_) as u8);
    v_res_5077_ = l_Lean_Meta_MetaM_parFirst___redArg(
        v_jobs_5069_,
        v_cancel_boxed_5076_,
        v_a_5071_,
        v_a_5072_,
        v_a_5073_,
        v_a_5074_,
    );
    lean_dec(v_a_5074_);
    lean_dec_ref(v_a_5073_);
    lean_dec(v_a_5072_);
    lean_dec_ref(v_a_5071_);
    return v_res_5077_;
}
pub unsafe fn l_Lean_Meta_MetaM_parFirst(
    mut v_00_u03b1_5078_: *mut LeanObject,
    mut v_jobs_5079_: *mut LeanObject,
    mut v_cancel_5080_: u8,
    mut v_a_5081_: *mut LeanObject,
    mut v_a_5082_: *mut LeanObject,
    mut v_a_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5087_: *mut LeanObject,
    mut v_jobs_5088_: *mut LeanObject,
    mut v_cancel_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
    mut v_a_5091_: *mut LeanObject,
    mut v_a_5092_: *mut LeanObject,
    mut v_a_5093_: *mut LeanObject,
    mut v_a_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_5095_: u8 = 0;
    let mut v_res_5096_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5095_ = (lean_unbox(v_cancel_5089_) as u8);
    v_res_5096_ = l_Lean_Meta_MetaM_parFirst(
        v_00_u03b1_5087_,
        v_jobs_5088_,
        v_cancel_boxed_5095_,
        v_a_5090_,
        v_a_5091_,
        v_a_5092_,
        v_a_5093_,
    );
    lean_dec(v_a_5093_);
    lean_dec_ref(v_a_5092_);
    lean_dec(v_a_5091_);
    lean_dec_ref(v_a_5090_);
    return v_res_5096_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(
    mut v_00_u03b1_5097_: *mut LeanObject,
    mut v_cancel_5098_: u8,
    mut v_fst_5099_: *mut LeanObject,
    mut v_inst_5100_: *mut LeanObject,
    mut v_R_5101_: *mut LeanObject,
    mut v_a_5102_: *mut LeanObject,
    mut v_b_5103_: *mut LeanObject,
    mut v_c_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5111_: *mut LeanObject,
    mut v_cancel_5112_: *mut LeanObject,
    mut v_fst_5113_: *mut LeanObject,
    mut v_inst_5114_: *mut LeanObject,
    mut v_R_5115_: *mut LeanObject,
    mut v_a_5116_: *mut LeanObject,
    mut v_b_5117_: *mut LeanObject,
    mut v_c_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
    mut v___y_5120_: *mut LeanObject,
    mut v___y_5121_: *mut LeanObject,
    mut v___y_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_5124_: u8 = 0;
    let mut v_res_5125_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5124_ = (lean_unbox(v_cancel_5112_) as u8);
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
    lean_dec(v___y_5122_);
    lean_dec_ref(v___y_5121_);
    lean_dec(v___y_5120_);
    lean_dec_ref(v___y_5119_);
    return v_res_5125_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(
    mut v_00_u03b1_5126_: *mut LeanObject,
    mut v_msg_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
    mut v___y_5129_: *mut LeanObject,
    mut v___y_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5134_: *mut LeanObject,
    mut v_msg_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5141_: *mut LeanObject = core::ptr::null_mut();
    v_res_5141_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(
        v_00_u03b1_5134_,
        v_msg_5135_,
        v___y_5136_,
        v___y_5137_,
        v___y_5138_,
        v___y_5139_,
    );
    lean_dec(v___y_5139_);
    lean_dec_ref(v___y_5138_);
    lean_dec(v___y_5137_);
    lean_dec_ref(v___y_5136_);
    return v_res_5141_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(
    mut v_x_5142_: *mut LeanObject,
    mut v_x_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
    mut v___y_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5157_: u8 = 0;
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5142_) == 0 {
                    v___x_5151_ = l_List_reverse___redArg(v_x_5143_);
                    v___x_5152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5152_, 0, v___x_5151_);
                    return v___x_5152_;
                } else {
                    v_head_5153_ = lean_ctor_get(v_x_5142_, 0);
                    v_tail_5154_ = lean_ctor_get(v_x_5142_, 1);
                    v_isSharedCheck_5172_ = (!lean_is_exclusive(v_x_5142_)) as u8;
                    if v_isSharedCheck_5172_ == 0 {
                        v___x_5156_ = v_x_5142_;
                        v_isShared_5157_ = v_isSharedCheck_5172_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5154_);
                        lean_inc(v_head_5153_);
                        lean_dec(v_x_5142_);
                        v___x_5156_ = lean_box(0);
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
                if lean_obj_tag(v___x_5158_) == 0 {
                    v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
                    lean_inc(v_a_5159_);
                    lean_dec_ref_known(v___x_5158_, 1);
                    if v_isShared_5157_ == 0 {
                        lean_ctor_set(v___x_5156_, 1, v_x_5143_);
                        lean_ctor_set(v___x_5156_, 0, v_a_5159_);
                        v___x_5161_ = v___x_5156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5159_);
                        lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_x_5143_);
                        v___x_5161_ = v_reuseFailAlloc_5163_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5156_);
                    lean_dec(v_tail_5154_);
                    lean_dec(v_x_5143_);
                    v_a_5164_ = lean_ctor_get(v___x_5158_, 0);
                    v_isSharedCheck_5171_ = (!lean_is_exclusive(v___x_5158_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5166_ = v___x_5158_;
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5164_);
                        lean_dec(v___x_5158_);
                        v___x_5166_ = lean_box(0);
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
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
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
    mut v_x_5173_: *mut LeanObject,
    mut v_x_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
    mut v___y_5177_: *mut LeanObject,
    mut v___y_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5182_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5180_);
    lean_dec_ref(v___y_5179_);
    lean_dec(v___y_5178_);
    lean_dec_ref(v___y_5177_);
    lean_dec(v___y_5176_);
    lean_dec_ref(v___y_5175_);
    return v_res_5182_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
    mut v_jobs_5183_: *mut LeanObject,
    mut v_a_5184_: *mut LeanObject,
    mut v_a_5185_: *mut LeanObject,
    mut v_a_5186_: *mut LeanObject,
    mut v_a_5187_: *mut LeanObject,
    mut v_a_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5196_: u8 = 0;
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5202_: u8 = 0;
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5210_: u8 = 0;
    let mut v_isSharedCheck_5211_: u8 = 0;
    let mut v_a_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5191_ = lean_box(0);
                v___x_5192_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_5183_, v___x_5191_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                if lean_obj_tag(v___x_5192_) == 0 {
                    v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
                    v_isSharedCheck_5211_ = (!lean_is_exclusive(v___x_5192_)) as u8;
                    if v_isSharedCheck_5211_ == 0 {
                        v___x_5195_ = v___x_5192_;
                        v_isShared_5196_ = v_isSharedCheck_5211_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5193_);
                        lean_dec(v___x_5192_);
                        v___x_5195_ = lean_box(0);
                        v_isShared_5196_ = v_isSharedCheck_5211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5212_ = lean_ctor_get(v___x_5192_, 0);
                    v_isSharedCheck_5219_ = (!lean_is_exclusive(v___x_5192_)) as u8;
                    if v_isSharedCheck_5219_ == 0 {
                        v___x_5214_ = v___x_5192_;
                        v_isShared_5215_ = v_isSharedCheck_5219_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5212_);
                        lean_dec(v___x_5192_);
                        v___x_5214_ = lean_box(0);
                        v_isShared_5215_ = v_isSharedCheck_5219_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5197_ = l_List_unzipTR___redArg(v_a_5193_);
                v_fst_5198_ = lean_ctor_get(v___x_5197_, 0);
                v_snd_5199_ = lean_ctor_get(v___x_5197_, 1);
                v_isSharedCheck_5210_ = (!lean_is_exclusive(v___x_5197_)) as u8;
                if v_isSharedCheck_5210_ == 0 {
                    v___x_5201_ = v___x_5197_;
                    v_isShared_5202_ = v_isSharedCheck_5210_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5199_);
                    lean_inc(v_fst_5198_);
                    lean_dec(v___x_5197_);
                    v___x_5201_ = lean_box(0);
                    v_isShared_5202_ = v_isSharedCheck_5210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5203_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_5203_, 0, v_fst_5198_);
                if v_isShared_5202_ == 0 {
                    lean_ctor_set(v___x_5201_, 0, v___x_5203_);
                    v___x_5205_ = v___x_5201_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5203_);
                    lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_snd_5199_);
                    v___x_5205_ = v_reuseFailAlloc_5209_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5196_ == 0 {
                    lean_ctor_set(v___x_5195_, 0, v___x_5205_);
                    v___x_5207_ = v___x_5195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5205_);
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
                    v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
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
    mut v_jobs_5220_: *mut LeanObject,
    mut v_a_5221_: *mut LeanObject,
    mut v_a_5222_: *mut LeanObject,
    mut v_a_5223_: *mut LeanObject,
    mut v_a_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5228_: *mut LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(
        v_jobs_5220_,
        v_a_5221_,
        v_a_5222_,
        v_a_5223_,
        v_a_5224_,
        v_a_5225_,
        v_a_5226_,
    );
    lean_dec(v_a_5226_);
    lean_dec_ref(v_a_5225_);
    lean_dec(v_a_5224_);
    lean_dec_ref(v_a_5223_);
    lean_dec(v_a_5222_);
    lean_dec_ref(v_a_5221_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterWithCancel(
    mut v_00_u03b1_5229_: *mut LeanObject,
    mut v_jobs_5230_: *mut LeanObject,
    mut v_a_5231_: *mut LeanObject,
    mut v_a_5232_: *mut LeanObject,
    mut v_a_5233_: *mut LeanObject,
    mut v_a_5234_: *mut LeanObject,
    mut v_a_5235_: *mut LeanObject,
    mut v_a_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5239_: *mut LeanObject,
    mut v_jobs_5240_: *mut LeanObject,
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
    mut v_a_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5248_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5246_);
    lean_dec_ref(v_a_5245_);
    lean_dec(v_a_5244_);
    lean_dec_ref(v_a_5243_);
    lean_dec(v_a_5242_);
    lean_dec_ref(v_a_5241_);
    return v_res_5248_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(
    mut v_00_u03b1_5249_: *mut LeanObject,
    mut v_x_5250_: *mut LeanObject,
    mut v_x_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5260_: *mut LeanObject,
    mut v_x_5261_: *mut LeanObject,
    mut v_x_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5270_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5268_);
    lean_dec_ref(v___y_5267_);
    lean_dec(v___y_5266_);
    lean_dec_ref(v___y_5265_);
    lean_dec(v___y_5264_);
    lean_dec_ref(v___y_5263_);
    return v_res_5270_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter___redArg(
    mut v_jobs_5271_: *mut LeanObject,
    mut v_a_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
    mut v_a_5277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v_snd_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5279_) == 0 {
                    v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
                    v_isSharedCheck_5288_ = (!lean_is_exclusive(v___x_5279_)) as u8;
                    if v_isSharedCheck_5288_ == 0 {
                        v___x_5282_ = v___x_5279_;
                        v_isShared_5283_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5280_);
                        lean_dec(v___x_5279_);
                        v___x_5282_ = lean_box(0);
                        v_isShared_5283_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5289_ = lean_ctor_get(v___x_5279_, 0);
                    v_isSharedCheck_5296_ = (!lean_is_exclusive(v___x_5279_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5291_ = v___x_5279_;
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5289_);
                        lean_dec(v___x_5279_);
                        v___x_5291_ = lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5284_ = lean_ctor_get(v_a_5280_, 1);
                lean_inc(v_snd_5284_);
                lean_dec(v_a_5280_);
                if v_isShared_5283_ == 0 {
                    lean_ctor_set(v___x_5282_, 0, v_snd_5284_);
                    v___x_5286_ = v___x_5282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_snd_5284_);
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
                    v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
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
    mut v_jobs_5297_: *mut LeanObject,
    mut v_a_5298_: *mut LeanObject,
    mut v_a_5299_: *mut LeanObject,
    mut v_a_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_a_5303_: *mut LeanObject,
    mut v_a_5304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5305_: *mut LeanObject = core::ptr::null_mut();
    v_res_5305_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(
        v_jobs_5297_,
        v_a_5298_,
        v_a_5299_,
        v_a_5300_,
        v_a_5301_,
        v_a_5302_,
        v_a_5303_,
    );
    lean_dec(v_a_5303_);
    lean_dec_ref(v_a_5302_);
    lean_dec(v_a_5301_);
    lean_dec_ref(v_a_5300_);
    lean_dec(v_a_5299_);
    lean_dec_ref(v_a_5298_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIter(
    mut v_00_u03b1_5306_: *mut LeanObject,
    mut v_jobs_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
    mut v_a_5309_: *mut LeanObject,
    mut v_a_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
    mut v_a_5312_: *mut LeanObject,
    mut v_a_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5316_: *mut LeanObject,
    mut v_jobs_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
    mut v_a_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
    mut v_a_5323_: *mut LeanObject,
    mut v_a_5324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5325_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5323_);
    lean_dec_ref(v_a_5322_);
    lean_dec(v_a_5321_);
    lean_dec_ref(v_a_5320_);
    lean_dec(v_a_5319_);
    lean_dec_ref(v_a_5318_);
    return v_res_5325_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
    mut v_jobs_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
    mut v_a_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5353_: u8 = 0;
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_a_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5334_ = lean_box(0);
                v___x_5335_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_5326_, v___x_5334_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
                if lean_obj_tag(v___x_5335_) == 0 {
                    v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
                    v_isSharedCheck_5354_ = (!lean_is_exclusive(v___x_5335_)) as u8;
                    if v_isSharedCheck_5354_ == 0 {
                        v___x_5338_ = v___x_5335_;
                        v_isShared_5339_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5336_);
                        lean_dec(v___x_5335_);
                        v___x_5338_ = lean_box(0);
                        v_isShared_5339_ = v_isSharedCheck_5354_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5355_ = lean_ctor_get(v___x_5335_, 0);
                    v_isSharedCheck_5362_ = (!lean_is_exclusive(v___x_5335_)) as u8;
                    if v_isSharedCheck_5362_ == 0 {
                        v___x_5357_ = v___x_5335_;
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5355_);
                        lean_dec(v___x_5335_);
                        v___x_5357_ = lean_box(0);
                        v_isShared_5358_ = v_isSharedCheck_5362_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5340_ = l_List_unzipTR___redArg(v_a_5336_);
                v_fst_5341_ = lean_ctor_get(v___x_5340_, 0);
                v_snd_5342_ = lean_ctor_get(v___x_5340_, 1);
                v_isSharedCheck_5353_ = (!lean_is_exclusive(v___x_5340_)) as u8;
                if v_isSharedCheck_5353_ == 0 {
                    v___x_5344_ = v___x_5340_;
                    v_isShared_5345_ = v_isSharedCheck_5353_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_5342_);
                    lean_inc(v_fst_5341_);
                    lean_dec(v___x_5340_);
                    v___x_5344_ = lean_box(0);
                    v_isShared_5345_ = v_isSharedCheck_5353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5346_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_5346_, 0, v_fst_5341_);
                if v_isShared_5345_ == 0 {
                    lean_ctor_set(v___x_5344_, 0, v___x_5346_);
                    v___x_5348_ = v___x_5344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5346_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_snd_5342_);
                    v___x_5348_ = v_reuseFailAlloc_5352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5339_ == 0 {
                    lean_ctor_set(v___x_5338_, 0, v___x_5348_);
                    v___x_5350_ = v___x_5338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
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
                    v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
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
    mut v_jobs_5363_: *mut LeanObject,
    mut v_a_5364_: *mut LeanObject,
    mut v_a_5365_: *mut LeanObject,
    mut v_a_5366_: *mut LeanObject,
    mut v_a_5367_: *mut LeanObject,
    mut v_a_5368_: *mut LeanObject,
    mut v_a_5369_: *mut LeanObject,
    mut v_a_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(
        v_jobs_5363_,
        v_a_5364_,
        v_a_5365_,
        v_a_5366_,
        v_a_5367_,
        v_a_5368_,
        v_a_5369_,
    );
    lean_dec(v_a_5369_);
    lean_dec_ref(v_a_5368_);
    lean_dec(v_a_5367_);
    lean_dec_ref(v_a_5366_);
    lean_dec(v_a_5365_);
    lean_dec_ref(v_a_5364_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(
    mut v_00_u03b1_5372_: *mut LeanObject,
    mut v_jobs_5373_: *mut LeanObject,
    mut v_a_5374_: *mut LeanObject,
    mut v_a_5375_: *mut LeanObject,
    mut v_a_5376_: *mut LeanObject,
    mut v_a_5377_: *mut LeanObject,
    mut v_a_5378_: *mut LeanObject,
    mut v_a_5379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5382_: *mut LeanObject,
    mut v_jobs_5383_: *mut LeanObject,
    mut v_a_5384_: *mut LeanObject,
    mut v_a_5385_: *mut LeanObject,
    mut v_a_5386_: *mut LeanObject,
    mut v_a_5387_: *mut LeanObject,
    mut v_a_5388_: *mut LeanObject,
    mut v_a_5389_: *mut LeanObject,
    mut v_a_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5391_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5389_);
    lean_dec_ref(v_a_5388_);
    lean_dec(v_a_5387_);
    lean_dec_ref(v_a_5386_);
    lean_dec(v_a_5385_);
    lean_dec_ref(v_a_5384_);
    return v_res_5391_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(
    mut v_jobs_5392_: *mut LeanObject,
    mut v_a_5393_: *mut LeanObject,
    mut v_a_5394_: *mut LeanObject,
    mut v_a_5395_: *mut LeanObject,
    mut v_a_5396_: *mut LeanObject,
    mut v_a_5397_: *mut LeanObject,
    mut v_a_5398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_snd_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v_a_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5400_) == 0 {
                    v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5409_ = (!lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v___x_5403_ = v___x_5400_;
                        v_isShared_5404_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5401_);
                        lean_dec(v___x_5400_);
                        v___x_5403_ = lean_box(0);
                        v_isShared_5404_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5410_ = lean_ctor_get(v___x_5400_, 0);
                    v_isSharedCheck_5417_ = (!lean_is_exclusive(v___x_5400_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5412_ = v___x_5400_;
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5410_);
                        lean_dec(v___x_5400_);
                        v___x_5412_ = lean_box(0);
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5405_ = lean_ctor_get(v_a_5401_, 1);
                lean_inc(v_snd_5405_);
                lean_dec(v_a_5401_);
                if v_isShared_5404_ == 0 {
                    lean_ctor_set(v___x_5403_, 0, v_snd_5405_);
                    v___x_5407_ = v___x_5403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_snd_5405_);
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
                    v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
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
    mut v_jobs_5418_: *mut LeanObject,
    mut v_a_5419_: *mut LeanObject,
    mut v_a_5420_: *mut LeanObject,
    mut v_a_5421_: *mut LeanObject,
    mut v_a_5422_: *mut LeanObject,
    mut v_a_5423_: *mut LeanObject,
    mut v_a_5424_: *mut LeanObject,
    mut v_a_5425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5426_: *mut LeanObject = core::ptr::null_mut();
    v_res_5426_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(
        v_jobs_5418_,
        v_a_5419_,
        v_a_5420_,
        v_a_5421_,
        v_a_5422_,
        v_a_5423_,
        v_a_5424_,
    );
    lean_dec(v_a_5424_);
    lean_dec_ref(v_a_5423_);
    lean_dec(v_a_5422_);
    lean_dec_ref(v_a_5421_);
    lean_dec(v_a_5420_);
    lean_dec_ref(v_a_5419_);
    return v_res_5426_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parIterGreedy(
    mut v_00_u03b1_5427_: *mut LeanObject,
    mut v_jobs_5428_: *mut LeanObject,
    mut v_a_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
    mut v_a_5431_: *mut LeanObject,
    mut v_a_5432_: *mut LeanObject,
    mut v_a_5433_: *mut LeanObject,
    mut v_a_5434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5437_: *mut LeanObject,
    mut v_jobs_5438_: *mut LeanObject,
    mut v_a_5439_: *mut LeanObject,
    mut v_a_5440_: *mut LeanObject,
    mut v_a_5441_: *mut LeanObject,
    mut v_a_5442_: *mut LeanObject,
    mut v_a_5443_: *mut LeanObject,
    mut v_a_5444_: *mut LeanObject,
    mut v_a_5445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5446_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5444_);
    lean_dec_ref(v_a_5443_);
    lean_dec(v_a_5442_);
    lean_dec_ref(v_a_5441_);
    lean_dec(v_a_5440_);
    lean_dec_ref(v_a_5439_);
    return v_res_5446_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(
    mut v_x_5447_: *mut LeanObject,
    mut v_x_5448_: *mut LeanObject,
    mut v___y_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
    mut v___y_5451_: *mut LeanObject,
    mut v___y_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5462_: u8 = 0;
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5447_) == 0 {
                    v___x_5456_ = l_List_reverse___redArg(v_x_5448_);
                    v___x_5457_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5457_, 0, v___x_5456_);
                    return v___x_5457_;
                } else {
                    v_head_5458_ = lean_ctor_get(v_x_5447_, 0);
                    v_tail_5459_ = lean_ctor_get(v_x_5447_, 1);
                    v_isSharedCheck_5477_ = (!lean_is_exclusive(v_x_5447_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5461_ = v_x_5447_;
                        v_isShared_5462_ = v_isSharedCheck_5477_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5459_);
                        lean_inc(v_head_5458_);
                        lean_dec(v_x_5447_);
                        v___x_5461_ = lean_box(0);
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
                if lean_obj_tag(v___x_5463_) == 0 {
                    v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
                    lean_inc(v_a_5464_);
                    lean_dec_ref_known(v___x_5463_, 1);
                    if v_isShared_5462_ == 0 {
                        lean_ctor_set(v___x_5461_, 1, v_x_5448_);
                        lean_ctor_set(v___x_5461_, 0, v_a_5464_);
                        v___x_5466_ = v___x_5461_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5464_);
                        lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_x_5448_);
                        v___x_5466_ = v_reuseFailAlloc_5468_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5461_);
                    lean_dec(v_tail_5459_);
                    lean_dec(v_x_5448_);
                    v_a_5469_ = lean_ctor_get(v___x_5463_, 0);
                    v_isSharedCheck_5476_ = (!lean_is_exclusive(v___x_5463_)) as u8;
                    if v_isSharedCheck_5476_ == 0 {
                        v___x_5471_ = v___x_5463_;
                        v_isShared_5472_ = v_isSharedCheck_5476_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5469_);
                        lean_dec(v___x_5463_);
                        v___x_5471_ = lean_box(0);
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
                    v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
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
    mut v_x_5478_: *mut LeanObject,
    mut v_x_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5487_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5485_);
    lean_dec_ref(v___y_5484_);
    lean_dec(v___y_5483_);
    lean_dec_ref(v___y_5482_);
    lean_dec(v___y_5481_);
    lean_dec_ref(v___y_5480_);
    return v_res_5487_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(
    mut v_as_x27_5488_: *mut LeanObject,
    mut v_b_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5502_: u8 = 0;
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: u8 = 0;
    let mut v___x_2960__overap_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut v_a_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5488_) == 0 {
                    v___x_5497_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5497_, 0, v_b_5489_);
                    return v___x_5497_;
                } else {
                    v_head_5498_ = lean_ctor_get(v_as_x27_5488_, 0);
                    v_tail_5499_ = lean_ctor_get(v_as_x27_5488_, 1);
                    lean_inc(v_head_5498_);
                    v___x_2960__overap_5511_ = lean_task_get_own(v_head_5498_);
                    lean_inc(v___y_5495_);
                    lean_inc_ref(v___y_5494_);
                    lean_inc(v___y_5493_);
                    lean_inc_ref(v___y_5492_);
                    lean_inc(v___y_5491_);
                    lean_inc_ref(v___y_5490_);
                    v___x_5512_ = lean_apply_7(
                        v___x_2960__overap_5511_,
                        v___y_5490_,
                        v___y_5491_,
                        v___y_5492_,
                        v___y_5493_,
                        v___y_5494_,
                        v___y_5495_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5512_) == 0 {
                        v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
                        lean_inc(v_a_5513_);
                        lean_dec_ref_known(v___x_5512_, 1);
                        v___x_5514_ = l_Lean_Elab_Term_saveState___redArg(
                            v___y_5491_,
                            v___y_5493_,
                            v___y_5495_,
                        );
                        if lean_obj_tag(v___x_5514_) == 0 {
                            v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
                            v_isSharedCheck_5525_ = (!lean_is_exclusive(v___x_5514_)) as u8;
                            if v_isSharedCheck_5525_ == 0 {
                                v___x_5517_ = v___x_5514_;
                                v_isShared_5518_ = v_isSharedCheck_5525_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5515_);
                                lean_dec(v___x_5514_);
                                v___x_5517_ = lean_box(0);
                                v_isShared_5518_ = v_isSharedCheck_5525_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5513_);
                            v_a_5526_ = lean_ctor_get(v___x_5514_, 0);
                            lean_inc(v_a_5526_);
                            lean_dec_ref_known(v___x_5514_, 1);
                            v_a_5508_ = v_a_5526_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5527_ = lean_ctor_get(v___x_5512_, 0);
                        lean_inc(v_a_5527_);
                        lean_dec_ref_known(v___x_5512_, 1);
                        v_a_5508_ = v_a_5527_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5502_ == 0 {
                    v___x_5503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5503_, 0, v___y_5501_);
                    v___x_5504_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5504_, 0, v___x_5503_);
                    lean_ctor_set(v___x_5504_, 1, v_b_5489_);
                    v_as_x27_5488_ = v_tail_5499_;
                    v_b_5489_ = v___x_5504_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_b_5489_);
                    v___x_5506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5506_, 0, v___y_5501_);
                    return v___x_5506_;
                }
            }
            2 => {
                v___x_5509_ = l_Lean_Exception_isInterrupt(v_a_5508_);
                if v___x_5509_ == 0 {
                    lean_inc_ref(v_a_5508_);
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
                v___x_5519_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5519_, 0, v_a_5513_);
                lean_ctor_set(v___x_5519_, 1, v_a_5515_);
                if v_isShared_5518_ == 0 {
                    lean_ctor_set_tag(v___x_5517_, 1);
                    lean_ctor_set(v___x_5517_, 0, v___x_5519_);
                    v___x_5521_ = v___x_5517_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5519_);
                    v___x_5521_ = v_reuseFailAlloc_5524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5522_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                lean_ctor_set(v___x_5522_, 1, v_b_5489_);
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
    mut v_as_x27_5528_: *mut LeanObject,
    mut v_b_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5537_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5535_);
    lean_dec_ref(v___y_5534_);
    lean_dec(v___y_5533_);
    lean_dec_ref(v___y_5532_);
    lean_dec(v___y_5531_);
    lean_dec_ref(v___y_5530_);
    lean_dec(v_as_x27_5528_);
    return v_res_5537_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par___redArg(
    mut v_jobs_5538_: *mut LeanObject,
    mut v_a_5539_: *mut LeanObject,
    mut v_a_5540_: *mut LeanObject,
    mut v_a_5541_: *mut LeanObject,
    mut v_a_5542_: *mut LeanObject,
    mut v_a_5543_: *mut LeanObject,
    mut v_a_5544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5546_ = lean_st_ref_get(v_a_5540_);
                v___x_5547_ = lean_box(0);
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
                if lean_obj_tag(v___x_5548_) == 0 {
                    v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
                    lean_inc(v_a_5549_);
                    lean_dec_ref_known(v___x_5548_, 1);
                    v___x_5550_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_5549_, v___x_5547_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
                    lean_dec(v_a_5549_);
                    if lean_obj_tag(v___x_5550_) == 0 {
                        v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
                        v_isSharedCheck_5560_ = (!lean_is_exclusive(v___x_5550_)) as u8;
                        if v_isSharedCheck_5560_ == 0 {
                            v___x_5553_ = v___x_5550_;
                            v_isShared_5554_ = v_isSharedCheck_5560_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5551_);
                            lean_dec(v___x_5550_);
                            v___x_5553_ = lean_box(0);
                            v_isShared_5554_ = v_isSharedCheck_5560_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5546_);
                        return v___x_5550_;
                    }
                } else {
                    lean_dec(v___x_5546_);
                    v_a_5561_ = lean_ctor_get(v___x_5548_, 0);
                    v_isSharedCheck_5568_ = (!lean_is_exclusive(v___x_5548_)) as u8;
                    if v_isSharedCheck_5568_ == 0 {
                        v___x_5563_ = v___x_5548_;
                        v_isShared_5564_ = v_isSharedCheck_5568_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5561_);
                        lean_dec(v___x_5548_);
                        v___x_5563_ = lean_box(0);
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
                    lean_ctor_set(v___x_5553_, 0, v___x_5556_);
                    v___x_5558_ = v___x_5553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
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
                    v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
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
    mut v_jobs_5569_: *mut LeanObject,
    mut v_a_5570_: *mut LeanObject,
    mut v_a_5571_: *mut LeanObject,
    mut v_a_5572_: *mut LeanObject,
    mut v_a_5573_: *mut LeanObject,
    mut v_a_5574_: *mut LeanObject,
    mut v_a_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5577_: *mut LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_Lean_Elab_Term_TermElabM_par___redArg(
        v_jobs_5569_,
        v_a_5570_,
        v_a_5571_,
        v_a_5572_,
        v_a_5573_,
        v_a_5574_,
        v_a_5575_,
    );
    lean_dec(v_a_5575_);
    lean_dec_ref(v_a_5574_);
    lean_dec(v_a_5573_);
    lean_dec_ref(v_a_5572_);
    lean_dec(v_a_5571_);
    lean_dec_ref(v_a_5570_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par(
    mut v_00_u03b1_5578_: *mut LeanObject,
    mut v_jobs_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
    mut v_a_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5588_: *mut LeanObject,
    mut v_jobs_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
    mut v_a_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
    mut v_a_5594_: *mut LeanObject,
    mut v_a_5595_: *mut LeanObject,
    mut v_a_5596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5597_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5595_);
    lean_dec_ref(v_a_5594_);
    lean_dec(v_a_5593_);
    lean_dec_ref(v_a_5592_);
    lean_dec(v_a_5591_);
    lean_dec_ref(v_a_5590_);
    return v_res_5597_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(
    mut v_00_u03b1_5598_: *mut LeanObject,
    mut v_x_5599_: *mut LeanObject,
    mut v_x_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
    mut v___y_5602_: *mut LeanObject,
    mut v___y_5603_: *mut LeanObject,
    mut v___y_5604_: *mut LeanObject,
    mut v___y_5605_: *mut LeanObject,
    mut v___y_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5609_: *mut LeanObject,
    mut v_x_5610_: *mut LeanObject,
    mut v_x_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5619_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5617_);
    lean_dec_ref(v___y_5616_);
    lean_dec(v___y_5615_);
    lean_dec_ref(v___y_5614_);
    lean_dec(v___y_5613_);
    lean_dec_ref(v___y_5612_);
    return v_res_5619_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(
    mut v_00_u03b1_5620_: *mut LeanObject,
    mut v_as_5621_: *mut LeanObject,
    mut v_as_x27_5622_: *mut LeanObject,
    mut v_b_5623_: *mut LeanObject,
    mut v_a_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5633_: *mut LeanObject,
    mut v_as_5634_: *mut LeanObject,
    mut v_as_x27_5635_: *mut LeanObject,
    mut v_b_5636_: *mut LeanObject,
    mut v_a_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5645_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5643_);
    lean_dec_ref(v___y_5642_);
    lean_dec(v___y_5641_);
    lean_dec_ref(v___y_5640_);
    lean_dec(v___y_5639_);
    lean_dec_ref(v___y_5638_);
    lean_dec(v_as_x27_5635_);
    lean_dec(v_as_5634_);
    return v_res_5645_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(
    mut v_as_x27_5646_: *mut LeanObject,
    mut v_b_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
    mut v___y_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
    mut v___y_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570__overap_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5667_: u8 = 0;
    let mut v___y_5669_: u8 = 0;
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: u8 = 0;
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5646_) == 0 {
                    v___x_5655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5655_, 0, v_b_5647_);
                    return v___x_5655_;
                } else {
                    v_head_5656_ = lean_ctor_get(v_as_x27_5646_, 0);
                    v_tail_5657_ = lean_ctor_get(v_as_x27_5646_, 1);
                    lean_inc(v_head_5656_);
                    v___x_2570__overap_5658_ = lean_task_get_own(v_head_5656_);
                    lean_inc(v___y_5653_);
                    lean_inc_ref(v___y_5652_);
                    lean_inc(v___y_5651_);
                    lean_inc_ref(v___y_5650_);
                    lean_inc(v___y_5649_);
                    lean_inc_ref(v___y_5648_);
                    v___x_5659_ = lean_apply_7(
                        v___x_2570__overap_5658_,
                        v___y_5648_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                        v___y_5653_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5659_) == 0 {
                        v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
                        lean_inc(v_a_5660_);
                        lean_dec_ref_known(v___x_5659_, 1);
                        v___x_5661_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5661_, 0, v_a_5660_);
                        v___x_5662_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5662_, 0, v___x_5661_);
                        lean_ctor_set(v___x_5662_, 1, v_b_5647_);
                        v_as_x27_5646_ = v_tail_5657_;
                        v_b_5647_ = v___x_5662_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5664_ = lean_ctor_get(v___x_5659_, 0);
                        v_isSharedCheck_5678_ = (!lean_is_exclusive(v___x_5659_)) as u8;
                        if v_isSharedCheck_5678_ == 0 {
                            v___x_5666_ = v___x_5659_;
                            v_isShared_5667_ = v_isSharedCheck_5678_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5664_);
                            lean_dec(v___x_5659_);
                            v___x_5666_ = lean_box(0);
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
                    lean_inc(v_a_5664_);
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
                    lean_del_object(v___x_5666_);
                    v___x_5670_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5670_, 0, v_a_5664_);
                    v___x_5671_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5671_, 0, v___x_5670_);
                    lean_ctor_set(v___x_5671_, 1, v_b_5647_);
                    v_as_x27_5646_ = v_tail_5657_;
                    v_b_5647_ = v___x_5671_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_b_5647_);
                    if v_isShared_5667_ == 0 {
                        v___x_5674_ = v___x_5666_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5664_);
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
    mut v_as_x27_5679_: *mut LeanObject,
    mut v_b_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5688_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5686_);
    lean_dec_ref(v___y_5685_);
    lean_dec(v___y_5684_);
    lean_dec_ref(v___y_5683_);
    lean_dec(v___y_5682_);
    lean_dec_ref(v___y_5681_);
    lean_dec(v_as_x27_5679_);
    return v_res_5688_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27___redArg(
    mut v_jobs_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
    mut v_a_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5705_: u8 = 0;
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5711_: u8 = 0;
    let mut v_a_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5715_: u8 = 0;
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5697_ = lean_st_ref_get(v_a_5691_);
                v___x_5698_ = lean_box(0);
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
                if lean_obj_tag(v___x_5699_) == 0 {
                    v_a_5700_ = lean_ctor_get(v___x_5699_, 0);
                    lean_inc(v_a_5700_);
                    lean_dec_ref_known(v___x_5699_, 1);
                    v___x_5701_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_5700_, v___x_5698_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
                    lean_dec(v_a_5700_);
                    if lean_obj_tag(v___x_5701_) == 0 {
                        v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
                        v_isSharedCheck_5711_ = (!lean_is_exclusive(v___x_5701_)) as u8;
                        if v_isSharedCheck_5711_ == 0 {
                            v___x_5704_ = v___x_5701_;
                            v_isShared_5705_ = v_isSharedCheck_5711_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5702_);
                            lean_dec(v___x_5701_);
                            v___x_5704_ = lean_box(0);
                            v_isShared_5705_ = v_isSharedCheck_5711_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5697_);
                        return v___x_5701_;
                    }
                } else {
                    lean_dec(v___x_5697_);
                    v_a_5712_ = lean_ctor_get(v___x_5699_, 0);
                    v_isSharedCheck_5719_ = (!lean_is_exclusive(v___x_5699_)) as u8;
                    if v_isSharedCheck_5719_ == 0 {
                        v___x_5714_ = v___x_5699_;
                        v_isShared_5715_ = v_isSharedCheck_5719_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5712_);
                        lean_dec(v___x_5699_);
                        v___x_5714_ = lean_box(0);
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
                    lean_ctor_set(v___x_5704_, 0, v___x_5707_);
                    v___x_5709_ = v___x_5704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5707_);
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
                    v_reuseFailAlloc_5718_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5712_);
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
    mut v_jobs_5720_: *mut LeanObject,
    mut v_a_5721_: *mut LeanObject,
    mut v_a_5722_: *mut LeanObject,
    mut v_a_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
    mut v_a_5725_: *mut LeanObject,
    mut v_a_5726_: *mut LeanObject,
    mut v_a_5727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5728_: *mut LeanObject = core::ptr::null_mut();
    v_res_5728_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(
        v_jobs_5720_,
        v_a_5721_,
        v_a_5722_,
        v_a_5723_,
        v_a_5724_,
        v_a_5725_,
        v_a_5726_,
    );
    lean_dec(v_a_5726_);
    lean_dec_ref(v_a_5725_);
    lean_dec(v_a_5724_);
    lean_dec_ref(v_a_5723_);
    lean_dec(v_a_5722_);
    lean_dec_ref(v_a_5721_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_par_x27(
    mut v_00_u03b1_5729_: *mut LeanObject,
    mut v_jobs_5730_: *mut LeanObject,
    mut v_a_5731_: *mut LeanObject,
    mut v_a_5732_: *mut LeanObject,
    mut v_a_5733_: *mut LeanObject,
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
    mut v_a_5736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5739_: *mut LeanObject,
    mut v_jobs_5740_: *mut LeanObject,
    mut v_a_5741_: *mut LeanObject,
    mut v_a_5742_: *mut LeanObject,
    mut v_a_5743_: *mut LeanObject,
    mut v_a_5744_: *mut LeanObject,
    mut v_a_5745_: *mut LeanObject,
    mut v_a_5746_: *mut LeanObject,
    mut v_a_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5748_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5746_);
    lean_dec_ref(v_a_5745_);
    lean_dec(v_a_5744_);
    lean_dec_ref(v_a_5743_);
    lean_dec(v_a_5742_);
    lean_dec_ref(v_a_5741_);
    return v_res_5748_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(
    mut v_00_u03b1_5749_: *mut LeanObject,
    mut v_as_5750_: *mut LeanObject,
    mut v_as_x27_5751_: *mut LeanObject,
    mut v_b_5752_: *mut LeanObject,
    mut v_a_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5762_: *mut LeanObject,
    mut v_as_5763_: *mut LeanObject,
    mut v_as_x27_5764_: *mut LeanObject,
    mut v_b_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5774_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5772_);
    lean_dec_ref(v___y_5771_);
    lean_dec(v___y_5770_);
    lean_dec_ref(v___y_5769_);
    lean_dec(v___y_5768_);
    lean_dec_ref(v___y_5767_);
    lean_dec(v_as_x27_5764_);
    lean_dec(v_as_5763_);
    return v_res_5774_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    v___x_5775_ = lean_box(1);
    v___x_5776_ = l_Lean_MessageData_ofFormat(v___x_5775_);
    return v___x_5776_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    v___x_5780_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2;
    v___x_5781_ = l_Lean_MessageData_ofFormat(v___x_5780_);
    return v___x_5781_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(
    mut v_x_5782_: *mut LeanObject,
    mut v_x_5783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5788_: u8 = 0;
    let mut v_before_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5792_: u8 = 0;
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5805_: u8 = 0;
    let mut v_unused_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5783_) == 0 {
                    return v_x_5782_;
                } else {
                    v_head_5784_ = lean_ctor_get(v_x_5783_, 0);
                    v_tail_5785_ = lean_ctor_get(v_x_5783_, 1);
                    v_isSharedCheck_5807_ = (!lean_is_exclusive(v_x_5783_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5787_ = v_x_5783_;
                        v_isShared_5788_ = v_isSharedCheck_5807_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5785_);
                        lean_inc(v_head_5784_);
                        lean_dec(v_x_5783_);
                        v___x_5787_ = lean_box(0);
                        v_isShared_5788_ = v_isSharedCheck_5807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5789_ = lean_ctor_get(v_head_5784_, 0);
                v_isSharedCheck_5805_ = (!lean_is_exclusive(v_head_5784_)) as u8;
                if v_isSharedCheck_5805_ == 0 {
                    v_unused_5806_ = lean_ctor_get(v_head_5784_, 1);
                    lean_dec(v_unused_5806_);
                    v___x_5791_ = v_head_5784_;
                    v_isShared_5792_ = v_isSharedCheck_5805_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_5789_);
                    lean_dec(v_head_5784_);
                    v___x_5791_ = lean_box(0);
                    v_isShared_5792_ = v_isSharedCheck_5805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5793_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
                if v_isShared_5792_ == 0 {
                    lean_ctor_set_tag(v___x_5791_, 7);
                    lean_ctor_set(v___x_5791_, 1, v___x_5793_);
                    lean_ctor_set(v___x_5791_, 0, v_x_5782_);
                    v___x_5795_ = v___x_5791_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5804_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_x_5782_);
                    lean_ctor_set(v_reuseFailAlloc_5804_, 1, v___x_5793_);
                    v___x_5795_ = v_reuseFailAlloc_5804_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5796_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
                if v_isShared_5788_ == 0 {
                    lean_ctor_set_tag(v___x_5787_, 7);
                    lean_ctor_set(v___x_5787_, 1, v___x_5796_);
                    lean_ctor_set(v___x_5787_, 0, v___x_5795_);
                    v___x_5798_ = v___x_5787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5803_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5795_);
                    lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5796_);
                    v___x_5798_ = v_reuseFailAlloc_5803_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5799_ = l_Lean_MessageData_ofSyntax(v_before_5789_);
                v___x_5800_ = l_Lean_indentD(v___x_5799_);
                v___x_5801_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5801_, 0, v___x_5798_);
                lean_ctor_set(v___x_5801_, 1, v___x_5800_);
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
    mut v_opts_5808_: *mut LeanObject,
    mut v_opt_5809_: *mut LeanObject,
) -> u8 {
    let mut v_name_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    v_name_5810_ = lean_ctor_get(v_opt_5809_, 0);
    v_defValue_5811_ = lean_ctor_get(v_opt_5809_, 1);
    v_map_5812_ = lean_ctor_get(v_opts_5808_, 0);
    v___x_5813_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5812_,
            v_name_5810_,
        );
    if lean_obj_tag(v___x_5813_) == 0 {
        let mut v___x_5814_: u8 = 0;
        v___x_5814_ = (lean_unbox(v_defValue_5811_) as u8);
        return v___x_5814_;
    } else {
        let mut v_val_5815_: *mut LeanObject = core::ptr::null_mut();
        v_val_5815_ = lean_ctor_get(v___x_5813_, 0);
        lean_inc(v_val_5815_);
        lean_dec_ref_known(v___x_5813_, 1);
        if lean_obj_tag(v_val_5815_) == 1 {
            let mut v_v_5816_: u8 = 0;
            v_v_5816_ = lean_ctor_get_uint8(v_val_5815_, 0 as u32);
            lean_dec_ref_known(v_val_5815_, 0);
            return v_v_5816_;
        } else {
            let mut v___x_5817_: u8 = 0;
            lean_dec(v_val_5815_);
            v___x_5817_ = (lean_unbox(v_defValue_5811_) as u8);
            return v___x_5817_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(
    mut v_opts_5818_: *mut LeanObject,
    mut v_opt_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5820_: u8 = 0;
    let mut v_r_5821_: *mut LeanObject = core::ptr::null_mut();
    v_res_5820_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_5818_, v_opt_5819_);
    lean_dec_ref(v_opt_5819_);
    lean_dec_ref(v_opts_5818_);
    v_r_5821_ = lean_box((v_res_5820_) as usize);
    return v_r_5821_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v___x_5825_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1;
    v___x_5826_ = l_Lean_MessageData_ofFormat(v___x_5825_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(
    mut v_msgData_5827_: *mut LeanObject,
    mut v_macroStack_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: u8 = 0;
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_unused_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5831_ = lean_ctor_get(v___y_5829_, 2);
                v___x_5832_ = l_Lean_Elab_pp_macroStack;
                v___x_5833_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_options_5831_, v___x_5832_);
                if v___x_5833_ == 0 {
                    lean_dec(v_macroStack_5828_);
                    v___x_5834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5834_, 0, v_msgData_5827_);
                    return v___x_5834_;
                } else {
                    if lean_obj_tag(v_macroStack_5828_) == 0 {
                        v___x_5835_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5835_, 0, v_msgData_5827_);
                        return v___x_5835_;
                    } else {
                        v_head_5836_ = lean_ctor_get(v_macroStack_5828_, 0);
                        lean_inc(v_head_5836_);
                        v_after_5837_ = lean_ctor_get(v_head_5836_, 1);
                        v_isSharedCheck_5852_ = (!lean_is_exclusive(v_head_5836_)) as u8;
                        if v_isSharedCheck_5852_ == 0 {
                            v_unused_5853_ = lean_ctor_get(v_head_5836_, 0);
                            lean_dec(v_unused_5853_);
                            v___x_5839_ = v_head_5836_;
                            v_isShared_5840_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_5837_);
                            lean_dec(v_head_5836_);
                            v___x_5839_ = lean_box(0);
                            v_isShared_5840_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5841_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
                if v_isShared_5840_ == 0 {
                    lean_ctor_set_tag(v___x_5839_, 7);
                    lean_ctor_set(v___x_5839_, 1, v___x_5841_);
                    lean_ctor_set(v___x_5839_, 0, v_msgData_5827_);
                    v___x_5843_ = v___x_5839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_msgData_5827_);
                    lean_ctor_set(v_reuseFailAlloc_5851_, 1, v___x_5841_);
                    v___x_5843_ = v_reuseFailAlloc_5851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5844_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
                v___x_5845_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5845_, 0, v___x_5843_);
                lean_ctor_set(v___x_5845_, 1, v___x_5844_);
                v___x_5846_ = l_Lean_MessageData_ofSyntax(v_after_5837_);
                v___x_5847_ = l_Lean_indentD(v___x_5846_);
                v_msgData_5848_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_5848_, 0, v___x_5845_);
                lean_ctor_set(v_msgData_5848_, 1, v___x_5847_);
                v___x_5849_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_5848_, v_macroStack_5828_);
                v___x_5850_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5850_, 0, v___x_5849_);
                return v___x_5850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(
    mut v_msgData_5854_: *mut LeanObject,
    mut v_macroStack_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5858_: *mut LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_5854_, v_macroStack_5855_, v___y_5856_);
    lean_dec_ref(v___y_5856_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(
    mut v_msg_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
    mut v___y_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5867_ = lean_ctor_get(v___y_5864_, 5);
                v___x_5868_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_5859_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
                v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
                lean_inc(v_a_5869_);
                lean_dec_ref(v___x_5868_);
                v_macroStack_5870_ = lean_ctor_get(v___y_5860_, 1);
                v___x_5871_ = l_Lean_Elab_getBetterRef(v_ref_5867_, v_macroStack_5870_);
                lean_inc(v_macroStack_5870_);
                v___x_5872_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_5869_, v_macroStack_5870_, v___y_5864_);
                v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
                v_isSharedCheck_5881_ = (!lean_is_exclusive(v___x_5872_)) as u8;
                if v_isSharedCheck_5881_ == 0 {
                    v___x_5875_ = v___x_5872_;
                    v_isShared_5876_ = v_isSharedCheck_5881_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5873_);
                    lean_dec(v___x_5872_);
                    v___x_5875_ = lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5877_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5877_, 0, v___x_5871_);
                lean_ctor_set(v___x_5877_, 1, v_a_5873_);
                if v_isShared_5876_ == 0 {
                    lean_ctor_set_tag(v___x_5875_, 1);
                    lean_ctor_set(v___x_5875_, 0, v___x_5877_);
                    v___x_5879_ = v___x_5875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5880_, 0, v___x_5877_);
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
    mut v_msg_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
    mut v___y_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
    mut v___y_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5890_: *mut LeanObject = core::ptr::null_mut();
    v_res_5890_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(
        v_msg_5882_,
        v___y_5883_,
        v___y_5884_,
        v___y_5885_,
        v___y_5886_,
        v___y_5887_,
        v___y_5888_,
    );
    lean_dec(v___y_5888_);
    lean_dec_ref(v___y_5887_);
    lean_dec(v___y_5886_);
    lean_dec_ref(v___y_5885_);
    lean_dec(v___y_5884_);
    lean_dec_ref(v___y_5883_);
    return v_res_5890_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(
    mut v_a_5891_: *mut LeanObject,
    mut v___x_5892_: *mut LeanObject,
    mut v_____r_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
    mut v___y_5895_: *mut LeanObject,
    mut v___y_5896_: *mut LeanObject,
    mut v___y_5897_: *mut LeanObject,
    mut v___y_5898_: *mut LeanObject,
    mut v___y_5899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    v___x_5901_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5901_, 0, v_a_5891_);
    v___x_5902_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5902_, 0, v___x_5901_);
    lean_ctor_set(v___x_5902_, 1, v___x_5892_);
    v___x_5903_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5903_, 0, v___x_5902_);
    v___x_5904_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5904_, 0, v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_5905_: *mut LeanObject,
    mut v___x_5906_: *mut LeanObject,
    mut v_____r_5907_: *mut LeanObject,
    mut v___y_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
    mut v___y_5911_: *mut LeanObject,
    mut v___y_5912_: *mut LeanObject,
    mut v___y_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5915_: *mut LeanObject = core::ptr::null_mut();
    v_res_5915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5905_, v___x_5906_, v_____r_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
    lean_dec(v___y_5913_);
    lean_dec_ref(v___y_5912_);
    lean_dec(v___y_5911_);
    lean_dec_ref(v___y_5910_);
    lean_dec(v___y_5909_);
    lean_dec_ref(v___y_5908_);
    return v_res_5915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(
    mut v_cancel_5916_: u8,
    mut v_fst_5917_: *mut LeanObject,
    mut v_a_5918_: *mut LeanObject,
    mut v_b_5919_: *mut LeanObject,
    mut v___y_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
    mut v___y_5923_: *mut LeanObject,
    mut v___y_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5936_: u8 = 0;
    let mut v_a_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5943_: u8 = 0;
    let mut v_a_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5947_: u8 = 0;
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5965_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: u8 = 0;
    let mut v_isSharedCheck_5972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5918_) == 0 {
                    lean_dec_ref(v_fst_5917_);
                    v___x_5927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5927_, 0, v_b_5919_);
                    return v___x_5927_;
                } else {
                    lean_dec_ref(v_b_5919_);
                    v___x_5928_ = l_IO_waitAny_x27___redArg(v_a_5918_);
                    v_fst_5929_ = lean_ctor_get(v___x_5928_, 0);
                    lean_inc(v_fst_5929_);
                    v_snd_5930_ = lean_ctor_get(v___x_5928_, 1);
                    lean_inc(v_snd_5930_);
                    lean_dec_ref(v___x_5928_);
                    v___x_5952_ = lean_box(0);
                    lean_inc(v___y_5925_);
                    lean_inc_ref(v___y_5924_);
                    lean_inc(v___y_5923_);
                    lean_inc_ref(v___y_5922_);
                    lean_inc(v___y_5921_);
                    lean_inc_ref(v___y_5920_);
                    v___x_5953_ = lean_apply_7(
                        v_fst_5929_,
                        v___y_5920_,
                        v___y_5921_,
                        v___y_5922_,
                        v___y_5923_,
                        v___y_5924_,
                        v___y_5925_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5953_) == 0 {
                        if v_cancel_5916_ == 0 {
                            v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
                            lean_inc(v_a_5954_);
                            lean_dec_ref_known(v___x_5953_, 1);
                            v___x_5955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5954_, v___x_5952_, v___x_5952_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
                            v___y_5932_ = v___x_5955_;
                            state = 1;
                            continue;
                        } else {
                            v_a_5956_ = lean_ctor_get(v___x_5953_, 0);
                            lean_inc(v_a_5956_);
                            lean_dec_ref_known(v___x_5953_, 1);
                            lean_inc_ref(v_fst_5917_);
                            v___x_5957_ = lean_apply_1(v_fst_5917_, lean_box(0));
                            v___x_5958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_5956_, v___x_5952_, v___x_5957_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
                            v___y_5932_ = v___x_5958_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5959_ = lean_ctor_get(v___x_5953_, 0);
                        v_isSharedCheck_5972_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                        if v_isSharedCheck_5972_ == 0 {
                            v___x_5961_ = v___x_5953_;
                            v_isShared_5962_ = v_isSharedCheck_5972_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5959_);
                            lean_dec(v___x_5953_);
                            v___x_5961_ = lean_box(0);
                            v_isShared_5962_ = v_isSharedCheck_5972_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_5932_) == 0 {
                    v_a_5933_ = lean_ctor_get(v___y_5932_, 0);
                    v_isSharedCheck_5943_ = (!lean_is_exclusive(v___y_5932_)) as u8;
                    if v_isSharedCheck_5943_ == 0 {
                        v___x_5935_ = v___y_5932_;
                        v_isShared_5936_ = v_isSharedCheck_5943_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5933_);
                        lean_dec(v___y_5932_);
                        v___x_5935_ = lean_box(0);
                        v_isShared_5936_ = v_isSharedCheck_5943_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_5930_);
                    lean_dec_ref(v_fst_5917_);
                    v_a_5944_ = lean_ctor_get(v___y_5932_, 0);
                    v_isSharedCheck_5951_ = (!lean_is_exclusive(v___y_5932_)) as u8;
                    if v_isSharedCheck_5951_ == 0 {
                        v___x_5946_ = v___y_5932_;
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5944_);
                        lean_dec(v___y_5932_);
                        v___x_5946_ = lean_box(0);
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5933_) == 0 {
                    lean_dec(v_snd_5930_);
                    lean_dec_ref(v_fst_5917_);
                    v_a_5937_ = lean_ctor_get(v_a_5933_, 0);
                    lean_inc(v_a_5937_);
                    lean_dec_ref_known(v_a_5933_, 1);
                    if v_isShared_5936_ == 0 {
                        lean_ctor_set(v___x_5935_, 0, v_a_5937_);
                        v___x_5939_ = v___x_5935_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5937_);
                        v___x_5939_ = v_reuseFailAlloc_5940_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5935_);
                    v_a_5941_ = lean_ctor_get(v_a_5933_, 0);
                    lean_inc(v_a_5941_);
                    lean_dec_ref_known(v_a_5933_, 1);
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
                    v_reuseFailAlloc_5950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_a_5944_);
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
                    lean_inc(v_a_5959_);
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
                    lean_del_object(v___x_5961_);
                    lean_dec(v_a_5959_);
                    v_a_5918_ = v_snd_5930_;
                    v_b_5919_ = v___x_5963_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_snd_5930_);
                    lean_dec_ref(v_fst_5917_);
                    if v_isShared_5962_ == 0 {
                        v___x_5968_ = v___x_5961_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5959_);
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
    mut v_cancel_5973_: *mut LeanObject,
    mut v_fst_5974_: *mut LeanObject,
    mut v_a_5975_: *mut LeanObject,
    mut v_b_5976_: *mut LeanObject,
    mut v___y_5977_: *mut LeanObject,
    mut v___y_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_5984_: u8 = 0;
    let mut v_res_5985_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_5984_ = (lean_unbox(v_cancel_5973_) as u8);
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
    lean_dec(v___y_5982_);
    lean_dec_ref(v___y_5981_);
    lean_dec(v___y_5980_);
    lean_dec_ref(v___y_5979_);
    lean_dec(v___y_5978_);
    lean_dec_ref(v___y_5977_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst___redArg(
    mut v_jobs_5986_: *mut LeanObject,
    mut v_cancel_5987_: u8,
    mut v_a_5988_: *mut LeanObject,
    mut v_a_5989_: *mut LeanObject,
    mut v_a_5990_: *mut LeanObject,
    mut v_a_5991_: *mut LeanObject,
    mut v_a_5992_: *mut LeanObject,
    mut v_a_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v_fst_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6012_: u8 = 0;
    let mut v_a_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6020_: u8 = 0;
    let mut v_a_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6024_: u8 = 0;
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6027_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5995_) == 0 {
                    v_a_5996_ = lean_ctor_get(v___x_5995_, 0);
                    lean_inc(v_a_5996_);
                    lean_dec_ref_known(v___x_5995_, 1);
                    v_fst_5997_ = lean_ctor_get(v_a_5996_, 0);
                    lean_inc(v_fst_5997_);
                    v_snd_5998_ = lean_ctor_get(v_a_5996_, 1);
                    lean_inc(v_snd_5998_);
                    lean_dec(v_a_5996_);
                    v___x_5999_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_6000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_5987_, v_fst_5997_, v_snd_5998_, v___x_5999_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
                    if lean_obj_tag(v___x_6000_) == 0 {
                        v_a_6001_ = lean_ctor_get(v___x_6000_, 0);
                        v_isSharedCheck_6012_ = (!lean_is_exclusive(v___x_6000_)) as u8;
                        if v_isSharedCheck_6012_ == 0 {
                            v___x_6003_ = v___x_6000_;
                            v_isShared_6004_ = v_isSharedCheck_6012_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6001_);
                            lean_dec(v___x_6000_);
                            v___x_6003_ = lean_box(0);
                            v_isShared_6004_ = v_isSharedCheck_6012_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6013_ = lean_ctor_get(v___x_6000_, 0);
                        v_isSharedCheck_6020_ = (!lean_is_exclusive(v___x_6000_)) as u8;
                        if v_isSharedCheck_6020_ == 0 {
                            v___x_6015_ = v___x_6000_;
                            v_isShared_6016_ = v_isSharedCheck_6020_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6013_);
                            lean_dec(v___x_6000_);
                            v___x_6015_ = lean_box(0);
                            v_isShared_6016_ = v_isSharedCheck_6020_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6021_ = lean_ctor_get(v___x_5995_, 0);
                    v_isSharedCheck_6028_ = (!lean_is_exclusive(v___x_5995_)) as u8;
                    if v_isSharedCheck_6028_ == 0 {
                        v___x_6023_ = v___x_5995_;
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6021_);
                        lean_dec(v___x_5995_);
                        v___x_6023_ = lean_box(0);
                        v_isShared_6024_ = v_isSharedCheck_6028_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6005_ = lean_ctor_get(v_a_6001_, 0);
                lean_inc(v_fst_6005_);
                lean_dec(v_a_6001_);
                if lean_obj_tag(v_fst_6005_) == 0 {
                    lean_del_object(v___x_6003_);
                    v___x_6006_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_6007_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_6006_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
                    return v___x_6007_;
                } else {
                    v_val_6008_ = lean_ctor_get(v_fst_6005_, 0);
                    lean_inc(v_val_6008_);
                    lean_dec_ref_known(v_fst_6005_, 1);
                    if v_isShared_6004_ == 0 {
                        lean_ctor_set(v___x_6003_, 0, v_val_6008_);
                        v___x_6010_ = v___x_6003_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_val_6008_);
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
                    v_reuseFailAlloc_6019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6019_, 0, v_a_6013_);
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
                    v_reuseFailAlloc_6027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
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
    mut v_jobs_6029_: *mut LeanObject,
    mut v_cancel_6030_: *mut LeanObject,
    mut v_a_6031_: *mut LeanObject,
    mut v_a_6032_: *mut LeanObject,
    mut v_a_6033_: *mut LeanObject,
    mut v_a_6034_: *mut LeanObject,
    mut v_a_6035_: *mut LeanObject,
    mut v_a_6036_: *mut LeanObject,
    mut v_a_6037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_6038_: u8 = 0;
    let mut v_res_6039_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6038_ = (lean_unbox(v_cancel_6030_) as u8);
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
    lean_dec(v_a_6036_);
    lean_dec_ref(v_a_6035_);
    lean_dec(v_a_6034_);
    lean_dec_ref(v_a_6033_);
    lean_dec(v_a_6032_);
    lean_dec_ref(v_a_6031_);
    return v_res_6039_;
}
pub unsafe fn l_Lean_Elab_Term_TermElabM_parFirst(
    mut v_00_u03b1_6040_: *mut LeanObject,
    mut v_jobs_6041_: *mut LeanObject,
    mut v_cancel_6042_: u8,
    mut v_a_6043_: *mut LeanObject,
    mut v_a_6044_: *mut LeanObject,
    mut v_a_6045_: *mut LeanObject,
    mut v_a_6046_: *mut LeanObject,
    mut v_a_6047_: *mut LeanObject,
    mut v_a_6048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6051_: *mut LeanObject,
    mut v_jobs_6052_: *mut LeanObject,
    mut v_cancel_6053_: *mut LeanObject,
    mut v_a_6054_: *mut LeanObject,
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
    mut v_a_6057_: *mut LeanObject,
    mut v_a_6058_: *mut LeanObject,
    mut v_a_6059_: *mut LeanObject,
    mut v_a_6060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_6061_: u8 = 0;
    let mut v_res_6062_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6061_ = (lean_unbox(v_cancel_6053_) as u8);
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
    lean_dec(v_a_6059_);
    lean_dec_ref(v_a_6058_);
    lean_dec(v_a_6057_);
    lean_dec_ref(v_a_6056_);
    lean_dec(v_a_6055_);
    lean_dec_ref(v_a_6054_);
    return v_res_6062_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(
    mut v_00_u03b1_6063_: *mut LeanObject,
    mut v_cancel_6064_: u8,
    mut v_fst_6065_: *mut LeanObject,
    mut v_inst_6066_: *mut LeanObject,
    mut v_R_6067_: *mut LeanObject,
    mut v_a_6068_: *mut LeanObject,
    mut v_b_6069_: *mut LeanObject,
    mut v_c_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6079_: *mut LeanObject,
    mut v_cancel_6080_: *mut LeanObject,
    mut v_fst_6081_: *mut LeanObject,
    mut v_inst_6082_: *mut LeanObject,
    mut v_R_6083_: *mut LeanObject,
    mut v_a_6084_: *mut LeanObject,
    mut v_b_6085_: *mut LeanObject,
    mut v_c_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_6094_: u8 = 0;
    let mut v_res_6095_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_6094_ = (lean_unbox(v_cancel_6080_) as u8);
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
    lean_dec(v___y_6092_);
    lean_dec_ref(v___y_6091_);
    lean_dec(v___y_6090_);
    lean_dec_ref(v___y_6089_);
    lean_dec(v___y_6088_);
    lean_dec_ref(v___y_6087_);
    return v_res_6095_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(
    mut v_00_u03b1_6096_: *mut LeanObject,
    mut v_msg_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
    mut v___y_6099_: *mut LeanObject,
    mut v___y_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6106_: *mut LeanObject,
    mut v_msg_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
    mut v___y_6109_: *mut LeanObject,
    mut v___y_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
    mut v___y_6112_: *mut LeanObject,
    mut v___y_6113_: *mut LeanObject,
    mut v___y_6114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6115_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6113_);
    lean_dec_ref(v___y_6112_);
    lean_dec(v___y_6111_);
    lean_dec_ref(v___y_6110_);
    lean_dec(v___y_6109_);
    lean_dec_ref(v___y_6108_);
    return v_res_6115_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(
    mut v_msgData_6116_: *mut LeanObject,
    mut v_macroStack_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
    mut v___y_6123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    v___x_6125_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_6116_, v_macroStack_6117_, v___y_6122_);
    return v___x_6125_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(
    mut v_msgData_6126_: *mut LeanObject,
    mut v_macroStack_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
    mut v___y_6132_: *mut LeanObject,
    mut v___y_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6135_: *mut LeanObject = core::ptr::null_mut();
    v_res_6135_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_6126_, v_macroStack_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
    lean_dec(v___y_6133_);
    lean_dec_ref(v___y_6132_);
    lean_dec(v___y_6131_);
    lean_dec_ref(v___y_6130_);
    lean_dec(v___y_6129_);
    lean_dec_ref(v___y_6128_);
    return v_res_6135_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(
    mut v_x_6136_: *mut LeanObject,
    mut v_x_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v_isSharedCheck_6168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6136_) == 0 {
                    v___x_6147_ = l_List_reverse___redArg(v_x_6137_);
                    v___x_6148_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6148_, 0, v___x_6147_);
                    return v___x_6148_;
                } else {
                    v_head_6149_ = lean_ctor_get(v_x_6136_, 0);
                    v_tail_6150_ = lean_ctor_get(v_x_6136_, 1);
                    v_isSharedCheck_6168_ = (!lean_is_exclusive(v_x_6136_)) as u8;
                    if v_isSharedCheck_6168_ == 0 {
                        v___x_6152_ = v_x_6136_;
                        v_isShared_6153_ = v_isSharedCheck_6168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6150_);
                        lean_inc(v_head_6149_);
                        lean_dec(v_x_6136_);
                        v___x_6152_ = lean_box(0);
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
                if lean_obj_tag(v___x_6154_) == 0 {
                    v_a_6155_ = lean_ctor_get(v___x_6154_, 0);
                    lean_inc(v_a_6155_);
                    lean_dec_ref_known(v___x_6154_, 1);
                    if v_isShared_6153_ == 0 {
                        lean_ctor_set(v___x_6152_, 1, v_x_6137_);
                        lean_ctor_set(v___x_6152_, 0, v_a_6155_);
                        v___x_6157_ = v___x_6152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6159_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_a_6155_);
                        lean_ctor_set(v_reuseFailAlloc_6159_, 1, v_x_6137_);
                        v___x_6157_ = v_reuseFailAlloc_6159_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6152_);
                    lean_dec(v_tail_6150_);
                    lean_dec(v_x_6137_);
                    v_a_6160_ = lean_ctor_get(v___x_6154_, 0);
                    v_isSharedCheck_6167_ = (!lean_is_exclusive(v___x_6154_)) as u8;
                    if v_isSharedCheck_6167_ == 0 {
                        v___x_6162_ = v___x_6154_;
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6160_);
                        lean_dec(v___x_6154_);
                        v___x_6162_ = lean_box(0);
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
                    v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
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
    mut v_x_6169_: *mut LeanObject,
    mut v_x_6170_: *mut LeanObject,
    mut v___y_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6180_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6178_);
    lean_dec_ref(v___y_6177_);
    lean_dec(v___y_6176_);
    lean_dec_ref(v___y_6175_);
    lean_dec(v___y_6174_);
    lean_dec_ref(v___y_6173_);
    lean_dec(v___y_6172_);
    lean_dec_ref(v___y_6171_);
    return v_res_6180_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(
    mut v_jobs_6181_: *mut LeanObject,
    mut v_a_6182_: *mut LeanObject,
    mut v_a_6183_: *mut LeanObject,
    mut v_a_6184_: *mut LeanObject,
    mut v_a_6185_: *mut LeanObject,
    mut v_a_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
    mut v_a_6189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6196_: u8 = 0;
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut v_a_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6215_: u8 = 0;
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6191_ = lean_box(0);
                v___x_6192_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_6181_, v___x_6191_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
                if lean_obj_tag(v___x_6192_) == 0 {
                    v_a_6193_ = lean_ctor_get(v___x_6192_, 0);
                    v_isSharedCheck_6211_ = (!lean_is_exclusive(v___x_6192_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v___x_6195_ = v___x_6192_;
                        v_isShared_6196_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6193_);
                        lean_dec(v___x_6192_);
                        v___x_6195_ = lean_box(0);
                        v_isShared_6196_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6212_ = lean_ctor_get(v___x_6192_, 0);
                    v_isSharedCheck_6219_ = (!lean_is_exclusive(v___x_6192_)) as u8;
                    if v_isSharedCheck_6219_ == 0 {
                        v___x_6214_ = v___x_6192_;
                        v_isShared_6215_ = v_isSharedCheck_6219_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6212_);
                        lean_dec(v___x_6192_);
                        v___x_6214_ = lean_box(0);
                        v_isShared_6215_ = v_isSharedCheck_6219_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6197_ = l_List_unzipTR___redArg(v_a_6193_);
                v_fst_6198_ = lean_ctor_get(v___x_6197_, 0);
                v_snd_6199_ = lean_ctor_get(v___x_6197_, 1);
                v_isSharedCheck_6210_ = (!lean_is_exclusive(v___x_6197_)) as u8;
                if v_isSharedCheck_6210_ == 0 {
                    v___x_6201_ = v___x_6197_;
                    v_isShared_6202_ = v_isSharedCheck_6210_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_6199_);
                    lean_inc(v_fst_6198_);
                    lean_dec(v___x_6197_);
                    v___x_6201_ = lean_box(0);
                    v_isShared_6202_ = v_isSharedCheck_6210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6203_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_6203_, 0, v_fst_6198_);
                if v_isShared_6202_ == 0 {
                    lean_ctor_set(v___x_6201_, 0, v___x_6203_);
                    v___x_6205_ = v___x_6201_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6209_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6209_, 0, v___x_6203_);
                    lean_ctor_set(v_reuseFailAlloc_6209_, 1, v_snd_6199_);
                    v___x_6205_ = v_reuseFailAlloc_6209_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6196_ == 0 {
                    lean_ctor_set(v___x_6195_, 0, v___x_6205_);
                    v___x_6207_ = v___x_6195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6205_);
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
                    v_reuseFailAlloc_6218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6218_, 0, v_a_6212_);
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
    mut v_jobs_6220_: *mut LeanObject,
    mut v_a_6221_: *mut LeanObject,
    mut v_a_6222_: *mut LeanObject,
    mut v_a_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
    mut v_a_6225_: *mut LeanObject,
    mut v_a_6226_: *mut LeanObject,
    mut v_a_6227_: *mut LeanObject,
    mut v_a_6228_: *mut LeanObject,
    mut v_a_6229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6230_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6228_);
    lean_dec_ref(v_a_6227_);
    lean_dec(v_a_6226_);
    lean_dec_ref(v_a_6225_);
    lean_dec(v_a_6224_);
    lean_dec_ref(v_a_6223_);
    lean_dec(v_a_6222_);
    lean_dec_ref(v_a_6221_);
    return v_res_6230_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterWithCancel(
    mut v_00_u03b1_6231_: *mut LeanObject,
    mut v_jobs_6232_: *mut LeanObject,
    mut v_a_6233_: *mut LeanObject,
    mut v_a_6234_: *mut LeanObject,
    mut v_a_6235_: *mut LeanObject,
    mut v_a_6236_: *mut LeanObject,
    mut v_a_6237_: *mut LeanObject,
    mut v_a_6238_: *mut LeanObject,
    mut v_a_6239_: *mut LeanObject,
    mut v_a_6240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6243_: *mut LeanObject,
    mut v_jobs_6244_: *mut LeanObject,
    mut v_a_6245_: *mut LeanObject,
    mut v_a_6246_: *mut LeanObject,
    mut v_a_6247_: *mut LeanObject,
    mut v_a_6248_: *mut LeanObject,
    mut v_a_6249_: *mut LeanObject,
    mut v_a_6250_: *mut LeanObject,
    mut v_a_6251_: *mut LeanObject,
    mut v_a_6252_: *mut LeanObject,
    mut v_a_6253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6254_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6252_);
    lean_dec_ref(v_a_6251_);
    lean_dec(v_a_6250_);
    lean_dec_ref(v_a_6249_);
    lean_dec(v_a_6248_);
    lean_dec_ref(v_a_6247_);
    lean_dec(v_a_6246_);
    lean_dec_ref(v_a_6245_);
    return v_res_6254_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(
    mut v_00_u03b1_6255_: *mut LeanObject,
    mut v_x_6256_: *mut LeanObject,
    mut v_x_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
    mut v___y_6265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6268_: *mut LeanObject,
    mut v_x_6269_: *mut LeanObject,
    mut v_x_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
    mut v___y_6272_: *mut LeanObject,
    mut v___y_6273_: *mut LeanObject,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
    mut v___y_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6280_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6278_);
    lean_dec_ref(v___y_6277_);
    lean_dec(v___y_6276_);
    lean_dec_ref(v___y_6275_);
    lean_dec(v___y_6274_);
    lean_dec_ref(v___y_6273_);
    lean_dec(v___y_6272_);
    lean_dec_ref(v___y_6271_);
    return v_res_6280_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter___redArg(
    mut v_jobs_6281_: *mut LeanObject,
    mut v_a_6282_: *mut LeanObject,
    mut v_a_6283_: *mut LeanObject,
    mut v_a_6284_: *mut LeanObject,
    mut v_a_6285_: *mut LeanObject,
    mut v_a_6286_: *mut LeanObject,
    mut v_a_6287_: *mut LeanObject,
    mut v_a_6288_: *mut LeanObject,
    mut v_a_6289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_snd_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v_a_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6304_: u8 = 0;
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_6291_) == 0 {
                    v_a_6292_ = lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6300_ = (!lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6292_);
                        lean_dec(v___x_6291_);
                        v___x_6294_ = lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6300_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6301_ = lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6308_ = (!lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6308_ == 0 {
                        v___x_6303_ = v___x_6291_;
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6301_);
                        lean_dec(v___x_6291_);
                        v___x_6303_ = lean_box(0);
                        v_isShared_6304_ = v_isSharedCheck_6308_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6296_ = lean_ctor_get(v_a_6292_, 1);
                lean_inc(v_snd_6296_);
                lean_dec(v_a_6292_);
                if v_isShared_6295_ == 0 {
                    lean_ctor_set(v___x_6294_, 0, v_snd_6296_);
                    v___x_6298_ = v___x_6294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_snd_6296_);
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
                    v_reuseFailAlloc_6307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_a_6301_);
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
    mut v_jobs_6309_: *mut LeanObject,
    mut v_a_6310_: *mut LeanObject,
    mut v_a_6311_: *mut LeanObject,
    mut v_a_6312_: *mut LeanObject,
    mut v_a_6313_: *mut LeanObject,
    mut v_a_6314_: *mut LeanObject,
    mut v_a_6315_: *mut LeanObject,
    mut v_a_6316_: *mut LeanObject,
    mut v_a_6317_: *mut LeanObject,
    mut v_a_6318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6319_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6317_);
    lean_dec_ref(v_a_6316_);
    lean_dec(v_a_6315_);
    lean_dec_ref(v_a_6314_);
    lean_dec(v_a_6313_);
    lean_dec_ref(v_a_6312_);
    lean_dec(v_a_6311_);
    lean_dec_ref(v_a_6310_);
    return v_res_6319_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIter(
    mut v_00_u03b1_6320_: *mut LeanObject,
    mut v_jobs_6321_: *mut LeanObject,
    mut v_a_6322_: *mut LeanObject,
    mut v_a_6323_: *mut LeanObject,
    mut v_a_6324_: *mut LeanObject,
    mut v_a_6325_: *mut LeanObject,
    mut v_a_6326_: *mut LeanObject,
    mut v_a_6327_: *mut LeanObject,
    mut v_a_6328_: *mut LeanObject,
    mut v_a_6329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6332_: *mut LeanObject,
    mut v_jobs_6333_: *mut LeanObject,
    mut v_a_6334_: *mut LeanObject,
    mut v_a_6335_: *mut LeanObject,
    mut v_a_6336_: *mut LeanObject,
    mut v_a_6337_: *mut LeanObject,
    mut v_a_6338_: *mut LeanObject,
    mut v_a_6339_: *mut LeanObject,
    mut v_a_6340_: *mut LeanObject,
    mut v_a_6341_: *mut LeanObject,
    mut v_a_6342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6343_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6341_);
    lean_dec_ref(v_a_6340_);
    lean_dec(v_a_6339_);
    lean_dec_ref(v_a_6338_);
    lean_dec(v_a_6337_);
    lean_dec_ref(v_a_6336_);
    lean_dec(v_a_6335_);
    lean_dec_ref(v_a_6334_);
    return v_res_6343_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(
    mut v_jobs_6344_: *mut LeanObject,
    mut v_a_6345_: *mut LeanObject,
    mut v_a_6346_: *mut LeanObject,
    mut v_a_6347_: *mut LeanObject,
    mut v_a_6348_: *mut LeanObject,
    mut v_a_6349_: *mut LeanObject,
    mut v_a_6350_: *mut LeanObject,
    mut v_a_6351_: *mut LeanObject,
    mut v_a_6352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut v_a_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6378_: u8 = 0;
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6354_ = lean_box(0);
                v___x_6355_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_6344_, v___x_6354_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_, v_a_6351_, v_a_6352_);
                if lean_obj_tag(v___x_6355_) == 0 {
                    v_a_6356_ = lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6374_ = (!lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6374_ == 0 {
                        v___x_6358_ = v___x_6355_;
                        v_isShared_6359_ = v_isSharedCheck_6374_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6356_);
                        lean_dec(v___x_6355_);
                        v___x_6358_ = lean_box(0);
                        v_isShared_6359_ = v_isSharedCheck_6374_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6375_ = lean_ctor_get(v___x_6355_, 0);
                    v_isSharedCheck_6382_ = (!lean_is_exclusive(v___x_6355_)) as u8;
                    if v_isSharedCheck_6382_ == 0 {
                        v___x_6377_ = v___x_6355_;
                        v_isShared_6378_ = v_isSharedCheck_6382_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6375_);
                        lean_dec(v___x_6355_);
                        v___x_6377_ = lean_box(0);
                        v_isShared_6378_ = v_isSharedCheck_6382_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6360_ = l_List_unzipTR___redArg(v_a_6356_);
                v_fst_6361_ = lean_ctor_get(v___x_6360_, 0);
                v_snd_6362_ = lean_ctor_get(v___x_6360_, 1);
                v_isSharedCheck_6373_ = (!lean_is_exclusive(v___x_6360_)) as u8;
                if v_isSharedCheck_6373_ == 0 {
                    v___x_6364_ = v___x_6360_;
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_6362_);
                    lean_inc(v_fst_6361_);
                    lean_dec(v___x_6360_);
                    v___x_6364_ = lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6366_ = lean_alloc_closure(
                    l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_6366_, 0, v_fst_6361_);
                if v_isShared_6365_ == 0 {
                    lean_ctor_set(v___x_6364_, 0, v___x_6366_);
                    v___x_6368_ = v___x_6364_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6372_, 0, v___x_6366_);
                    lean_ctor_set(v_reuseFailAlloc_6372_, 1, v_snd_6362_);
                    v___x_6368_ = v_reuseFailAlloc_6372_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6359_ == 0 {
                    lean_ctor_set(v___x_6358_, 0, v___x_6368_);
                    v___x_6370_ = v___x_6358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6371_, 0, v___x_6368_);
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
                    v_reuseFailAlloc_6381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_a_6375_);
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
    mut v_jobs_6383_: *mut LeanObject,
    mut v_a_6384_: *mut LeanObject,
    mut v_a_6385_: *mut LeanObject,
    mut v_a_6386_: *mut LeanObject,
    mut v_a_6387_: *mut LeanObject,
    mut v_a_6388_: *mut LeanObject,
    mut v_a_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6393_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6391_);
    lean_dec_ref(v_a_6390_);
    lean_dec(v_a_6389_);
    lean_dec_ref(v_a_6388_);
    lean_dec(v_a_6387_);
    lean_dec_ref(v_a_6386_);
    lean_dec(v_a_6385_);
    lean_dec_ref(v_a_6384_);
    return v_res_6393_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(
    mut v_00_u03b1_6394_: *mut LeanObject,
    mut v_jobs_6395_: *mut LeanObject,
    mut v_a_6396_: *mut LeanObject,
    mut v_a_6397_: *mut LeanObject,
    mut v_a_6398_: *mut LeanObject,
    mut v_a_6399_: *mut LeanObject,
    mut v_a_6400_: *mut LeanObject,
    mut v_a_6401_: *mut LeanObject,
    mut v_a_6402_: *mut LeanObject,
    mut v_a_6403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6406_: *mut LeanObject,
    mut v_jobs_6407_: *mut LeanObject,
    mut v_a_6408_: *mut LeanObject,
    mut v_a_6409_: *mut LeanObject,
    mut v_a_6410_: *mut LeanObject,
    mut v_a_6411_: *mut LeanObject,
    mut v_a_6412_: *mut LeanObject,
    mut v_a_6413_: *mut LeanObject,
    mut v_a_6414_: *mut LeanObject,
    mut v_a_6415_: *mut LeanObject,
    mut v_a_6416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6417_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6415_);
    lean_dec_ref(v_a_6414_);
    lean_dec(v_a_6413_);
    lean_dec_ref(v_a_6412_);
    lean_dec(v_a_6411_);
    lean_dec_ref(v_a_6410_);
    lean_dec(v_a_6409_);
    lean_dec_ref(v_a_6408_);
    return v_res_6417_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(
    mut v_jobs_6418_: *mut LeanObject,
    mut v_a_6419_: *mut LeanObject,
    mut v_a_6420_: *mut LeanObject,
    mut v_a_6421_: *mut LeanObject,
    mut v_a_6422_: *mut LeanObject,
    mut v_a_6423_: *mut LeanObject,
    mut v_a_6424_: *mut LeanObject,
    mut v_a_6425_: *mut LeanObject,
    mut v_a_6426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6432_: u8 = 0;
    let mut v_snd_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6437_: u8 = 0;
    let mut v_a_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6441_: u8 = 0;
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6444_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_6428_) == 0 {
                    v_a_6429_ = lean_ctor_get(v___x_6428_, 0);
                    v_isSharedCheck_6437_ = (!lean_is_exclusive(v___x_6428_)) as u8;
                    if v_isSharedCheck_6437_ == 0 {
                        v___x_6431_ = v___x_6428_;
                        v_isShared_6432_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6429_);
                        lean_dec(v___x_6428_);
                        v___x_6431_ = lean_box(0);
                        v_isShared_6432_ = v_isSharedCheck_6437_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6438_ = lean_ctor_get(v___x_6428_, 0);
                    v_isSharedCheck_6445_ = (!lean_is_exclusive(v___x_6428_)) as u8;
                    if v_isSharedCheck_6445_ == 0 {
                        v___x_6440_ = v___x_6428_;
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6438_);
                        lean_dec(v___x_6428_);
                        v___x_6440_ = lean_box(0);
                        v_isShared_6441_ = v_isSharedCheck_6445_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6433_ = lean_ctor_get(v_a_6429_, 1);
                lean_inc(v_snd_6433_);
                lean_dec(v_a_6429_);
                if v_isShared_6432_ == 0 {
                    lean_ctor_set(v___x_6431_, 0, v_snd_6433_);
                    v___x_6435_ = v___x_6431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_snd_6433_);
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
                    v_reuseFailAlloc_6444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
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
    mut v_jobs_6446_: *mut LeanObject,
    mut v_a_6447_: *mut LeanObject,
    mut v_a_6448_: *mut LeanObject,
    mut v_a_6449_: *mut LeanObject,
    mut v_a_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
    mut v_a_6452_: *mut LeanObject,
    mut v_a_6453_: *mut LeanObject,
    mut v_a_6454_: *mut LeanObject,
    mut v_a_6455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6456_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6454_);
    lean_dec_ref(v_a_6453_);
    lean_dec(v_a_6452_);
    lean_dec_ref(v_a_6451_);
    lean_dec(v_a_6450_);
    lean_dec_ref(v_a_6449_);
    lean_dec(v_a_6448_);
    lean_dec_ref(v_a_6447_);
    return v_res_6456_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parIterGreedy(
    mut v_00_u03b1_6457_: *mut LeanObject,
    mut v_jobs_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
    mut v_a_6460_: *mut LeanObject,
    mut v_a_6461_: *mut LeanObject,
    mut v_a_6462_: *mut LeanObject,
    mut v_a_6463_: *mut LeanObject,
    mut v_a_6464_: *mut LeanObject,
    mut v_a_6465_: *mut LeanObject,
    mut v_a_6466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6469_: *mut LeanObject,
    mut v_jobs_6470_: *mut LeanObject,
    mut v_a_6471_: *mut LeanObject,
    mut v_a_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
    mut v_a_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
    mut v_a_6476_: *mut LeanObject,
    mut v_a_6477_: *mut LeanObject,
    mut v_a_6478_: *mut LeanObject,
    mut v_a_6479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6480_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6478_);
    lean_dec_ref(v_a_6477_);
    lean_dec(v_a_6476_);
    lean_dec_ref(v_a_6475_);
    lean_dec(v_a_6474_);
    lean_dec_ref(v_a_6473_);
    lean_dec(v_a_6472_);
    lean_dec_ref(v_a_6471_);
    return v_res_6480_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(
    mut v_as_x27_6481_: *mut LeanObject,
    mut v_b_6482_: *mut LeanObject,
    mut v___y_6483_: *mut LeanObject,
    mut v___y_6484_: *mut LeanObject,
    mut v___y_6485_: *mut LeanObject,
    mut v___y_6486_: *mut LeanObject,
    mut v___y_6487_: *mut LeanObject,
    mut v___y_6488_: *mut LeanObject,
    mut v___y_6489_: *mut LeanObject,
    mut v___y_6490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6499_: u8 = 0;
    let mut v___y_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: u8 = 0;
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6510_: u8 = 0;
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6514_: u8 = 0;
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: u8 = 0;
    let mut v___x_2645__overap_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut v_a_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut v_a_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6543_: u8 = 0;
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_6481_) == 0 {
                    v___x_6492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6492_, 0, v_b_6482_);
                    return v___x_6492_;
                } else {
                    v_head_6493_ = lean_ctor_get(v_as_x27_6481_, 0);
                    v_tail_6494_ = lean_ctor_get(v_as_x27_6481_, 1);
                    v___x_6495_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6484_,
                        v___y_6486_,
                        v___y_6488_,
                        v___y_6490_,
                    );
                    if lean_obj_tag(v___x_6495_) == 0 {
                        v_a_6496_ = lean_ctor_get(v___x_6495_, 0);
                        v_isSharedCheck_6539_ = (!lean_is_exclusive(v___x_6495_)) as u8;
                        if v_isSharedCheck_6539_ == 0 {
                            v___x_6498_ = v___x_6495_;
                            v_isShared_6499_ = v_isSharedCheck_6539_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6496_);
                            lean_dec(v___x_6495_);
                            v___x_6498_ = lean_box(0);
                            v_isShared_6499_ = v_isSharedCheck_6539_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_6482_);
                        v_a_6540_ = lean_ctor_get(v___x_6495_, 0);
                        v_isSharedCheck_6547_ = (!lean_is_exclusive(v___x_6495_)) as u8;
                        if v_isSharedCheck_6547_ == 0 {
                            v___x_6542_ = v___x_6495_;
                            v_isShared_6543_ = v_isSharedCheck_6547_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6540_);
                            lean_dec(v___x_6495_);
                            v___x_6542_ = lean_box(0);
                            v_isShared_6543_ = v_isSharedCheck_6547_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_head_6493_);
                v___x_2645__overap_6522_ = lean_task_get_own(v_head_6493_);
                lean_inc(v___y_6490_);
                lean_inc_ref(v___y_6489_);
                lean_inc(v___y_6488_);
                lean_inc_ref(v___y_6487_);
                lean_inc(v___y_6486_);
                lean_inc_ref(v___y_6485_);
                lean_inc(v___y_6484_);
                lean_inc_ref(v___y_6483_);
                v___x_6523_ = lean_apply_9(
                    v___x_2645__overap_6522_,
                    v___y_6483_,
                    v___y_6484_,
                    v___y_6485_,
                    v___y_6486_,
                    v___y_6487_,
                    v___y_6488_,
                    v___y_6489_,
                    v___y_6490_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6523_) == 0 {
                    v_a_6524_ = lean_ctor_get(v___x_6523_, 0);
                    lean_inc(v_a_6524_);
                    lean_dec_ref_known(v___x_6523_, 1);
                    v___x_6525_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6484_,
                        v___y_6486_,
                        v___y_6488_,
                        v___y_6490_,
                    );
                    if lean_obj_tag(v___x_6525_) == 0 {
                        lean_del_object(v___x_6498_);
                        lean_dec(v_a_6496_);
                        v_a_6526_ = lean_ctor_get(v___x_6525_, 0);
                        v_isSharedCheck_6536_ = (!lean_is_exclusive(v___x_6525_)) as u8;
                        if v_isSharedCheck_6536_ == 0 {
                            v___x_6528_ = v___x_6525_;
                            v_isShared_6529_ = v_isSharedCheck_6536_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6526_);
                            lean_dec(v___x_6525_);
                            v___x_6528_ = lean_box(0);
                            v_isShared_6529_ = v_isSharedCheck_6536_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6524_);
                        v_a_6537_ = lean_ctor_get(v___x_6525_, 0);
                        lean_inc(v_a_6537_);
                        lean_dec_ref_known(v___x_6525_, 1);
                        v_a_6519_ = v_a_6537_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_6538_ = lean_ctor_get(v___x_6523_, 0);
                    lean_inc(v_a_6538_);
                    lean_dec_ref_known(v___x_6523_, 1);
                    v_a_6519_ = v_a_6538_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                if v___y_6502_ == 0 {
                    lean_del_object(v___x_6498_);
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
                    if lean_obj_tag(v___x_6503_) == 0 {
                        lean_dec_ref_known(v___x_6503_, 1);
                        v___x_6504_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6504_, 0, v___y_6501_);
                        v___x_6505_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_6505_, 0, v___x_6504_);
                        lean_ctor_set(v___x_6505_, 1, v_b_6482_);
                        v_as_x27_6481_ = v_tail_6494_;
                        v_b_6482_ = v___x_6505_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6501_);
                        lean_dec(v_b_6482_);
                        v_a_6507_ = lean_ctor_get(v___x_6503_, 0);
                        v_isSharedCheck_6514_ = (!lean_is_exclusive(v___x_6503_)) as u8;
                        if v_isSharedCheck_6514_ == 0 {
                            v___x_6509_ = v___x_6503_;
                            v_isShared_6510_ = v_isSharedCheck_6514_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6507_);
                            lean_dec(v___x_6503_);
                            v___x_6509_ = lean_box(0);
                            v_isShared_6510_ = v_isSharedCheck_6514_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6496_);
                    lean_dec(v_b_6482_);
                    if v_isShared_6499_ == 0 {
                        lean_ctor_set_tag(v___x_6498_, 1);
                        lean_ctor_set(v___x_6498_, 0, v___y_6501_);
                        v___x_6516_ = v___x_6498_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6517_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6517_, 0, v___y_6501_);
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
                    v_reuseFailAlloc_6513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
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
                    lean_inc_ref(v_a_6519_);
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
                v___x_6530_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6530_, 0, v_a_6524_);
                lean_ctor_set(v___x_6530_, 1, v_a_6526_);
                if v_isShared_6529_ == 0 {
                    lean_ctor_set_tag(v___x_6528_, 1);
                    lean_ctor_set(v___x_6528_, 0, v___x_6530_);
                    v___x_6532_ = v___x_6528_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6530_);
                    v___x_6532_ = v_reuseFailAlloc_6535_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6533_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6533_, 0, v___x_6532_);
                lean_ctor_set(v___x_6533_, 1, v_b_6482_);
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
                    v_reuseFailAlloc_6546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6546_, 0, v_a_6540_);
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
    mut v_as_x27_6548_: *mut LeanObject,
    mut v_b_6549_: *mut LeanObject,
    mut v___y_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6559_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6557_);
    lean_dec_ref(v___y_6556_);
    lean_dec(v___y_6555_);
    lean_dec_ref(v___y_6554_);
    lean_dec(v___y_6553_);
    lean_dec_ref(v___y_6552_);
    lean_dec(v___y_6551_);
    lean_dec_ref(v___y_6550_);
    lean_dec(v_as_x27_6548_);
    return v_res_6559_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(
    mut v_x_6560_: *mut LeanObject,
    mut v_x_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6577_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v_isSharedCheck_6592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6560_) == 0 {
                    v___x_6571_ = l_List_reverse___redArg(v_x_6561_);
                    v___x_6572_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6572_, 0, v___x_6571_);
                    return v___x_6572_;
                } else {
                    v_head_6573_ = lean_ctor_get(v_x_6560_, 0);
                    v_tail_6574_ = lean_ctor_get(v_x_6560_, 1);
                    v_isSharedCheck_6592_ = (!lean_is_exclusive(v_x_6560_)) as u8;
                    if v_isSharedCheck_6592_ == 0 {
                        v___x_6576_ = v_x_6560_;
                        v_isShared_6577_ = v_isSharedCheck_6592_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6574_);
                        lean_inc(v_head_6573_);
                        lean_dec(v_x_6560_);
                        v___x_6576_ = lean_box(0);
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
                if lean_obj_tag(v___x_6578_) == 0 {
                    v_a_6579_ = lean_ctor_get(v___x_6578_, 0);
                    lean_inc(v_a_6579_);
                    lean_dec_ref_known(v___x_6578_, 1);
                    if v_isShared_6577_ == 0 {
                        lean_ctor_set(v___x_6576_, 1, v_x_6561_);
                        lean_ctor_set(v___x_6576_, 0, v_a_6579_);
                        v___x_6581_ = v___x_6576_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6583_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_a_6579_);
                        lean_ctor_set(v_reuseFailAlloc_6583_, 1, v_x_6561_);
                        v___x_6581_ = v_reuseFailAlloc_6583_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6576_);
                    lean_dec(v_tail_6574_);
                    lean_dec(v_x_6561_);
                    v_a_6584_ = lean_ctor_get(v___x_6578_, 0);
                    v_isSharedCheck_6591_ = (!lean_is_exclusive(v___x_6578_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6578_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6584_);
                        lean_dec(v___x_6578_);
                        v___x_6586_ = lean_box(0);
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
                    v_reuseFailAlloc_6590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
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
    mut v_x_6593_: *mut LeanObject,
    mut v_x_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
    mut v___y_6600_: *mut LeanObject,
    mut v___y_6601_: *mut LeanObject,
    mut v___y_6602_: *mut LeanObject,
    mut v___y_6603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6604_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6602_);
    lean_dec_ref(v___y_6601_);
    lean_dec(v___y_6600_);
    lean_dec_ref(v___y_6599_);
    lean_dec(v___y_6598_);
    lean_dec_ref(v___y_6597_);
    lean_dec(v___y_6596_);
    lean_dec_ref(v___y_6595_);
    return v_res_6604_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par___redArg(
    mut v_jobs_6605_: *mut LeanObject,
    mut v_a_6606_: *mut LeanObject,
    mut v_a_6607_: *mut LeanObject,
    mut v_a_6608_: *mut LeanObject,
    mut v_a_6609_: *mut LeanObject,
    mut v_a_6610_: *mut LeanObject,
    mut v_a_6611_: *mut LeanObject,
    mut v_a_6612_: *mut LeanObject,
    mut v_a_6613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6629_: u8 = 0;
    let mut v_a_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6615_ = lean_st_ref_get(v_a_6607_);
                v___x_6616_ = lean_box(0);
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
                if lean_obj_tag(v___x_6617_) == 0 {
                    v_a_6618_ = lean_ctor_get(v___x_6617_, 0);
                    lean_inc(v_a_6618_);
                    lean_dec_ref_known(v___x_6617_, 1);
                    v___x_6619_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_6618_, v___x_6616_, v_a_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_);
                    lean_dec(v_a_6618_);
                    if lean_obj_tag(v___x_6619_) == 0 {
                        v_a_6620_ = lean_ctor_get(v___x_6619_, 0);
                        v_isSharedCheck_6629_ = (!lean_is_exclusive(v___x_6619_)) as u8;
                        if v_isSharedCheck_6629_ == 0 {
                            v___x_6622_ = v___x_6619_;
                            v_isShared_6623_ = v_isSharedCheck_6629_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6620_);
                            lean_dec(v___x_6619_);
                            v___x_6622_ = lean_box(0);
                            v_isShared_6623_ = v_isSharedCheck_6629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6615_);
                        return v___x_6619_;
                    }
                } else {
                    lean_dec(v___x_6615_);
                    v_a_6630_ = lean_ctor_get(v___x_6617_, 0);
                    v_isSharedCheck_6637_ = (!lean_is_exclusive(v___x_6617_)) as u8;
                    if v_isSharedCheck_6637_ == 0 {
                        v___x_6632_ = v___x_6617_;
                        v_isShared_6633_ = v_isSharedCheck_6637_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6630_);
                        lean_dec(v___x_6617_);
                        v___x_6632_ = lean_box(0);
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
                    lean_ctor_set(v___x_6622_, 0, v___x_6625_);
                    v___x_6627_ = v___x_6622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6628_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6628_, 0, v___x_6625_);
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
                    v_reuseFailAlloc_6636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6636_, 0, v_a_6630_);
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
    mut v_jobs_6638_: *mut LeanObject,
    mut v_a_6639_: *mut LeanObject,
    mut v_a_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
    mut v_a_6642_: *mut LeanObject,
    mut v_a_6643_: *mut LeanObject,
    mut v_a_6644_: *mut LeanObject,
    mut v_a_6645_: *mut LeanObject,
    mut v_a_6646_: *mut LeanObject,
    mut v_a_6647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6648_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6646_);
    lean_dec_ref(v_a_6645_);
    lean_dec(v_a_6644_);
    lean_dec_ref(v_a_6643_);
    lean_dec(v_a_6642_);
    lean_dec_ref(v_a_6641_);
    lean_dec(v_a_6640_);
    lean_dec_ref(v_a_6639_);
    return v_res_6648_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par(
    mut v_00_u03b1_6649_: *mut LeanObject,
    mut v_jobs_6650_: *mut LeanObject,
    mut v_a_6651_: *mut LeanObject,
    mut v_a_6652_: *mut LeanObject,
    mut v_a_6653_: *mut LeanObject,
    mut v_a_6654_: *mut LeanObject,
    mut v_a_6655_: *mut LeanObject,
    mut v_a_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
    mut v_a_6658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6661_: *mut LeanObject,
    mut v_jobs_6662_: *mut LeanObject,
    mut v_a_6663_: *mut LeanObject,
    mut v_a_6664_: *mut LeanObject,
    mut v_a_6665_: *mut LeanObject,
    mut v_a_6666_: *mut LeanObject,
    mut v_a_6667_: *mut LeanObject,
    mut v_a_6668_: *mut LeanObject,
    mut v_a_6669_: *mut LeanObject,
    mut v_a_6670_: *mut LeanObject,
    mut v_a_6671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6672_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6670_);
    lean_dec_ref(v_a_6669_);
    lean_dec(v_a_6668_);
    lean_dec_ref(v_a_6667_);
    lean_dec(v_a_6666_);
    lean_dec_ref(v_a_6665_);
    lean_dec(v_a_6664_);
    lean_dec_ref(v_a_6663_);
    return v_res_6672_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(
    mut v_00_u03b1_6673_: *mut LeanObject,
    mut v_x_6674_: *mut LeanObject,
    mut v_x_6675_: *mut LeanObject,
    mut v___y_6676_: *mut LeanObject,
    mut v___y_6677_: *mut LeanObject,
    mut v___y_6678_: *mut LeanObject,
    mut v___y_6679_: *mut LeanObject,
    mut v___y_6680_: *mut LeanObject,
    mut v___y_6681_: *mut LeanObject,
    mut v___y_6682_: *mut LeanObject,
    mut v___y_6683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6686_: *mut LeanObject,
    mut v_x_6687_: *mut LeanObject,
    mut v_x_6688_: *mut LeanObject,
    mut v___y_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
    mut v___y_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
    mut v___y_6695_: *mut LeanObject,
    mut v___y_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6698_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6696_);
    lean_dec_ref(v___y_6695_);
    lean_dec(v___y_6694_);
    lean_dec_ref(v___y_6693_);
    lean_dec(v___y_6692_);
    lean_dec_ref(v___y_6691_);
    lean_dec(v___y_6690_);
    lean_dec_ref(v___y_6689_);
    return v_res_6698_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(
    mut v_00_u03b1_6699_: *mut LeanObject,
    mut v_as_6700_: *mut LeanObject,
    mut v_as_x27_6701_: *mut LeanObject,
    mut v_b_6702_: *mut LeanObject,
    mut v_a_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
    mut v___y_6706_: *mut LeanObject,
    mut v___y_6707_: *mut LeanObject,
    mut v___y_6708_: *mut LeanObject,
    mut v___y_6709_: *mut LeanObject,
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6714_: *mut LeanObject,
    mut v_as_6715_: *mut LeanObject,
    mut v_as_x27_6716_: *mut LeanObject,
    mut v_b_6717_: *mut LeanObject,
    mut v_a_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
    mut v___y_6724_: *mut LeanObject,
    mut v___y_6725_: *mut LeanObject,
    mut v___y_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6728_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6726_);
    lean_dec_ref(v___y_6725_);
    lean_dec(v___y_6724_);
    lean_dec_ref(v___y_6723_);
    lean_dec(v___y_6722_);
    lean_dec_ref(v___y_6721_);
    lean_dec(v___y_6720_);
    lean_dec_ref(v___y_6719_);
    lean_dec(v_as_x27_6716_);
    lean_dec(v_as_6715_);
    return v_res_6728_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(
    mut v_as_x27_6729_: *mut LeanObject,
    mut v_b_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
    mut v___y_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330__overap_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___y_6756_: u8 = 0;
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: u8 = 0;
    let mut v___x_6773_: u8 = 0;
    let mut v_isSharedCheck_6774_: u8 = 0;
    let mut v_a_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6778_: u8 = 0;
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_6729_) == 0 {
                    v___x_6740_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6740_, 0, v_b_6730_);
                    return v___x_6740_;
                } else {
                    v_head_6741_ = lean_ctor_get(v_as_x27_6729_, 0);
                    v_tail_6742_ = lean_ctor_get(v_as_x27_6729_, 1);
                    v___x_6743_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6732_,
                        v___y_6734_,
                        v___y_6736_,
                        v___y_6738_,
                    );
                    if lean_obj_tag(v___x_6743_) == 0 {
                        v_a_6744_ = lean_ctor_get(v___x_6743_, 0);
                        lean_inc(v_a_6744_);
                        lean_dec_ref_known(v___x_6743_, 1);
                        lean_inc(v_head_6741_);
                        v___x_2330__overap_6745_ = lean_task_get_own(v_head_6741_);
                        lean_inc(v___y_6738_);
                        lean_inc_ref(v___y_6737_);
                        lean_inc(v___y_6736_);
                        lean_inc_ref(v___y_6735_);
                        lean_inc(v___y_6734_);
                        lean_inc_ref(v___y_6733_);
                        lean_inc(v___y_6732_);
                        lean_inc_ref(v___y_6731_);
                        v___x_6746_ = lean_apply_9(
                            v___x_2330__overap_6745_,
                            v___y_6731_,
                            v___y_6732_,
                            v___y_6733_,
                            v___y_6734_,
                            v___y_6735_,
                            v___y_6736_,
                            v___y_6737_,
                            v___y_6738_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_6746_) == 0 {
                            lean_dec(v_a_6744_);
                            v_a_6747_ = lean_ctor_get(v___x_6746_, 0);
                            lean_inc(v_a_6747_);
                            lean_dec_ref_known(v___x_6746_, 1);
                            v___x_6748_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6748_, 0, v_a_6747_);
                            v___x_6749_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_6749_, 0, v___x_6748_);
                            lean_ctor_set(v___x_6749_, 1, v_b_6730_);
                            v_as_x27_6729_ = v_tail_6742_;
                            v_b_6730_ = v___x_6749_;
                            state = 0;
                            continue;
                        } else {
                            v_a_6751_ = lean_ctor_get(v___x_6746_, 0);
                            v_isSharedCheck_6774_ = (!lean_is_exclusive(v___x_6746_)) as u8;
                            if v_isSharedCheck_6774_ == 0 {
                                v___x_6753_ = v___x_6746_;
                                v_isShared_6754_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6751_);
                                lean_dec(v___x_6746_);
                                v___x_6753_ = lean_box(0);
                                v_isShared_6754_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_b_6730_);
                        v_a_6775_ = lean_ctor_get(v___x_6743_, 0);
                        v_isSharedCheck_6782_ = (!lean_is_exclusive(v___x_6743_)) as u8;
                        if v_isSharedCheck_6782_ == 0 {
                            v___x_6777_ = v___x_6743_;
                            v_isShared_6778_ = v_isSharedCheck_6782_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6775_);
                            lean_dec(v___x_6743_);
                            v___x_6777_ = lean_box(0);
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
                    lean_inc(v_a_6751_);
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
                    lean_del_object(v___x_6753_);
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
                    if lean_obj_tag(v___x_6757_) == 0 {
                        lean_dec_ref_known(v___x_6757_, 1);
                        v___x_6758_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6758_, 0, v_a_6751_);
                        v___x_6759_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_6759_, 0, v___x_6758_);
                        lean_ctor_set(v___x_6759_, 1, v_b_6730_);
                        v_as_x27_6729_ = v_tail_6742_;
                        v_b_6730_ = v___x_6759_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_6751_);
                        lean_dec(v_b_6730_);
                        v_a_6761_ = lean_ctor_get(v___x_6757_, 0);
                        v_isSharedCheck_6768_ = (!lean_is_exclusive(v___x_6757_)) as u8;
                        if v_isSharedCheck_6768_ == 0 {
                            v___x_6763_ = v___x_6757_;
                            v_isShared_6764_ = v_isSharedCheck_6768_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6761_);
                            lean_dec(v___x_6757_);
                            v___x_6763_ = lean_box(0);
                            v_isShared_6764_ = v_isSharedCheck_6768_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6744_);
                    lean_dec(v_b_6730_);
                    if v_isShared_6754_ == 0 {
                        v___x_6770_ = v___x_6753_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6771_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6751_);
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
                    v_reuseFailAlloc_6767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6761_);
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
                    v_reuseFailAlloc_6781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 0, v_a_6775_);
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
    mut v_as_x27_6783_: *mut LeanObject,
    mut v_b_6784_: *mut LeanObject,
    mut v___y_6785_: *mut LeanObject,
    mut v___y_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
    mut v___y_6789_: *mut LeanObject,
    mut v___y_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6794_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6792_);
    lean_dec_ref(v___y_6791_);
    lean_dec(v___y_6790_);
    lean_dec_ref(v___y_6789_);
    lean_dec(v___y_6788_);
    lean_dec_ref(v___y_6787_);
    lean_dec(v___y_6786_);
    lean_dec_ref(v___y_6785_);
    lean_dec(v_as_x27_6783_);
    return v_res_6794_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27___redArg(
    mut v_jobs_6795_: *mut LeanObject,
    mut v_a_6796_: *mut LeanObject,
    mut v_a_6797_: *mut LeanObject,
    mut v_a_6798_: *mut LeanObject,
    mut v_a_6799_: *mut LeanObject,
    mut v_a_6800_: *mut LeanObject,
    mut v_a_6801_: *mut LeanObject,
    mut v_a_6802_: *mut LeanObject,
    mut v_a_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6813_: u8 = 0;
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6819_: u8 = 0;
    let mut v_a_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6823_: u8 = 0;
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6805_ = lean_st_ref_get(v_a_6797_);
                v___x_6806_ = lean_box(0);
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
                if lean_obj_tag(v___x_6807_) == 0 {
                    v_a_6808_ = lean_ctor_get(v___x_6807_, 0);
                    lean_inc(v_a_6808_);
                    lean_dec_ref_known(v___x_6807_, 1);
                    v___x_6809_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_a_6808_, v___x_6806_, v_a_6796_, v_a_6797_, v_a_6798_, v_a_6799_, v_a_6800_, v_a_6801_, v_a_6802_, v_a_6803_);
                    lean_dec(v_a_6808_);
                    if lean_obj_tag(v___x_6809_) == 0 {
                        v_a_6810_ = lean_ctor_get(v___x_6809_, 0);
                        v_isSharedCheck_6819_ = (!lean_is_exclusive(v___x_6809_)) as u8;
                        if v_isSharedCheck_6819_ == 0 {
                            v___x_6812_ = v___x_6809_;
                            v_isShared_6813_ = v_isSharedCheck_6819_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6810_);
                            lean_dec(v___x_6809_);
                            v___x_6812_ = lean_box(0);
                            v_isShared_6813_ = v_isSharedCheck_6819_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6805_);
                        return v___x_6809_;
                    }
                } else {
                    lean_dec(v___x_6805_);
                    v_a_6820_ = lean_ctor_get(v___x_6807_, 0);
                    v_isSharedCheck_6827_ = (!lean_is_exclusive(v___x_6807_)) as u8;
                    if v_isSharedCheck_6827_ == 0 {
                        v___x_6822_ = v___x_6807_;
                        v_isShared_6823_ = v_isSharedCheck_6827_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6820_);
                        lean_dec(v___x_6807_);
                        v___x_6822_ = lean_box(0);
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
                    lean_ctor_set(v___x_6812_, 0, v___x_6815_);
                    v___x_6817_ = v___x_6812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6818_, 0, v___x_6815_);
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
                    v_reuseFailAlloc_6826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_a_6820_);
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
    mut v_jobs_6828_: *mut LeanObject,
    mut v_a_6829_: *mut LeanObject,
    mut v_a_6830_: *mut LeanObject,
    mut v_a_6831_: *mut LeanObject,
    mut v_a_6832_: *mut LeanObject,
    mut v_a_6833_: *mut LeanObject,
    mut v_a_6834_: *mut LeanObject,
    mut v_a_6835_: *mut LeanObject,
    mut v_a_6836_: *mut LeanObject,
    mut v_a_6837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6838_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6836_);
    lean_dec_ref(v_a_6835_);
    lean_dec(v_a_6834_);
    lean_dec_ref(v_a_6833_);
    lean_dec(v_a_6832_);
    lean_dec_ref(v_a_6831_);
    lean_dec(v_a_6830_);
    lean_dec_ref(v_a_6829_);
    return v_res_6838_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_par_x27(
    mut v_00_u03b1_6839_: *mut LeanObject,
    mut v_jobs_6840_: *mut LeanObject,
    mut v_a_6841_: *mut LeanObject,
    mut v_a_6842_: *mut LeanObject,
    mut v_a_6843_: *mut LeanObject,
    mut v_a_6844_: *mut LeanObject,
    mut v_a_6845_: *mut LeanObject,
    mut v_a_6846_: *mut LeanObject,
    mut v_a_6847_: *mut LeanObject,
    mut v_a_6848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6851_: *mut LeanObject,
    mut v_jobs_6852_: *mut LeanObject,
    mut v_a_6853_: *mut LeanObject,
    mut v_a_6854_: *mut LeanObject,
    mut v_a_6855_: *mut LeanObject,
    mut v_a_6856_: *mut LeanObject,
    mut v_a_6857_: *mut LeanObject,
    mut v_a_6858_: *mut LeanObject,
    mut v_a_6859_: *mut LeanObject,
    mut v_a_6860_: *mut LeanObject,
    mut v_a_6861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6862_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6860_);
    lean_dec_ref(v_a_6859_);
    lean_dec(v_a_6858_);
    lean_dec_ref(v_a_6857_);
    lean_dec(v_a_6856_);
    lean_dec_ref(v_a_6855_);
    lean_dec(v_a_6854_);
    lean_dec_ref(v_a_6853_);
    return v_res_6862_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(
    mut v_00_u03b1_6863_: *mut LeanObject,
    mut v_as_6864_: *mut LeanObject,
    mut v_as_x27_6865_: *mut LeanObject,
    mut v_b_6866_: *mut LeanObject,
    mut v_a_6867_: *mut LeanObject,
    mut v___y_6868_: *mut LeanObject,
    mut v___y_6869_: *mut LeanObject,
    mut v___y_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6878_: *mut LeanObject,
    mut v_as_6879_: *mut LeanObject,
    mut v_as_x27_6880_: *mut LeanObject,
    mut v_b_6881_: *mut LeanObject,
    mut v_a_6882_: *mut LeanObject,
    mut v___y_6883_: *mut LeanObject,
    mut v___y_6884_: *mut LeanObject,
    mut v___y_6885_: *mut LeanObject,
    mut v___y_6886_: *mut LeanObject,
    mut v___y_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6892_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6890_);
    lean_dec_ref(v___y_6889_);
    lean_dec(v___y_6888_);
    lean_dec_ref(v___y_6887_);
    lean_dec(v___y_6886_);
    lean_dec_ref(v___y_6885_);
    lean_dec(v___y_6884_);
    lean_dec_ref(v___y_6883_);
    lean_dec(v_as_x27_6880_);
    lean_dec(v_as_6879_);
    return v_res_6892_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(
    mut v_a_6893_: *mut LeanObject,
    mut v___x_6894_: *mut LeanObject,
    mut v_____r_6895_: *mut LeanObject,
    mut v___y_6896_: *mut LeanObject,
    mut v___y_6897_: *mut LeanObject,
    mut v___y_6898_: *mut LeanObject,
    mut v___y_6899_: *mut LeanObject,
    mut v___y_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    v___x_6905_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6905_, 0, v_a_6893_);
    v___x_6906_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6906_, 0, v___x_6905_);
    lean_ctor_set(v___x_6906_, 1, v___x_6894_);
    v___x_6907_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6907_, 0, v___x_6906_);
    v___x_6908_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6908_, 0, v___x_6907_);
    return v___x_6908_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(
    mut v_a_6909_: *mut LeanObject,
    mut v___x_6910_: *mut LeanObject,
    mut v_____r_6911_: *mut LeanObject,
    mut v___y_6912_: *mut LeanObject,
    mut v___y_6913_: *mut LeanObject,
    mut v___y_6914_: *mut LeanObject,
    mut v___y_6915_: *mut LeanObject,
    mut v___y_6916_: *mut LeanObject,
    mut v___y_6917_: *mut LeanObject,
    mut v___y_6918_: *mut LeanObject,
    mut v___y_6919_: *mut LeanObject,
    mut v___y_6920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6921_: *mut LeanObject = core::ptr::null_mut();
    v_res_6921_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6909_, v___x_6910_, v_____r_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_);
    lean_dec(v___y_6919_);
    lean_dec_ref(v___y_6918_);
    lean_dec(v___y_6917_);
    lean_dec_ref(v___y_6916_);
    lean_dec(v___y_6915_);
    lean_dec_ref(v___y_6914_);
    lean_dec(v___y_6913_);
    lean_dec_ref(v___y_6912_);
    return v_res_6921_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(
    mut v_cancel_6922_: u8,
    mut v_fst_6923_: *mut LeanObject,
    mut v_a_6924_: *mut LeanObject,
    mut v_b_6925_: *mut LeanObject,
    mut v___y_6926_: *mut LeanObject,
    mut v___y_6927_: *mut LeanObject,
    mut v___y_6928_: *mut LeanObject,
    mut v___y_6929_: *mut LeanObject,
    mut v___y_6930_: *mut LeanObject,
    mut v___y_6931_: *mut LeanObject,
    mut v___y_6932_: *mut LeanObject,
    mut v___y_6933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v_a_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6951_: u8 = 0;
    let mut v_a_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6972_: u8 = 0;
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6975_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6981_: u8 = 0;
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6985_: u8 = 0;
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: u8 = 0;
    let mut v___x_6990_: u8 = 0;
    let mut v_isSharedCheck_6991_: u8 = 0;
    let mut v_a_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6995_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6924_) == 0 {
                    lean_dec_ref(v_fst_6923_);
                    v___x_6935_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6935_, 0, v_b_6925_);
                    return v___x_6935_;
                } else {
                    lean_dec_ref(v_b_6925_);
                    v___x_6936_ = l_IO_waitAny_x27___redArg(v_a_6924_);
                    v_fst_6937_ = lean_ctor_get(v___x_6936_, 0);
                    lean_inc(v_fst_6937_);
                    v_snd_6938_ = lean_ctor_get(v___x_6936_, 1);
                    lean_inc(v_snd_6938_);
                    lean_dec_ref(v___x_6936_);
                    v___x_6960_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_6927_,
                        v___y_6929_,
                        v___y_6931_,
                        v___y_6933_,
                    );
                    if lean_obj_tag(v___x_6960_) == 0 {
                        v_a_6961_ = lean_ctor_get(v___x_6960_, 0);
                        lean_inc(v_a_6961_);
                        lean_dec_ref_known(v___x_6960_, 1);
                        v___x_6962_ = lean_box(0);
                        lean_inc(v___y_6933_);
                        lean_inc_ref(v___y_6932_);
                        lean_inc(v___y_6931_);
                        lean_inc_ref(v___y_6930_);
                        lean_inc(v___y_6929_);
                        lean_inc_ref(v___y_6928_);
                        lean_inc(v___y_6927_);
                        lean_inc_ref(v___y_6926_);
                        v___x_6963_ = lean_apply_9(
                            v_fst_6937_,
                            v___y_6926_,
                            v___y_6927_,
                            v___y_6928_,
                            v___y_6929_,
                            v___y_6930_,
                            v___y_6931_,
                            v___y_6932_,
                            v___y_6933_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_6963_) == 0 {
                            lean_dec(v_a_6961_);
                            if v_cancel_6922_ == 0 {
                                v_a_6964_ = lean_ctor_get(v___x_6963_, 0);
                                lean_inc(v_a_6964_);
                                lean_dec_ref_known(v___x_6963_, 1);
                                v___x_6965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6964_, v___x_6962_, v___x_6962_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_);
                                v___y_6940_ = v___x_6965_;
                                state = 1;
                                continue;
                            } else {
                                v_a_6966_ = lean_ctor_get(v___x_6963_, 0);
                                lean_inc(v_a_6966_);
                                lean_dec_ref_known(v___x_6963_, 1);
                                lean_inc_ref(v_fst_6923_);
                                v___x_6967_ = lean_apply_1(v_fst_6923_, lean_box(0));
                                v___x_6968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_6966_, v___x_6962_, v___x_6967_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_);
                                v___y_6940_ = v___x_6968_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6969_ = lean_ctor_get(v___x_6963_, 0);
                            v_isSharedCheck_6991_ = (!lean_is_exclusive(v___x_6963_)) as u8;
                            if v_isSharedCheck_6991_ == 0 {
                                v___x_6971_ = v___x_6963_;
                                v_isShared_6972_ = v_isSharedCheck_6991_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6969_);
                                lean_dec(v___x_6963_);
                                v___x_6971_ = lean_box(0);
                                v_isShared_6972_ = v_isSharedCheck_6991_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_6938_);
                        lean_dec(v_fst_6937_);
                        lean_dec_ref(v_fst_6923_);
                        v_a_6992_ = lean_ctor_get(v___x_6960_, 0);
                        v_isSharedCheck_6999_ = (!lean_is_exclusive(v___x_6960_)) as u8;
                        if v_isSharedCheck_6999_ == 0 {
                            v___x_6994_ = v___x_6960_;
                            v_isShared_6995_ = v_isSharedCheck_6999_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_6992_);
                            lean_dec(v___x_6960_);
                            v___x_6994_ = lean_box(0);
                            v_isShared_6995_ = v_isSharedCheck_6999_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_6940_) == 0 {
                    v_a_6941_ = lean_ctor_get(v___y_6940_, 0);
                    v_isSharedCheck_6951_ = (!lean_is_exclusive(v___y_6940_)) as u8;
                    if v_isSharedCheck_6951_ == 0 {
                        v___x_6943_ = v___y_6940_;
                        v_isShared_6944_ = v_isSharedCheck_6951_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6941_);
                        lean_dec(v___y_6940_);
                        v___x_6943_ = lean_box(0);
                        v_isShared_6944_ = v_isSharedCheck_6951_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_6938_);
                    lean_dec_ref(v_fst_6923_);
                    v_a_6952_ = lean_ctor_get(v___y_6940_, 0);
                    v_isSharedCheck_6959_ = (!lean_is_exclusive(v___y_6940_)) as u8;
                    if v_isSharedCheck_6959_ == 0 {
                        v___x_6954_ = v___y_6940_;
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6952_);
                        lean_dec(v___y_6940_);
                        v___x_6954_ = lean_box(0);
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6941_) == 0 {
                    lean_dec(v_snd_6938_);
                    lean_dec_ref(v_fst_6923_);
                    v_a_6945_ = lean_ctor_get(v_a_6941_, 0);
                    lean_inc(v_a_6945_);
                    lean_dec_ref_known(v_a_6941_, 1);
                    if v_isShared_6944_ == 0 {
                        lean_ctor_set(v___x_6943_, 0, v_a_6945_);
                        v___x_6947_ = v___x_6943_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6948_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_a_6945_);
                        v___x_6947_ = v_reuseFailAlloc_6948_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6943_);
                    v_a_6949_ = lean_ctor_get(v_a_6941_, 0);
                    lean_inc(v_a_6949_);
                    lean_dec_ref_known(v_a_6941_, 1);
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
                    v_reuseFailAlloc_6958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
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
                    lean_inc(v_a_6969_);
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
                    lean_del_object(v___x_6971_);
                    lean_dec(v_a_6969_);
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
                    if lean_obj_tag(v___x_6976_) == 0 {
                        lean_dec_ref_known(v___x_6976_, 1);
                        v_a_6924_ = v_snd_6938_;
                        v_b_6925_ = v___x_6973_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_snd_6938_);
                        lean_dec_ref(v_fst_6923_);
                        v_a_6978_ = lean_ctor_get(v___x_6976_, 0);
                        v_isSharedCheck_6985_ = (!lean_is_exclusive(v___x_6976_)) as u8;
                        if v_isSharedCheck_6985_ == 0 {
                            v___x_6980_ = v___x_6976_;
                            v_isShared_6981_ = v_isSharedCheck_6985_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6978_);
                            lean_dec(v___x_6976_);
                            v___x_6980_ = lean_box(0);
                            v_isShared_6981_ = v_isSharedCheck_6985_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6961_);
                    lean_dec(v_snd_6938_);
                    lean_dec_ref(v_fst_6923_);
                    if v_isShared_6972_ == 0 {
                        v___x_6987_ = v___x_6971_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6988_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6988_, 0, v_a_6969_);
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
                    v_reuseFailAlloc_6984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_a_6978_);
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
                    v_reuseFailAlloc_6998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6998_, 0, v_a_6992_);
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
    mut v_cancel_7000_: *mut LeanObject,
    mut v_fst_7001_: *mut LeanObject,
    mut v_a_7002_: *mut LeanObject,
    mut v_b_7003_: *mut LeanObject,
    mut v___y_7004_: *mut LeanObject,
    mut v___y_7005_: *mut LeanObject,
    mut v___y_7006_: *mut LeanObject,
    mut v___y_7007_: *mut LeanObject,
    mut v___y_7008_: *mut LeanObject,
    mut v___y_7009_: *mut LeanObject,
    mut v___y_7010_: *mut LeanObject,
    mut v___y_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_7013_: u8 = 0;
    let mut v_res_7014_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7013_ = (lean_unbox(v_cancel_7000_) as u8);
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
    lean_dec(v___y_7011_);
    lean_dec_ref(v___y_7010_);
    lean_dec(v___y_7009_);
    lean_dec_ref(v___y_7008_);
    lean_dec(v___y_7007_);
    lean_dec_ref(v___y_7006_);
    lean_dec(v___y_7005_);
    lean_dec_ref(v___y_7004_);
    return v_res_7014_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(
    mut v_msg_7015_: *mut LeanObject,
    mut v___y_7016_: *mut LeanObject,
    mut v___y_7017_: *mut LeanObject,
    mut v___y_7018_: *mut LeanObject,
    mut v___y_7019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7026_: u8 = 0;
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7021_ = lean_ctor_get(v___y_7018_, 5);
                v___x_7022_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_);
                v_a_7023_ = lean_ctor_get(v___x_7022_, 0);
                v_isSharedCheck_7031_ = (!lean_is_exclusive(v___x_7022_)) as u8;
                if v_isSharedCheck_7031_ == 0 {
                    v___x_7025_ = v___x_7022_;
                    v_isShared_7026_ = v_isSharedCheck_7031_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7023_);
                    lean_dec(v___x_7022_);
                    v___x_7025_ = lean_box(0);
                    v_isShared_7026_ = v_isSharedCheck_7031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_7021_);
                v___x_7027_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7027_, 0, v_ref_7021_);
                lean_ctor_set(v___x_7027_, 1, v_a_7023_);
                if v_isShared_7026_ == 0 {
                    lean_ctor_set_tag(v___x_7025_, 1);
                    lean_ctor_set(v___x_7025_, 0, v___x_7027_);
                    v___x_7029_ = v___x_7025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7030_, 0, v___x_7027_);
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
    mut v_msg_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
    mut v___y_7034_: *mut LeanObject,
    mut v___y_7035_: *mut LeanObject,
    mut v___y_7036_: *mut LeanObject,
    mut v___y_7037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7038_: *mut LeanObject = core::ptr::null_mut();
    v_res_7038_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(
        v_msg_7032_,
        v___y_7033_,
        v___y_7034_,
        v___y_7035_,
        v___y_7036_,
    );
    lean_dec(v___y_7036_);
    lean_dec_ref(v___y_7035_);
    lean_dec(v___y_7034_);
    lean_dec_ref(v___y_7033_);
    return v_res_7038_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst___redArg(
    mut v_jobs_7039_: *mut LeanObject,
    mut v_cancel_7040_: u8,
    mut v_a_7041_: *mut LeanObject,
    mut v_a_7042_: *mut LeanObject,
    mut v_a_7043_: *mut LeanObject,
    mut v_a_7044_: *mut LeanObject,
    mut v_a_7045_: *mut LeanObject,
    mut v_a_7046_: *mut LeanObject,
    mut v_a_7047_: *mut LeanObject,
    mut v_a_7048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7059_: u8 = 0;
    let mut v_fst_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7067_: u8 = 0;
    let mut v_a_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7071_: u8 = 0;
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut v_a_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_7050_) == 0 {
                    v_a_7051_ = lean_ctor_get(v___x_7050_, 0);
                    lean_inc(v_a_7051_);
                    lean_dec_ref_known(v___x_7050_, 1);
                    v_fst_7052_ = lean_ctor_get(v_a_7051_, 0);
                    lean_inc(v_fst_7052_);
                    v_snd_7053_ = lean_ctor_get(v_a_7051_, 1);
                    lean_inc(v_snd_7053_);
                    lean_dec(v_a_7051_);
                    v___x_7054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0;
                    v___x_7055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_7040_, v_fst_7052_, v_snd_7053_, v___x_7054_, v_a_7041_, v_a_7042_, v_a_7043_, v_a_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
                    if lean_obj_tag(v___x_7055_) == 0 {
                        v_a_7056_ = lean_ctor_get(v___x_7055_, 0);
                        v_isSharedCheck_7067_ = (!lean_is_exclusive(v___x_7055_)) as u8;
                        if v_isSharedCheck_7067_ == 0 {
                            v___x_7058_ = v___x_7055_;
                            v_isShared_7059_ = v_isSharedCheck_7067_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7056_);
                            lean_dec(v___x_7055_);
                            v___x_7058_ = lean_box(0);
                            v_isShared_7059_ = v_isSharedCheck_7067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7068_ = lean_ctor_get(v___x_7055_, 0);
                        v_isSharedCheck_7075_ = (!lean_is_exclusive(v___x_7055_)) as u8;
                        if v_isSharedCheck_7075_ == 0 {
                            v___x_7070_ = v___x_7055_;
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7068_);
                            lean_dec(v___x_7055_);
                            v___x_7070_ = lean_box(0);
                            v_isShared_7071_ = v_isSharedCheck_7075_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_7076_ = lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7083_ = (!lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7083_ == 0 {
                        v___x_7078_ = v___x_7050_;
                        v_isShared_7079_ = v_isSharedCheck_7083_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7076_);
                        lean_dec(v___x_7050_);
                        v___x_7078_ = lean_box(0);
                        v_isShared_7079_ = v_isSharedCheck_7083_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7060_ = lean_ctor_get(v_a_7056_, 0);
                lean_inc(v_fst_7060_);
                lean_dec(v_a_7056_);
                if lean_obj_tag(v_fst_7060_) == 0 {
                    lean_del_object(v___x_7058_);
                    v___x_7061_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Core_CoreM_parFirst___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Core_CoreM_parFirst___redArg___closed__1_once
                        ),
                        _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1,
                    );
                    v___x_7062_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_7061_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
                    return v___x_7062_;
                } else {
                    v_val_7063_ = lean_ctor_get(v_fst_7060_, 0);
                    lean_inc(v_val_7063_);
                    lean_dec_ref_known(v_fst_7060_, 1);
                    if v_isShared_7059_ == 0 {
                        lean_ctor_set(v___x_7058_, 0, v_val_7063_);
                        v___x_7065_ = v___x_7058_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7066_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7066_, 0, v_val_7063_);
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
                    v_reuseFailAlloc_7074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_a_7068_);
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
                    v_reuseFailAlloc_7082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7076_);
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
    mut v_jobs_7084_: *mut LeanObject,
    mut v_cancel_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
    mut v_a_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
    mut v_a_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
    mut v_a_7091_: *mut LeanObject,
    mut v_a_7092_: *mut LeanObject,
    mut v_a_7093_: *mut LeanObject,
    mut v_a_7094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_7095_: u8 = 0;
    let mut v_res_7096_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7095_ = (lean_unbox(v_cancel_7085_) as u8);
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
    lean_dec(v_a_7093_);
    lean_dec_ref(v_a_7092_);
    lean_dec(v_a_7091_);
    lean_dec_ref(v_a_7090_);
    lean_dec(v_a_7089_);
    lean_dec_ref(v_a_7088_);
    lean_dec(v_a_7087_);
    lean_dec_ref(v_a_7086_);
    return v_res_7096_;
}
pub unsafe fn l_Lean_Elab_Tactic_TacticM_parFirst(
    mut v_00_u03b1_7097_: *mut LeanObject,
    mut v_jobs_7098_: *mut LeanObject,
    mut v_cancel_7099_: u8,
    mut v_a_7100_: *mut LeanObject,
    mut v_a_7101_: *mut LeanObject,
    mut v_a_7102_: *mut LeanObject,
    mut v_a_7103_: *mut LeanObject,
    mut v_a_7104_: *mut LeanObject,
    mut v_a_7105_: *mut LeanObject,
    mut v_a_7106_: *mut LeanObject,
    mut v_a_7107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7110_: *mut LeanObject,
    mut v_jobs_7111_: *mut LeanObject,
    mut v_cancel_7112_: *mut LeanObject,
    mut v_a_7113_: *mut LeanObject,
    mut v_a_7114_: *mut LeanObject,
    mut v_a_7115_: *mut LeanObject,
    mut v_a_7116_: *mut LeanObject,
    mut v_a_7117_: *mut LeanObject,
    mut v_a_7118_: *mut LeanObject,
    mut v_a_7119_: *mut LeanObject,
    mut v_a_7120_: *mut LeanObject,
    mut v_a_7121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancel_boxed_7122_: u8 = 0;
    let mut v_res_7123_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7122_ = (lean_unbox(v_cancel_7112_) as u8);
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
    lean_dec(v_a_7120_);
    lean_dec_ref(v_a_7119_);
    lean_dec(v_a_7118_);
    lean_dec_ref(v_a_7117_);
    lean_dec(v_a_7116_);
    lean_dec_ref(v_a_7115_);
    lean_dec(v_a_7114_);
    lean_dec_ref(v_a_7113_);
    return v_res_7123_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(
    mut v_00_u03b1_7124_: *mut LeanObject,
    mut v_cancel_7125_: u8,
    mut v_fst_7126_: *mut LeanObject,
    mut v_inst_7127_: *mut LeanObject,
    mut v_R_7128_: *mut LeanObject,
    mut v_a_7129_: *mut LeanObject,
    mut v_b_7130_: *mut LeanObject,
    mut v_c_7131_: *mut LeanObject,
    mut v___y_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
    mut v___y_7136_: *mut LeanObject,
    mut v___y_7137_: *mut LeanObject,
    mut v___y_7138_: *mut LeanObject,
    mut v___y_7139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_7142_: *mut LeanObject = *_args.add(0);
    let mut v_cancel_7143_: *mut LeanObject = *_args.add(1);
    let mut v_fst_7144_: *mut LeanObject = *_args.add(2);
    let mut v_inst_7145_: *mut LeanObject = *_args.add(3);
    let mut v_R_7146_: *mut LeanObject = *_args.add(4);
    let mut v_a_7147_: *mut LeanObject = *_args.add(5);
    let mut v_b_7148_: *mut LeanObject = *_args.add(6);
    let mut v_c_7149_: *mut LeanObject = *_args.add(7);
    let mut v___y_7150_: *mut LeanObject = *_args.add(8);
    let mut v___y_7151_: *mut LeanObject = *_args.add(9);
    let mut v___y_7152_: *mut LeanObject = *_args.add(10);
    let mut v___y_7153_: *mut LeanObject = *_args.add(11);
    let mut v___y_7154_: *mut LeanObject = *_args.add(12);
    let mut v___y_7155_: *mut LeanObject = *_args.add(13);
    let mut v___y_7156_: *mut LeanObject = *_args.add(14);
    let mut v___y_7157_: *mut LeanObject = *_args.add(15);
    let mut v___y_7158_: *mut LeanObject = *_args.add(16);
    let mut v_cancel_boxed_7159_: u8 = 0;
    let mut v_res_7160_: *mut LeanObject = core::ptr::null_mut();
    v_cancel_boxed_7159_ = (lean_unbox(v_cancel_7143_) as u8);
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
    lean_dec(v___y_7157_);
    lean_dec_ref(v___y_7156_);
    lean_dec(v___y_7155_);
    lean_dec_ref(v___y_7154_);
    lean_dec(v___y_7153_);
    lean_dec_ref(v___y_7152_);
    lean_dec(v___y_7151_);
    lean_dec_ref(v___y_7150_);
    return v_res_7160_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(
    mut v_00_u03b1_7161_: *mut LeanObject,
    mut v_msg_7162_: *mut LeanObject,
    mut v___y_7163_: *mut LeanObject,
    mut v___y_7164_: *mut LeanObject,
    mut v___y_7165_: *mut LeanObject,
    mut v___y_7166_: *mut LeanObject,
    mut v___y_7167_: *mut LeanObject,
    mut v___y_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7173_: *mut LeanObject,
    mut v_msg_7174_: *mut LeanObject,
    mut v___y_7175_: *mut LeanObject,
    mut v___y_7176_: *mut LeanObject,
    mut v___y_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
    mut v___y_7180_: *mut LeanObject,
    mut v___y_7181_: *mut LeanObject,
    mut v___y_7182_: *mut LeanObject,
    mut v___y_7183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7184_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_7182_);
    lean_dec_ref(v___y_7181_);
    lean_dec(v___y_7180_);
    lean_dec_ref(v___y_7179_);
    lean_dec(v___y_7178_);
    lean_dec_ref(v___y_7177_);
    lean_dec(v___y_7176_);
    lean_dec_ref(v___y_7175_);
    return v_res_7184_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Parallel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Parallel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Parallel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Parallel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Parallel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Parallel(builtin);
}

// Lean compiler output
// Module: Lean.Elab.ConfigEval.Extra
// Imports: Lean.Elab.ConfigEval.Instances
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_replaceRef};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_KVMap_instValueBool, l_Lean_KVMap_instValueInt, l_Lean_KVMap_instValueName,
    l_Lean_KVMap_instValueNat, l_Lean_KVMap_instValueString,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_set___redArg, l_Lean_getOptionDecl};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool,
    l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName,
    l_Lean_Elab_ConfigEval_ConfigItem_prevRoot,
    l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg,
};
use crate::r#gen::Lean::Elab::ConfigEval::Instances::{
    initialize_Lean_Elab_ConfigEval_Instances, l_Lean_Elab_ConfigEval_EvalExpr_instBool,
    l_Lean_Elab_ConfigEval_EvalExpr_instInt, l_Lean_Elab_ConfigEval_EvalExpr_instName,
    l_Lean_Elab_ConfigEval_EvalExpr_instNat, l_Lean_Elab_ConfigEval_EvalExpr_instString,
    l_Lean_Elab_ConfigEval_EvalTerm_instBool, l_Lean_Elab_ConfigEval_EvalTerm_instInt,
    l_Lean_Elab_ConfigEval_EvalTerm_instName, l_Lean_Elab_ConfigEval_EvalTerm_instNat,
    l_Lean_Elab_ConfigEval_EvalTerm_instString, runtime_initialize_Lean_Elab_ConfigEval_Instances,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 115, 101, 116, 32, 96, 83, 121, 110, 116, 97, 120, 96, 32,
        111, 112, 116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(
    mut v_t_515_: *mut crate::leanh::LeanObject,
    mut v___y_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_535_: u8 = 0;
    let mut v_enabled_536_: u8 = 0;
    let mut v_assignment_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_542_: u8 = 0;
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_518_ = lean_st_ref_get(v___y_516_);
                v_infoState_519_ = crate::leanh::lean_ctor_get(v___x_518_, 7);
                crate::leanh::lean_inc_ref(v_infoState_519_);
                crate::leanh::lean_dec(v___x_518_);
                v_enabled_520_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_519_);
                if v_enabled_520_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_515_);
                    v___x_521_ = crate::leanh::lean_box(0);
                    v___x_522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_522_, 0, v___x_521_);
                    return v___x_522_;
                } else {
                    v___x_523_ = lean_st_ref_take(v___y_516_);
                    v_infoState_524_ = crate::leanh::lean_ctor_get(v___x_523_, 7);
                    v_env_525_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                    v_nextMacroScope_526_ = crate::leanh::lean_ctor_get(v___x_523_, 1);
                    v_ngen_527_ = crate::leanh::lean_ctor_get(v___x_523_, 2);
                    v_auxDeclNGen_528_ = crate::leanh::lean_ctor_get(v___x_523_, 3);
                    v_traceState_529_ = crate::leanh::lean_ctor_get(v___x_523_, 4);
                    v_cache_530_ = crate::leanh::lean_ctor_get(v___x_523_, 5);
                    v_messages_531_ = crate::leanh::lean_ctor_get(v___x_523_, 6);
                    v_snapshotTasks_532_ = crate::leanh::lean_ctor_get(v___x_523_, 8);
                    v_isSharedCheck_554_ = (!crate::leanh::lean_is_exclusive(v___x_523_)) as u8;
                    if v_isSharedCheck_554_ == 0 {
                        v___x_534_ = v___x_523_;
                        v_isShared_535_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_532_);
                        crate::leanh::lean_inc(v_infoState_524_);
                        crate::leanh::lean_inc(v_messages_531_);
                        crate::leanh::lean_inc(v_cache_530_);
                        crate::leanh::lean_inc(v_traceState_529_);
                        crate::leanh::lean_inc(v_auxDeclNGen_528_);
                        crate::leanh::lean_inc(v_ngen_527_);
                        crate::leanh::lean_inc(v_nextMacroScope_526_);
                        crate::leanh::lean_inc(v_env_525_);
                        crate::leanh::lean_dec(v___x_523_);
                        v___x_534_ = crate::leanh::lean_box(0);
                        v_isShared_535_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_536_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_524_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_537_ = crate::leanh::lean_ctor_get(v_infoState_524_, 0);
                v_lazyAssignment_538_ = crate::leanh::lean_ctor_get(v_infoState_524_, 1);
                v_trees_539_ = crate::leanh::lean_ctor_get(v_infoState_524_, 2);
                v_isSharedCheck_553_ = (!crate::leanh::lean_is_exclusive(v_infoState_524_)) as u8;
                if v_isSharedCheck_553_ == 0 {
                    v___x_541_ = v_infoState_524_;
                    v_isShared_542_ = v_isSharedCheck_553_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_539_);
                    crate::leanh::lean_inc(v_lazyAssignment_538_);
                    crate::leanh::lean_inc(v_assignment_537_);
                    crate::leanh::lean_dec(v_infoState_524_);
                    v___x_541_ = crate::leanh::lean_box(0);
                    v_isShared_542_ = v_isSharedCheck_553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_543_ = l_Lean_PersistentArray_push___redArg(v_trees_539_, v_t_515_);
                if v_isShared_542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_541_, 2, v___x_543_);
                    v___x_545_ = v___x_541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v_assignment_537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 1, v_lazyAssignment_538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 2, v___x_543_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_552_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_536_,
                    );
                    v___x_545_ = v_reuseFailAlloc_552_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_534_, 7, v___x_545_);
                    v___x_547_ = v___x_534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_551_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 0, v_env_525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ngen_527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 4, v_traceState_529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 5, v_cache_530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 6, v_messages_531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 7, v___x_545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 8, v_snapshotTasks_532_);
                    v___x_547_ = v_reuseFailAlloc_551_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_548_ = lean_st_ref_set(v___y_516_, v___x_547_);
                v___x_549_ = crate::leanh::lean_box(0);
                v___x_550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
                return v___x_550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(
    mut v_t_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_555_, v___y_556_);
    crate::leanh::lean_dec(v___y_556_);
    return v_res_558_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
    v___x_561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_561_, 0, v___x_560_);
    return v___x_561_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_562_: usize = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = 5usize;
    v___x_563_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_564_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_565_ = lean_mk_empty_array_with_capacity(v___x_564_);
    v___x_566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0);
    v___x_567_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_567_, 0, v___x_566_);
    crate::leanh::lean_ctor_set(v___x_567_, 1, v___x_565_);
    crate::leanh::lean_ctor_set(v___x_567_, 2, v___x_563_);
    crate::leanh::lean_ctor_set(v___x_567_, 3, v___x_563_);
    crate::leanh::lean_ctor_set_usize(v___x_567_, 4, v___x_562_);
    return v___x_567_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(
    mut v_t_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
    mut v___y_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_578_: u8 = 0;
    v___x_576_ = lean_st_ref_get(v___y_574_);
    v_infoState_577_ = crate::leanh::lean_ctor_get(v___x_576_, 7);
    crate::leanh::lean_inc_ref(v_infoState_577_);
    crate::leanh::lean_dec(v___x_576_);
    v_enabled_578_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_577_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_577_);
    if v_enabled_578_ == 0 {
        let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_568_);
        v___x_579_ = crate::leanh::lean_box(0);
        v___x_580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_580_, 0, v___x_579_);
        return v___x_580_;
    } else {
        let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1);
        v___x_582_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_582_, 0, v_t_568_);
        crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
        v___x_583_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v___x_582_, v___y_574_);
        return v___x_583_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(
    mut v_t_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v_t_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
    crate::leanh::lean_dec(v___y_590_);
    crate::leanh::lean_dec_ref(v___y_589_);
    crate::leanh::lean_dec(v___y_588_);
    crate::leanh::lean_dec_ref(v___y_587_);
    crate::leanh::lean_dec(v___y_586_);
    crate::leanh::lean_dec_ref(v___y_585_);
    return v_res_592_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(
    mut v_info_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
    mut v___y_595_: *mut crate::leanh::LeanObject,
    mut v___y_596_: *mut crate::leanh::LeanObject,
    mut v___y_597_: *mut crate::leanh::LeanObject,
    mut v___y_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_601_, 0, v_info_593_);
    v___x_602_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_601_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
    return v___x_602_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(
    mut v_info_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v_info_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
    crate::leanh::lean_dec(v___y_609_);
    crate::leanh::lean_dec_ref(v___y_608_);
    crate::leanh::lean_dec(v___y_607_);
    crate::leanh::lean_dec_ref(v___y_606_);
    crate::leanh::lean_dec(v___y_605_);
    crate::leanh::lean_dec_ref(v___y_604_);
    return v_res_611_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(
    mut v_msgData_612_: *mut crate::leanh::LeanObject,
    mut v___y_613_: *mut crate::leanh::LeanObject,
    mut v___y_614_: *mut crate::leanh::LeanObject,
    mut v___y_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = lean_st_ref_get(v___y_616_);
    v_env_619_ = crate::leanh::lean_ctor_get(v___x_618_, 0);
    crate::leanh::lean_inc_ref(v_env_619_);
    crate::leanh::lean_dec(v___x_618_);
    v___x_620_ = lean_st_ref_get(v___y_614_);
    v_mctx_621_ = crate::leanh::lean_ctor_get(v___x_620_, 0);
    crate::leanh::lean_inc_ref(v_mctx_621_);
    crate::leanh::lean_dec(v___x_620_);
    v_lctx_622_ = crate::leanh::lean_ctor_get(v___y_613_, 2);
    v_options_623_ = crate::leanh::lean_ctor_get(v___y_615_, 2);
    crate::leanh::lean_inc_ref(v_options_623_);
    crate::leanh::lean_inc_ref(v_lctx_622_);
    v___x_624_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_624_, 0, v_env_619_);
    crate::leanh::lean_ctor_set(v___x_624_, 1, v_mctx_621_);
    crate::leanh::lean_ctor_set(v___x_624_, 2, v_lctx_622_);
    crate::leanh::lean_ctor_set(v___x_624_, 3, v_options_623_);
    v___x_625_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_624_);
    crate::leanh::lean_ctor_set(v___x_625_, 1, v_msgData_612_);
    v___x_626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_626_, 0, v___x_625_);
    return v___x_626_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(
    mut v_msgData_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_633_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msgData_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
    crate::leanh::lean_dec(v___y_631_);
    crate::leanh::lean_dec_ref(v___y_630_);
    crate::leanh::lean_dec(v___y_629_);
    crate::leanh::lean_dec_ref(v___y_628_);
    return v_res_633_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = crate::leanh::lean_box(1);
    v___x_635_ = l_Lean_MessageData_ofFormat(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2;
    v___x_640_ = l_Lean_MessageData_ofFormat(v___x_639_);
    return v___x_640_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(
    mut v_x_641_: *mut crate::leanh::LeanObject,
    mut v_x_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v_before_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut v_unused_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_642_) == 0 {
                    return v_x_641_;
                } else {
                    v_head_643_ = crate::leanh::lean_ctor_get(v_x_642_, 0);
                    v_tail_644_ = crate::leanh::lean_ctor_get(v_x_642_, 1);
                    v_isSharedCheck_666_ = (!crate::leanh::lean_is_exclusive(v_x_642_)) as u8;
                    if v_isSharedCheck_666_ == 0 {
                        v___x_646_ = v_x_642_;
                        v_isShared_647_ = v_isSharedCheck_666_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_644_);
                        crate::leanh::lean_inc(v_head_643_);
                        crate::leanh::lean_dec(v_x_642_);
                        v___x_646_ = crate::leanh::lean_box(0);
                        v_isShared_647_ = v_isSharedCheck_666_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_648_ = crate::leanh::lean_ctor_get(v_head_643_, 0);
                v_isSharedCheck_664_ = (!crate::leanh::lean_is_exclusive(v_head_643_)) as u8;
                if v_isSharedCheck_664_ == 0 {
                    v_unused_665_ = crate::leanh::lean_ctor_get(v_head_643_, 1);
                    crate::leanh::lean_dec(v_unused_665_);
                    v___x_650_ = v_head_643_;
                    v_isShared_651_ = v_isSharedCheck_664_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_648_);
                    crate::leanh::lean_dec(v_head_643_);
                    v___x_650_ = crate::leanh::lean_box(0);
                    v_isShared_651_ = v_isSharedCheck_664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
                if v_isShared_651_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_650_, 7);
                    crate::leanh::lean_ctor_set(v___x_650_, 1, v___x_652_);
                    crate::leanh::lean_ctor_set(v___x_650_, 0, v_x_641_);
                    v___x_654_ = v___x_650_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_663_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_663_, 0, v_x_641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_663_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3);
                if v_isShared_647_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_646_, 7);
                    crate::leanh::lean_ctor_set(v___x_646_, 1, v___x_655_);
                    crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_654_);
                    v___x_657_ = v___x_646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_662_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_655_);
                    v___x_657_ = v_reuseFailAlloc_662_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_658_ = l_Lean_MessageData_ofSyntax(v_before_648_);
                v___x_659_ = l_Lean_indentD(v___x_658_);
                v___x_660_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_657_);
                crate::leanh::lean_ctor_set(v___x_660_, 1, v___x_659_);
                v_x_641_ = v___x_660_;
                v_x_642_ = v_tail_644_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(
    mut v_opts_667_: *mut crate::leanh::LeanObject,
    mut v_opt_668_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_669_ = crate::leanh::lean_ctor_get(v_opt_668_, 0);
    v_defValue_670_ = crate::leanh::lean_ctor_get(v_opt_668_, 1);
    v_map_671_ = crate::leanh::lean_ctor_get(v_opts_667_, 0);
    v___x_672_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_671_,
            v_name_669_,
        );
    if crate::leanh::lean_obj_tag(v___x_672_) == 0 {
        let mut v___x_673_: u8 = 0;
        v___x_673_ = (crate::leanh::lean_unbox(v_defValue_670_) as u8);
        return v___x_673_;
    } else {
        let mut v_val_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_674_ = crate::leanh::lean_ctor_get(v___x_672_, 0);
        crate::leanh::lean_inc(v_val_674_);
        crate::leanh::lean_dec_ref_known(v___x_672_, 1);
        if crate::leanh::lean_obj_tag(v_val_674_) == 1 {
            let mut v_v_675_: u8 = 0;
            v_v_675_ = crate::leanh::lean_ctor_get_uint8(v_val_674_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_674_, 0);
            return v_v_675_;
        } else {
            let mut v___x_676_: u8 = 0;
            crate::leanh::lean_dec(v_val_674_);
            v___x_676_ = (crate::leanh::lean_unbox(v_defValue_670_) as u8);
            return v___x_676_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(
    mut v_opts_677_: *mut crate::leanh::LeanObject,
    mut v_opt_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_679_: u8 = 0;
    let mut v_r_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_opts_677_, v_opt_678_);
    crate::leanh::lean_dec_ref(v_opt_678_);
    crate::leanh::lean_dec_ref(v_opts_677_);
    v_r_680_ = crate::leanh::lean_box((v_res_679_) as usize);
    return v_r_680_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1;
    v___x_685_ = l_Lean_MessageData_ofFormat(v___x_684_);
    return v___x_685_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(
    mut v_msgData_686_: *mut crate::leanh::LeanObject,
    mut v_macroStack_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_699_: u8 = 0;
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_711_: u8 = 0;
    let mut v_unused_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_690_ = crate::leanh::lean_ctor_get(v___y_688_, 2);
                v___x_691_ = l_Lean_Elab_pp_macroStack;
                v___x_692_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_options_690_, v___x_691_);
                if v___x_692_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_687_);
                    v___x_693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_693_, 0, v_msgData_686_);
                    return v___x_693_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_687_) == 0 {
                        v___x_694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_694_, 0, v_msgData_686_);
                        return v___x_694_;
                    } else {
                        v_head_695_ = crate::leanh::lean_ctor_get(v_macroStack_687_, 0);
                        crate::leanh::lean_inc(v_head_695_);
                        v_after_696_ = crate::leanh::lean_ctor_get(v_head_695_, 1);
                        v_isSharedCheck_711_ =
                            (!crate::leanh::lean_is_exclusive(v_head_695_)) as u8;
                        if v_isSharedCheck_711_ == 0 {
                            v_unused_712_ = crate::leanh::lean_ctor_get(v_head_695_, 0);
                            crate::leanh::lean_dec(v_unused_712_);
                            v___x_698_ = v_head_695_;
                            v_isShared_699_ = v_isSharedCheck_711_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_696_);
                            crate::leanh::lean_dec(v_head_695_);
                            v___x_698_ = crate::leanh::lean_box(0);
                            v_isShared_699_ = v_isSharedCheck_711_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
                if v_isShared_699_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_698_, 7);
                    crate::leanh::lean_ctor_set(v___x_698_, 1, v___x_700_);
                    crate::leanh::lean_ctor_set(v___x_698_, 0, v_msgData_686_);
                    v___x_702_ = v___x_698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_710_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_710_, 0, v_msgData_686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_700_);
                    v___x_702_ = v_reuseFailAlloc_710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2);
                v___x_704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_702_);
                crate::leanh::lean_ctor_set(v___x_704_, 1, v___x_703_);
                v___x_705_ = l_Lean_MessageData_ofSyntax(v_after_696_);
                v___x_706_ = l_Lean_indentD(v___x_705_);
                v_msgData_707_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_707_, 0, v___x_704_);
                crate::leanh::lean_ctor_set(v_msgData_707_, 1, v___x_706_);
                v___x_708_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(v_msgData_707_, v_macroStack_687_);
                v___x_709_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_708_);
                return v___x_709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_msgData_713_: *mut crate::leanh::LeanObject,
    mut v_macroStack_714_: *mut crate::leanh::LeanObject,
    mut v___y_715_: *mut crate::leanh::LeanObject,
    mut v___y_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_713_, v_macroStack_714_, v___y_715_);
    crate::leanh::lean_dec_ref(v___y_715_);
    return v_res_717_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(
    mut v_msg_718_: *mut crate::leanh::LeanObject,
    mut v___y_719_: *mut crate::leanh::LeanObject,
    mut v___y_720_: *mut crate::leanh::LeanObject,
    mut v___y_721_: *mut crate::leanh::LeanObject,
    mut v___y_722_: *mut crate::leanh::LeanObject,
    mut v___y_723_: *mut crate::leanh::LeanObject,
    mut v___y_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_735_: u8 = 0;
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_726_ = crate::leanh::lean_ctor_get(v___y_723_, 5);
                v___x_727_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msg_718_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
                v_a_728_ = crate::leanh::lean_ctor_get(v___x_727_, 0);
                crate::leanh::lean_inc(v_a_728_);
                crate::leanh::lean_dec_ref(v___x_727_);
                v_macroStack_729_ = crate::leanh::lean_ctor_get(v___y_719_, 1);
                v___x_730_ = l_Lean_Elab_getBetterRef(v_ref_726_, v_macroStack_729_);
                crate::leanh::lean_inc(v_macroStack_729_);
                v___x_731_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_a_728_, v_macroStack_729_, v___y_723_);
                v_a_732_ = crate::leanh::lean_ctor_get(v___x_731_, 0);
                v_isSharedCheck_740_ = (!crate::leanh::lean_is_exclusive(v___x_731_)) as u8;
                if v_isSharedCheck_740_ == 0 {
                    v___x_734_ = v___x_731_;
                    v_isShared_735_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_732_);
                    crate::leanh::lean_dec(v___x_731_);
                    v___x_734_ = crate::leanh::lean_box(0);
                    v_isShared_735_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_736_, 0, v___x_730_);
                crate::leanh::lean_ctor_set(v___x_736_, 1, v_a_732_);
                if v_isShared_735_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_734_, 1);
                    crate::leanh::lean_ctor_set(v___x_734_, 0, v___x_736_);
                    v___x_738_ = v___x_734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
                    v___x_738_ = v_reuseFailAlloc_739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(
    mut v_msg_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
    crate::leanh::lean_dec(v___y_747_);
    crate::leanh::lean_dec_ref(v___y_746_);
    crate::leanh::lean_dec(v___y_745_);
    crate::leanh::lean_dec_ref(v___y_744_);
    crate::leanh::lean_dec(v___y_743_);
    crate::leanh::lean_dec_ref(v___y_742_);
    return v_res_749_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(
    mut v_ref_750_: *mut crate::leanh::LeanObject,
    mut v_msg_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_771_: u8 = 0;
    let mut v_cancelTk_x3f_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_773_: u8 = 0;
    let mut v_inheritedTraceOptions_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_759_ = crate::leanh::lean_ctor_get(v___y_756_, 0);
    v_fileMap_760_ = crate::leanh::lean_ctor_get(v___y_756_, 1);
    v_options_761_ = crate::leanh::lean_ctor_get(v___y_756_, 2);
    v_currRecDepth_762_ = crate::leanh::lean_ctor_get(v___y_756_, 3);
    v_maxRecDepth_763_ = crate::leanh::lean_ctor_get(v___y_756_, 4);
    v_ref_764_ = crate::leanh::lean_ctor_get(v___y_756_, 5);
    v_currNamespace_765_ = crate::leanh::lean_ctor_get(v___y_756_, 6);
    v_openDecls_766_ = crate::leanh::lean_ctor_get(v___y_756_, 7);
    v_initHeartbeats_767_ = crate::leanh::lean_ctor_get(v___y_756_, 8);
    v_maxHeartbeats_768_ = crate::leanh::lean_ctor_get(v___y_756_, 9);
    v_quotContext_769_ = crate::leanh::lean_ctor_get(v___y_756_, 10);
    v_currMacroScope_770_ = crate::leanh::lean_ctor_get(v___y_756_, 11);
    v_diag_771_ = crate::leanh::lean_ctor_get_uint8(
        v___y_756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_772_ = crate::leanh::lean_ctor_get(v___y_756_, 12);
    v_suppressElabErrors_773_ = crate::leanh::lean_ctor_get_uint8(
        v___y_756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_774_ = crate::leanh::lean_ctor_get(v___y_756_, 13);
    v_ref_775_ = l_Lean_replaceRef(v_ref_750_, v_ref_764_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_774_);
    crate::leanh::lean_inc(v_cancelTk_x3f_772_);
    crate::leanh::lean_inc(v_currMacroScope_770_);
    crate::leanh::lean_inc(v_quotContext_769_);
    crate::leanh::lean_inc(v_maxHeartbeats_768_);
    crate::leanh::lean_inc(v_initHeartbeats_767_);
    crate::leanh::lean_inc(v_openDecls_766_);
    crate::leanh::lean_inc(v_currNamespace_765_);
    crate::leanh::lean_inc(v_maxRecDepth_763_);
    crate::leanh::lean_inc(v_currRecDepth_762_);
    crate::leanh::lean_inc_ref(v_options_761_);
    crate::leanh::lean_inc_ref(v_fileMap_760_);
    crate::leanh::lean_inc_ref(v_fileName_759_);
    v___x_776_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_776_, 0, v_fileName_759_);
    crate::leanh::lean_ctor_set(v___x_776_, 1, v_fileMap_760_);
    crate::leanh::lean_ctor_set(v___x_776_, 2, v_options_761_);
    crate::leanh::lean_ctor_set(v___x_776_, 3, v_currRecDepth_762_);
    crate::leanh::lean_ctor_set(v___x_776_, 4, v_maxRecDepth_763_);
    crate::leanh::lean_ctor_set(v___x_776_, 5, v_ref_775_);
    crate::leanh::lean_ctor_set(v___x_776_, 6, v_currNamespace_765_);
    crate::leanh::lean_ctor_set(v___x_776_, 7, v_openDecls_766_);
    crate::leanh::lean_ctor_set(v___x_776_, 8, v_initHeartbeats_767_);
    crate::leanh::lean_ctor_set(v___x_776_, 9, v_maxHeartbeats_768_);
    crate::leanh::lean_ctor_set(v___x_776_, 10, v_quotContext_769_);
    crate::leanh::lean_ctor_set(v___x_776_, 11, v_currMacroScope_770_);
    crate::leanh::lean_ctor_set(v___x_776_, 12, v_cancelTk_x3f_772_);
    crate::leanh::lean_ctor_set(v___x_776_, 13, v_inheritedTraceOptions_774_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_776_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_771_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_776_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_773_,
    );
    v___x_777_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___x_776_, v___y_757_);
    crate::leanh::lean_dec_ref_known(v___x_776_, 14);
    return v___x_777_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(
    mut v_ref_778_: *mut crate::leanh::LeanObject,
    mut v_msg_779_: *mut crate::leanh::LeanObject,
    mut v___y_780_: *mut crate::leanh::LeanObject,
    mut v___y_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_778_, v_msg_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
    crate::leanh::lean_dec(v___y_785_);
    crate::leanh::lean_dec_ref(v___y_784_);
    crate::leanh::lean_dec(v___y_783_);
    crate::leanh::lean_dec_ref(v___y_782_);
    crate::leanh::lean_dec(v___y_781_);
    crate::leanh::lean_dec_ref(v___y_780_);
    crate::leanh::lean_dec(v_ref_778_);
    return v_res_787_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2;
    v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
    return v___x_793_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4;
    v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
    return v___x_796_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(
    mut v_optionPrefix_797_: *mut crate::leanh::LeanObject,
    mut v_opts_798_: *mut crate::leanh::LeanObject,
    mut v_item_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_option_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionComps_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_839_: u8 = 0;
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optName_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_856_: u8 = 0;
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_861_: u8 = 0;
    let mut v_a_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_865_: u8 = 0;
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_900_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_904_: u8 = 0;
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_909_: u8 = 0;
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_913_: u8 = 0;
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v_ref_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_935_: u8 = 0;
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut v_unused_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_807_ = l_Lean_Elab_ConfigEval_EvalTerm_instBool;
                v___x_808_ = l_Lean_Elab_ConfigEval_EvalExpr_instBool;
                v___x_809_ = l_Lean_KVMap_instValueBool;
                v___x_810_ = l_Lean_Elab_ConfigEval_EvalTerm_instNat;
                v___x_811_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
                v___x_812_ = l_Lean_KVMap_instValueNat;
                v___x_813_ = l_Lean_Elab_ConfigEval_EvalTerm_instInt;
                v___x_814_ = l_Lean_Elab_ConfigEval_EvalExpr_instInt;
                v___x_815_ = l_Lean_KVMap_instValueInt;
                v___x_816_ = l_Lean_Elab_ConfigEval_EvalTerm_instString;
                v___x_817_ = l_Lean_Elab_ConfigEval_EvalExpr_instString;
                v___x_818_ = l_Lean_KVMap_instValueString;
                v___x_819_ = l_Lean_Elab_ConfigEval_EvalTerm_instName;
                v___x_820_ = l_Lean_Elab_ConfigEval_EvalExpr_instName;
                v___x_821_ = l_Lean_KVMap_instValueName;
                v_option_822_ = crate::leanh::lean_ctor_get(v_item_799_, 1);
                v_value_823_ = crate::leanh::lean_ctor_get(v_item_799_, 2);
                crate::leanh::lean_inc(v_value_823_);
                v_optionComps_824_ = crate::leanh::lean_ctor_get(v_item_799_, 5);
                v___x_825_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_799_);
                crate::leanh::lean_inc(v_optionComps_824_);
                v___x_826_ = lean_array_mk(v_optionComps_824_);
                v___x_827_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1;
                v___x_828_ = crate::leanh::lean_box(2);
                v___x_829_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_828_);
                crate::leanh::lean_ctor_set(v___x_829_, 1, v___x_827_);
                crate::leanh::lean_ctor_set(v___x_829_, 2, v___x_826_);
                v___x_830_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_831_ = lean_mk_empty_array_with_capacity(v___x_830_);
                v___x_832_ = lean_array_push(v___x_831_, v___x_825_);
                v___x_833_ = lean_array_push(v___x_832_, v___x_829_);
                v___x_834_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_834_, 0, v___x_828_);
                crate::leanh::lean_ctor_set(v___x_834_, 1, v___x_827_);
                crate::leanh::lean_ctor_set(v___x_834_, 2, v___x_833_);
                v___x_835_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
                v___x_836_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v___x_835_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
                v_isSharedCheck_936_ = (!crate::leanh::lean_is_exclusive(v___x_836_)) as u8;
                if v_isSharedCheck_936_ == 0 {
                    v_unused_937_ = crate::leanh::lean_ctor_get(v___x_836_, 0);
                    crate::leanh::lean_dec(v_unused_937_);
                    v___x_838_ = v___x_836_;
                    v_isShared_839_ = v_isSharedCheck_936_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_836_);
                    v___x_838_ = crate::leanh::lean_box(0);
                    v_isShared_839_ = v_isSharedCheck_936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_item_799_);
                v___x_840_ = l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(v_item_799_);
                v_optName_841_ = l_Lean_Name_append(v_optionPrefix_797_, v___x_840_);
                crate::leanh::lean_inc(v_optName_841_);
                v___x_870_ = l_Lean_getOptionDecl(v_optName_841_);
                if crate::leanh::lean_obj_tag(v___x_870_) == 0 {
                    v_a_871_ = crate::leanh::lean_ctor_get(v___x_870_, 0);
                    crate::leanh::lean_inc(v_a_871_);
                    crate::leanh::lean_dec_ref_known(v___x_870_, 1);
                    v_declName_872_ = crate::leanh::lean_ctor_get(v_a_871_, 1);
                    crate::leanh::lean_inc(v_declName_872_);
                    v_defValue_873_ = crate::leanh::lean_ctor_get(v_a_871_, 2);
                    crate::leanh::lean_inc_ref(v_defValue_873_);
                    crate::leanh::lean_dec(v_a_871_);
                    crate::leanh::lean_inc(v_optName_841_);
                    crate::leanh::lean_inc(v_option_822_);
                    v___x_874_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_874_, 0, v_option_822_);
                    crate::leanh::lean_ctor_set(v___x_874_, 1, v_optName_841_);
                    crate::leanh::lean_ctor_set(v___x_874_, 2, v_declName_872_);
                    if v_isShared_839_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_838_, 5);
                        crate::leanh::lean_ctor_set(v___x_838_, 0, v___x_874_);
                        v___x_876_ = v___x_838_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_920_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_874_);
                        v___x_876_ = v_reuseFailAlloc_920_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_optName_841_);
                    crate::leanh::lean_dec(v_value_823_);
                    crate::leanh::lean_dec_ref(v_item_799_);
                    crate::leanh::lean_dec_ref(v_opts_798_);
                    v_a_921_ = crate::leanh::lean_ctor_get(v___x_870_, 0);
                    v_isSharedCheck_935_ = (!crate::leanh::lean_is_exclusive(v___x_870_)) as u8;
                    if v_isSharedCheck_935_ == 0 {
                        v___x_923_ = v___x_870_;
                        v_isShared_924_ = v_isSharedCheck_935_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_921_);
                        crate::leanh::lean_dec(v___x_870_);
                        v___x_923_ = crate::leanh::lean_box(0);
                        v_isShared_924_ = v_isSharedCheck_935_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_inst_844_);
                crate::leanh::lean_inc_ref(v_inst_843_);
                v___x_852_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
                    v_inst_843_,
                    v_inst_844_,
                    v_value_823_,
                    v___y_846_,
                    v___y_847_,
                    v___y_848_,
                    v___y_849_,
                    v___y_850_,
                    v___y_851_,
                );
                if crate::leanh::lean_obj_tag(v___x_852_) == 0 {
                    v_a_853_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_861_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_861_ == 0 {
                        v___x_855_ = v___x_852_;
                        v_isShared_856_ = v_isSharedCheck_861_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_853_);
                        crate::leanh::lean_dec(v___x_852_);
                        v___x_855_ = crate::leanh::lean_box(0);
                        v_isShared_856_ = v_isSharedCheck_861_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_optName_841_);
                    crate::leanh::lean_dec_ref(v_opts_798_);
                    v_a_862_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_869_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_869_ == 0 {
                        v___x_864_ = v___x_852_;
                        v_isShared_865_ = v_isSharedCheck_869_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_862_);
                        crate::leanh::lean_dec(v___x_852_);
                        v___x_864_ = crate::leanh::lean_box(0);
                        v_isShared_865_ = v_isSharedCheck_869_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_inst_845_);
                v___x_857_ =
                    l_Lean_Options_set___redArg(v_inst_845_, v_opts_798_, v_optName_841_, v_a_853_);
                if v_isShared_856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_857_);
                    v___x_859_ = v___x_855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
                    v___x_859_ = v_reuseFailAlloc_860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_859_;
            }
            5 => {
                if v_isShared_865_ == 0 {
                    v___x_867_ = v___x_864_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
                    v___x_867_ = v_reuseFailAlloc_868_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_867_;
            }
            7 => {
                v___x_877_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_876_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
                crate::leanh::lean_dec_ref(v___x_877_);
                match crate::leanh::lean_obj_tag(v_defValue_873_) {
                    0 => {
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 1);
                        v___x_878_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                            v_item_799_,
                            v_a_800_,
                            v_a_801_,
                            v_a_802_,
                            v_a_803_,
                            v_a_804_,
                            v_a_805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_878_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_878_, 1);
                            v_inst_843_ = v___x_816_;
                            v_inst_844_ = v___x_817_;
                            v_inst_845_ = v___x_818_;
                            v___y_846_ = v_a_800_;
                            v___y_847_ = v_a_801_;
                            v___y_848_ = v_a_802_;
                            v___y_849_ = v_a_803_;
                            v___y_850_ = v_a_804_;
                            v___y_851_ = v_a_805_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_optName_841_);
                            crate::leanh::lean_dec(v_value_823_);
                            crate::leanh::lean_dec_ref(v_opts_798_);
                            v_a_879_ = crate::leanh::lean_ctor_get(v___x_878_, 0);
                            v_isSharedCheck_886_ =
                                (!crate::leanh::lean_is_exclusive(v___x_878_)) as u8;
                            if v_isSharedCheck_886_ == 0 {
                                v___x_881_ = v___x_878_;
                                v_isShared_882_ = v_isSharedCheck_886_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_879_);
                                crate::leanh::lean_dec(v___x_878_);
                                v___x_881_ = crate::leanh::lean_box(0);
                                v_isShared_882_ = v_isSharedCheck_886_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 0);
                        crate::leanh::lean_dec_ref(v_item_799_);
                        v_inst_843_ = v___x_807_;
                        v_inst_844_ = v___x_808_;
                        v_inst_845_ = v___x_809_;
                        v___y_846_ = v_a_800_;
                        v___y_847_ = v_a_801_;
                        v___y_848_ = v_a_802_;
                        v___y_849_ = v_a_803_;
                        v___y_850_ = v_a_804_;
                        v___y_851_ = v_a_805_;
                        state = 2;
                        continue;
                    }
                    2 => {
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 1);
                        v___x_887_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                            v_item_799_,
                            v_a_800_,
                            v_a_801_,
                            v_a_802_,
                            v_a_803_,
                            v_a_804_,
                            v_a_805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_887_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_887_, 1);
                            v_inst_843_ = v___x_819_;
                            v_inst_844_ = v___x_820_;
                            v_inst_845_ = v___x_821_;
                            v___y_846_ = v_a_800_;
                            v___y_847_ = v_a_801_;
                            v___y_848_ = v_a_802_;
                            v___y_849_ = v_a_803_;
                            v___y_850_ = v_a_804_;
                            v___y_851_ = v_a_805_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_optName_841_);
                            crate::leanh::lean_dec(v_value_823_);
                            crate::leanh::lean_dec_ref(v_opts_798_);
                            v_a_888_ = crate::leanh::lean_ctor_get(v___x_887_, 0);
                            v_isSharedCheck_895_ =
                                (!crate::leanh::lean_is_exclusive(v___x_887_)) as u8;
                            if v_isSharedCheck_895_ == 0 {
                                v___x_890_ = v___x_887_;
                                v_isShared_891_ = v_isSharedCheck_895_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_888_);
                                crate::leanh::lean_dec(v___x_887_);
                                v___x_890_ = crate::leanh::lean_box(0);
                                v_isShared_891_ = v_isSharedCheck_895_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 1);
                        v___x_896_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                            v_item_799_,
                            v_a_800_,
                            v_a_801_,
                            v_a_802_,
                            v_a_803_,
                            v_a_804_,
                            v_a_805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_896_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_896_, 1);
                            v_inst_843_ = v___x_810_;
                            v_inst_844_ = v___x_811_;
                            v_inst_845_ = v___x_812_;
                            v___y_846_ = v_a_800_;
                            v___y_847_ = v_a_801_;
                            v___y_848_ = v_a_802_;
                            v___y_849_ = v_a_803_;
                            v___y_850_ = v_a_804_;
                            v___y_851_ = v_a_805_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_optName_841_);
                            crate::leanh::lean_dec(v_value_823_);
                            crate::leanh::lean_dec_ref(v_opts_798_);
                            v_a_897_ = crate::leanh::lean_ctor_get(v___x_896_, 0);
                            v_isSharedCheck_904_ =
                                (!crate::leanh::lean_is_exclusive(v___x_896_)) as u8;
                            if v_isSharedCheck_904_ == 0 {
                                v___x_899_ = v___x_896_;
                                v_isShared_900_ = v_isSharedCheck_904_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_897_);
                                crate::leanh::lean_dec(v___x_896_);
                                v___x_899_ = crate::leanh::lean_box(0);
                                v_isShared_900_ = v_isSharedCheck_904_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 1);
                        v___x_905_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                            v_item_799_,
                            v_a_800_,
                            v_a_801_,
                            v_a_802_,
                            v_a_803_,
                            v_a_804_,
                            v_a_805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_905_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_905_, 1);
                            v_inst_843_ = v___x_813_;
                            v_inst_844_ = v___x_814_;
                            v_inst_845_ = v___x_815_;
                            v___y_846_ = v_a_800_;
                            v___y_847_ = v_a_801_;
                            v___y_848_ = v_a_802_;
                            v___y_849_ = v_a_803_;
                            v___y_850_ = v_a_804_;
                            v___y_851_ = v_a_805_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_optName_841_);
                            crate::leanh::lean_dec(v_value_823_);
                            crate::leanh::lean_dec_ref(v_opts_798_);
                            v_a_906_ = crate::leanh::lean_ctor_get(v___x_905_, 0);
                            v_isSharedCheck_913_ =
                                (!crate::leanh::lean_is_exclusive(v___x_905_)) as u8;
                            if v_isSharedCheck_913_ == 0 {
                                v___x_908_ = v___x_905_;
                                v_isShared_909_ = v_isSharedCheck_913_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_906_);
                                crate::leanh::lean_dec(v___x_905_);
                                v___x_908_ = crate::leanh::lean_box(0);
                                v_isShared_909_ = v_isSharedCheck_913_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_inc(v_option_822_);
                        crate::leanh::lean_dec_ref_known(v_defValue_873_, 1);
                        crate::leanh::lean_dec(v_value_823_);
                        crate::leanh::lean_dec_ref(v_item_799_);
                        crate::leanh::lean_dec_ref(v_opts_798_);
                        v___x_914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3);
                        v___x_915_ = l_Lean_MessageData_ofName(v_optName_841_);
                        v___x_916_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_914_);
                        crate::leanh::lean_ctor_set(v___x_916_, 1, v___x_915_);
                        v___x_917_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5);
                        v___x_918_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_916_);
                        crate::leanh::lean_ctor_set(v___x_918_, 1, v___x_917_);
                        v___x_919_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_option_822_, v___x_918_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
                        crate::leanh::lean_dec(v_option_822_);
                        return v___x_919_;
                    }
                }
            }
            8 => {
                if v_isShared_882_ == 0 {
                    v___x_884_ = v___x_881_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
                    v___x_884_ = v_reuseFailAlloc_885_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_884_;
            }
            10 => {
                if v_isShared_891_ == 0 {
                    v___x_893_ = v___x_890_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
                    v___x_893_ = v_reuseFailAlloc_894_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_893_;
            }
            12 => {
                if v_isShared_900_ == 0 {
                    v___x_902_ = v___x_899_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
                    v___x_902_ = v_reuseFailAlloc_903_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_902_;
            }
            14 => {
                if v_isShared_909_ == 0 {
                    v___x_911_ = v___x_908_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
                    v___x_911_ = v_reuseFailAlloc_912_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_911_;
            }
            16 => {
                v_ref_925_ = crate::leanh::lean_ctor_get(v_a_804_, 5);
                v___x_926_ = lean_io_error_to_string(v_a_921_);
                if v_isShared_839_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_838_, 3);
                    crate::leanh::lean_ctor_set(v___x_838_, 0, v___x_926_);
                    v___x_928_ = v___x_838_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_926_);
                    v___x_928_ = v_reuseFailAlloc_934_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
                crate::leanh::lean_inc(v_ref_925_);
                v___x_930_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_930_, 0, v_ref_925_);
                crate::leanh::lean_ctor_set(v___x_930_, 1, v___x_929_);
                if v_isShared_924_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_930_);
                    v___x_932_ = v___x_923_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
                    v___x_932_ = v_reuseFailAlloc_933_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(
    mut v_optionPrefix_938_: *mut crate::leanh::LeanObject,
    mut v_opts_939_: *mut crate::leanh::LeanObject,
    mut v_item_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
    mut v_a_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(
        v_optionPrefix_938_,
        v_opts_939_,
        v_item_940_,
        v_a_941_,
        v_a_942_,
        v_a_943_,
        v_a_944_,
        v_a_945_,
        v_a_946_,
    );
    crate::leanh::lean_dec(v_a_946_);
    crate::leanh::lean_dec_ref(v_a_945_);
    crate::leanh::lean_dec(v_a_944_);
    crate::leanh::lean_dec_ref(v_a_943_);
    crate::leanh::lean_dec(v_a_942_);
    crate::leanh::lean_dec_ref(v_a_941_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(
    mut v_t_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
    mut v___y_952_: *mut crate::leanh::LeanObject,
    mut v___y_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_949_, v___y_955_);
    return v___x_957_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(
    mut v_t_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(v_t_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
    crate::leanh::lean_dec(v___y_964_);
    crate::leanh::lean_dec_ref(v___y_963_);
    crate::leanh::lean_dec(v___y_962_);
    crate::leanh::lean_dec_ref(v___y_961_);
    crate::leanh::lean_dec(v___y_960_);
    crate::leanh::lean_dec_ref(v___y_959_);
    return v_res_966_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(
    mut v_00_u03b1_967_: *mut crate::leanh::LeanObject,
    mut v_ref_968_: *mut crate::leanh::LeanObject,
    mut v_msg_969_: *mut crate::leanh::LeanObject,
    mut v___y_970_: *mut crate::leanh::LeanObject,
    mut v___y_971_: *mut crate::leanh::LeanObject,
    mut v___y_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_977_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_968_, v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
    return v___x_977_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(
    mut v_00_u03b1_978_: *mut crate::leanh::LeanObject,
    mut v_ref_979_: *mut crate::leanh::LeanObject,
    mut v_msg_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(
            v_00_u03b1_978_,
            v_ref_979_,
            v_msg_980_,
            v___y_981_,
            v___y_982_,
            v___y_983_,
            v___y_984_,
            v___y_985_,
            v___y_986_,
        );
    crate::leanh::lean_dec(v___y_986_);
    crate::leanh::lean_dec_ref(v___y_985_);
    crate::leanh::lean_dec(v___y_984_);
    crate::leanh::lean_dec_ref(v___y_983_);
    crate::leanh::lean_dec(v___y_982_);
    crate::leanh::lean_dec_ref(v___y_981_);
    crate::leanh::lean_dec(v_ref_979_);
    return v_res_988_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(
    mut v_00_u03b1_989_: *mut crate::leanh::LeanObject,
    mut v_msg_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
    return v___x_998_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(
    mut v_00_u03b1_999_: *mut crate::leanh::LeanObject,
    mut v_msg_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(v_00_u03b1_999_, v_msg_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
    crate::leanh::lean_dec(v___y_1006_);
    crate::leanh::lean_dec_ref(v___y_1005_);
    crate::leanh::lean_dec(v___y_1004_);
    crate::leanh::lean_dec_ref(v___y_1003_);
    crate::leanh::lean_dec(v___y_1002_);
    crate::leanh::lean_dec_ref(v___y_1001_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(
    mut v_msgData_1009_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: *mut crate::leanh::LeanObject,
    mut v___y_1014_: *mut crate::leanh::LeanObject,
    mut v___y_1015_: *mut crate::leanh::LeanObject,
    mut v___y_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_1009_, v_macroStack_1010_, v___y_1015_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(
    mut v_msgData_1019_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(v_msgData_1019_, v_macroStack_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
    crate::leanh::lean_dec(v___y_1026_);
    crate::leanh::lean_dec_ref(v___y_1025_);
    crate::leanh::lean_dec(v___y_1024_);
    crate::leanh::lean_dec_ref(v___y_1023_);
    crate::leanh::lean_dec(v___y_1022_);
    crate::leanh::lean_dec_ref(v___y_1021_);
    return v_res_1028_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Extra(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Extra(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Extra(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Extra(builtin);
}

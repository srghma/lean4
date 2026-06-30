// Lean compiler output
// Module: Lean.Meta.Tactic.AuxLemma
// Imports: Lean.AddDecl Lean.DefEqAttrib
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_expr_eqv, lean_name_eq, lean_nat_add,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_mix_hash,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::CoreM::l_Lean_DeclNameGenerator_mkUniqueName;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DefEqAttrib::{
    initialize_Lean_DefEqAttrib, l_Lean_defeqAttr, l_Lean_inferDefEqAttr,
    runtime_initialize_Lean_DefEqAttrib,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_asyncMayModify___redArg, l_Lean_EnvExtension_modifyState___redArg,
    l_Lean_Environment_asyncPrefix_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_hasUnsafe, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hash;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
pub static l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instBEqAuxLemmaKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instBEqAuxLemmaKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instHashableAuxLemmaKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instHashableAuxLemmaKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedAuxLemmas_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedAuxLemmas: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_auxLemmasExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4_value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 112, 114, 101, 115, 101, 110, 116, 32, 97, 115, 121, 110, 99, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkAuxLemma___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [95, 112, 114, 111, 111, 102, 0],
    };
static mut l_Lean_Meta_mkAuxLemma___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkAuxLemma___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkAuxLemma___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkAuxLemma___closed__0_value)
                as *mut leanh::LeanObject,
            18080288155440783478 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkAuxLemma___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkAuxLemma___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_instBEqAuxLemmaKey_beq(
    mut v_x_993_: *mut leanh::LeanObject,
    mut v_x_994_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_type_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_996_: u8 = 0;
    let mut v_defeq_997_: u8 = 0;
    let mut v_type_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_999_: u8 = 0;
    let mut v_defeq_1000_: u8 = 0;
    let mut v___y_1002_: u8 = 0;
    let mut v___x_1003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_995_ = leanh::lean_ctor_get(v_x_993_, 0);
                v_isPrivate_996_ = leanh::lean_ctor_get_uint8(
                    v_x_993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_defeq_997_ = leanh::lean_ctor_get_uint8(
                    v_x_993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_type_998_ = leanh::lean_ctor_get(v_x_994_, 0);
                v_isPrivate_999_ = leanh::lean_ctor_get_uint8(
                    v_x_994_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_defeq_1000_ = leanh::lean_ctor_get_uint8(
                    v_x_994_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v___x_1003_ = lean_expr_eqv(v_type_995_, v_type_998_);
                if v___x_1003_ == 0 {
                    return v___x_1003_;
                } else {
                    if v_isPrivate_996_ == 0 {
                        if v_isPrivate_999_ == 0 {
                            v___y_1002_ = v___x_1003_;
                            state = 1;
                            continue;
                        } else {
                            return v_isPrivate_996_;
                        }
                    } else {
                        v___y_1002_ = v_isPrivate_999_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1002_ == 0 {
                    return v___y_1002_;
                } else {
                    if v_defeq_997_ == 0 {
                        if v_defeq_1000_ == 0 {
                            return v___y_1002_;
                        } else {
                            return v_defeq_997_;
                        }
                    } else {
                        return v_defeq_1000_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(
    mut v_x_1004_: *mut leanh::LeanObject,
    mut v_x_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1006_: u8 = 0;
    let mut v_r_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_1004_, v_x_1005_);
    leanh::lean_dec_ref(v_x_1005_);
    leanh::lean_dec_ref(v_x_1004_);
    v_r_1007_ = leanh::lean_box((v_res_1006_) as usize);
    return v_r_1007_;
}
pub unsafe fn l_Lean_Meta_instHashableAuxLemmaKey_hash(
    mut v_x_1010_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_type_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_1012_: u8 = 0;
    let mut v_defeq_1013_: u8 = 0;
    let mut v___x_1014_: u64 = 0;
    let mut v___x_1015_: u64 = 0;
    let mut v___x_1016_: u64 = 0;
    let mut v___y_1018_: u64 = 0;
    let mut v___x_1019_: u64 = 0;
    let mut v___x_1020_: u64 = 0;
    let mut v___x_1021_: u64 = 0;
    let mut v___x_1022_: u64 = 0;
    let mut v___x_1023_: u64 = 0;
    let mut v___x_1024_: u64 = 0;
    let mut v___x_1025_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_1011_ = leanh::lean_ctor_get(v_x_1010_, 0);
                v_isPrivate_1012_ = leanh::lean_ctor_get_uint8(
                    v_x_1010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_defeq_1013_ = leanh::lean_ctor_get_uint8(
                    v_x_1010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v___x_1014_ = 0u64;
                v___x_1015_ = l_Lean_Expr_hash(v_type_1011_);
                v___x_1016_ = lean_uint64_mix_hash(v___x_1014_, v___x_1015_);
                if v_isPrivate_1012_ == 0 {
                    v___x_1024_ = 13u64;
                    v___y_1018_ = v___x_1024_;
                    state = 1;
                    continue;
                } else {
                    v___x_1025_ = 11u64;
                    v___y_1018_ = v___x_1025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1019_ = lean_uint64_mix_hash(v___x_1016_, v___y_1018_);
                if v_defeq_1013_ == 0 {
                    v___x_1020_ = 13u64;
                    v___x_1021_ = lean_uint64_mix_hash(v___x_1019_, v___x_1020_);
                    return v___x_1021_;
                } else {
                    v___x_1022_ = 11u64;
                    v___x_1023_ = lean_uint64_mix_hash(v___x_1019_, v___x_1022_);
                    return v___x_1023_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(
    mut v_x_1026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1027_: u64 = 0;
    let mut v_r_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_1026_);
    leanh::lean_dec_ref(v_x_1026_);
    v_r_1028_ = leanh::lean_box_uint64(v_res_1027_);
    return v_r_1028_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1031_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0,
    );
    v___x_1033_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1033_, 0, v___x_1032_);
    return v___x_1033_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedAuxLemmas_default() -> *mut leanh::LeanObject {
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1,
    );
    return v___x_1034_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedAuxLemmas() -> *mut leanh::LeanObject {
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
    return v___x_1035_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(
    mut v___x_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1038_, 0, v___x_1036_);
    return v___x_1038_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(
    mut v___x_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(v___x_1039_);
    return v_res_1041_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1,
    );
    v___f_1043_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_1043_, 0, v___x_1042_);
    return v___f_1043_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1045_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
    v___x_1046_ = leanh::lean_box(0);
    v___x_1047_ = leanh::lean_box(1);
    v___x_1048_ = l_Lean_registerEnvExtension___redArg(v___f_1045_, v___x_1046_, v___x_1047_);
    return v___x_1048_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(
    mut v_a_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
    return v_res_1050_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(
    mut v_kind_1051_: *mut leanh::LeanObject,
    mut v___y_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1072_: u8 = 0;
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1078_: u8 = 0;
    let mut v_unused_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1054_ = lean_st_ref_get(v___y_1052_);
                v_auxDeclNGen_1055_ = leanh::lean_ctor_get(v___x_1054_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_1055_);
                leanh::lean_dec(v___x_1054_);
                v___x_1056_ = lean_st_ref_get(v___y_1052_);
                v_env_1057_ = leanh::lean_ctor_get(v___x_1056_, 0);
                leanh::lean_inc_ref(v_env_1057_);
                leanh::lean_dec(v___x_1056_);
                v___x_1058_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_1057_,
                    v_auxDeclNGen_1055_,
                    v_kind_1051_,
                );
                v_fst_1059_ = leanh::lean_ctor_get(v___x_1058_, 0);
                leanh::lean_inc(v_fst_1059_);
                v_snd_1060_ = leanh::lean_ctor_get(v___x_1058_, 1);
                leanh::lean_inc(v_snd_1060_);
                leanh::lean_dec_ref(v___x_1058_);
                v___x_1061_ = lean_st_ref_take(v___y_1052_);
                v_env_1062_ = leanh::lean_ctor_get(v___x_1061_, 0);
                v_nextMacroScope_1063_ = leanh::lean_ctor_get(v___x_1061_, 1);
                v_ngen_1064_ = leanh::lean_ctor_get(v___x_1061_, 2);
                v_traceState_1065_ = leanh::lean_ctor_get(v___x_1061_, 4);
                v_cache_1066_ = leanh::lean_ctor_get(v___x_1061_, 5);
                v_messages_1067_ = leanh::lean_ctor_get(v___x_1061_, 6);
                v_infoState_1068_ = leanh::lean_ctor_get(v___x_1061_, 7);
                v_snapshotTasks_1069_ = leanh::lean_ctor_get(v___x_1061_, 8);
                v_isSharedCheck_1078_ = (!leanh::lean_is_exclusive(v___x_1061_)) as u8;
                if v_isSharedCheck_1078_ == 0 {
                    v_unused_1079_ = leanh::lean_ctor_get(v___x_1061_, 3);
                    leanh::lean_dec(v_unused_1079_);
                    v___x_1071_ = v___x_1061_;
                    v_isShared_1072_ = v_isSharedCheck_1078_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1069_);
                    leanh::lean_inc(v_infoState_1068_);
                    leanh::lean_inc(v_messages_1067_);
                    leanh::lean_inc(v_cache_1066_);
                    leanh::lean_inc(v_traceState_1065_);
                    leanh::lean_inc(v_ngen_1064_);
                    leanh::lean_inc(v_nextMacroScope_1063_);
                    leanh::lean_inc(v_env_1062_);
                    leanh::lean_dec(v___x_1061_);
                    v___x_1071_ = leanh::lean_box(0);
                    v_isShared_1072_ = v_isSharedCheck_1078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1072_ == 0 {
                    leanh::lean_ctor_set(v___x_1071_, 3, v_snd_1060_);
                    v___x_1074_ = v___x_1071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_env_1062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_nextMacroScope_1063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_ngen_1064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_snd_1060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_traceState_1065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 5, v_cache_1066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 6, v_messages_1067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 7, v_infoState_1068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 8, v_snapshotTasks_1069_);
                    v___x_1074_ = v_reuseFailAlloc_1077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1075_ = lean_st_ref_set(v___y_1052_, v___x_1074_);
                v___x_1076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1076_, 0, v_fst_1059_);
                return v___x_1076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(
    mut v_kind_1080_: *mut leanh::LeanObject,
    mut v___y_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(
        v_kind_1080_,
        v___y_1081_,
    );
    leanh::lean_dec(v___y_1081_);
    return v_res_1083_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(
    mut v_kind_1084_: *mut leanh::LeanObject,
    mut v___y_1085_: *mut leanh::LeanObject,
    mut v___y_1086_: *mut leanh::LeanObject,
    mut v___y_1087_: *mut leanh::LeanObject,
    mut v___y_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(
        v_kind_1084_,
        v___y_1088_,
    );
    return v___x_1090_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(
    mut v_kind_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
    mut v___y_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(
        v_kind_1091_,
        v___y_1092_,
        v___y_1093_,
        v___y_1094_,
        v___y_1095_,
    );
    leanh::lean_dec(v___y_1095_);
    leanh::lean_dec_ref(v___y_1094_);
    leanh::lean_dec(v___y_1093_);
    leanh::lean_dec_ref(v___y_1092_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(
    mut v_x_1098_: *mut leanh::LeanObject,
    mut v_x_1099_: *mut leanh::LeanObject,
    mut v_x_1100_: *mut leanh::LeanObject,
    mut v_x_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1102_ = leanh::lean_ctor_get(v_x_1098_, 0);
                v_vs_1103_ = leanh::lean_ctor_get(v_x_1098_, 1);
                v_isSharedCheck_1127_ = (!leanh::lean_is_exclusive(v_x_1098_)) as u8;
                if v_isSharedCheck_1127_ == 0 {
                    v___x_1105_ = v_x_1098_;
                    v_isShared_1106_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1103_);
                    leanh::lean_inc(v_ks_1102_);
                    leanh::lean_dec(v_x_1098_);
                    v___x_1105_ = leanh::lean_box(0);
                    v_isShared_1106_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1107_ = lean_array_get_size(v_ks_1102_);
                v___x_1108_ = lean_nat_dec_lt(v_x_1099_, v___x_1107_);
                if v___x_1108_ == 0 {
                    leanh::lean_dec(v_x_1099_);
                    v___x_1109_ = lean_array_push(v_ks_1102_, v_x_1100_);
                    v___x_1110_ = lean_array_push(v_vs_1103_, v_x_1101_);
                    if v_isShared_1106_ == 0 {
                        leanh::lean_ctor_set(v___x_1105_, 1, v___x_1110_);
                        leanh::lean_ctor_set(v___x_1105_, 0, v___x_1109_);
                        v___x_1112_ = v___x_1105_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1113_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1109_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1110_);
                        v___x_1112_ = v_reuseFailAlloc_1113_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1114_ = lean_array_fget_borrowed(v_ks_1102_, v_x_1099_);
                    v___x_1115_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_1100_, v_k_x27_1114_);
                    if v___x_1115_ == 0 {
                        if v_isShared_1106_ == 0 {
                            v___x_1117_ = v___x_1105_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1121_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_ks_1102_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_vs_1103_);
                            v___x_1117_ = v_reuseFailAlloc_1121_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1122_ = lean_array_fset(v_ks_1102_, v_x_1099_, v_x_1100_);
                        v___x_1123_ = lean_array_fset(v_vs_1103_, v_x_1099_, v_x_1101_);
                        leanh::lean_dec(v_x_1099_);
                        if v_isShared_1106_ == 0 {
                            leanh::lean_ctor_set(v___x_1105_, 1, v___x_1123_);
                            leanh::lean_ctor_set(v___x_1105_, 0, v___x_1122_);
                            v___x_1125_ = v___x_1105_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1126_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1122_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1123_);
                            v___x_1125_ = v_reuseFailAlloc_1126_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1112_;
            }
            3 => {
                v___x_1118_ = leanh::lean_unsigned_to_nat(1);
                v___x_1119_ = lean_nat_add(v_x_1099_, v___x_1118_);
                leanh::lean_dec(v_x_1099_);
                v_x_1098_ = v___x_1117_;
                v_x_1099_ = v___x_1119_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(
    mut v_n_1128_: *mut leanh::LeanObject,
    mut v_k_1129_: *mut leanh::LeanObject,
    mut v_v_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = leanh::lean_unsigned_to_nat(0);
    v___x_1132_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_1128_, v___x_1131_, v_k_1129_, v_v_1130_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1133_: usize = 0;
    let mut v___x_1134_: usize = 0;
    let mut v___x_1135_: usize = 0;
    v___x_1133_ = 5usize;
    v___x_1134_ = 1usize;
    v___x_1135_ = lean_usize_shift_left(v___x_1134_, v___x_1133_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1136_: usize = 0;
    let mut v___x_1137_: usize = 0;
    let mut v___x_1138_: usize = 0;
    v___x_1136_ = 1usize;
    v___x_1137_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
    v___x_1138_ = lean_usize_sub(v___x_1137_, v___x_1136_);
    return v___x_1138_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1139_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(
    mut v_x_1140_: *mut leanh::LeanObject,
    mut v_x_1141_: usize,
    mut v_x_1142_: usize,
    mut v_x_1143_: *mut leanh::LeanObject,
    mut v_x_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: usize = 0;
    let mut v___x_1147_: usize = 0;
    let mut v___x_1148_: usize = 0;
    let mut v___x_1149_: usize = 0;
    let mut v_j_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v_v_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1176_: u8 = 0;
    let mut v_node_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v___x_1181_: usize = 0;
    let mut v___x_1182_: usize = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1189_: u8 = 0;
    let mut v_unused_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1200_: u8 = 0;
    let mut v_ks_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v_reuseFailAlloc_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1140_) == 0 {
                    v_es_1145_ = leanh::lean_ctor_get(v_x_1140_, 0);
                    v___x_1146_ = 5usize;
                    v___x_1147_ = 1usize;
                    v___x_1148_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
                    v___x_1149_ = lean_usize_land(v_x_1141_, v___x_1148_);
                    v_j_1150_ = lean_usize_to_nat(v___x_1149_);
                    v___x_1151_ = lean_array_get_size(v_es_1145_);
                    v___x_1152_ = lean_nat_dec_lt(v_j_1150_, v___x_1151_);
                    if v___x_1152_ == 0 {
                        leanh::lean_dec(v_j_1150_);
                        leanh::lean_dec(v_x_1144_);
                        leanh::lean_dec_ref(v_x_1143_);
                        return v_x_1140_;
                    } else {
                        leanh::lean_inc_ref(v_es_1145_);
                        v_isSharedCheck_1189_ = (!leanh::lean_is_exclusive(v_x_1140_)) as u8;
                        if v_isSharedCheck_1189_ == 0 {
                            v_unused_1190_ = leanh::lean_ctor_get(v_x_1140_, 0);
                            leanh::lean_dec(v_unused_1190_);
                            v___x_1154_ = v_x_1140_;
                            v_isShared_1155_ = v_isSharedCheck_1189_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1140_);
                            v___x_1154_ = leanh::lean_box(0);
                            v_isShared_1155_ = v_isSharedCheck_1189_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1191_ = leanh::lean_ctor_get(v_x_1140_, 0);
                    v_vs_1192_ = leanh::lean_ctor_get(v_x_1140_, 1);
                    v_isSharedCheck_1212_ = (!leanh::lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1212_ == 0 {
                        v___x_1194_ = v_x_1140_;
                        v_isShared_1195_ = v_isSharedCheck_1212_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1192_);
                        leanh::lean_inc(v_ks_1191_);
                        leanh::lean_dec(v_x_1140_);
                        v___x_1194_ = leanh::lean_box(0);
                        v_isShared_1195_ = v_isSharedCheck_1212_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1156_ = lean_array_fget(v_es_1145_, v_j_1150_);
                v___x_1157_ = leanh::lean_box(0);
                v_xs_x27_1158_ = lean_array_fset(v_es_1145_, v_j_1150_, v___x_1157_);
                match leanh::lean_obj_tag(v_v_1156_) {
                    0 => {
                        v_key_1165_ = leanh::lean_ctor_get(v_v_1156_, 0);
                        v_val_1166_ = leanh::lean_ctor_get(v_v_1156_, 1);
                        v_isSharedCheck_1176_ = (!leanh::lean_is_exclusive(v_v_1156_)) as u8;
                        if v_isSharedCheck_1176_ == 0 {
                            v___x_1168_ = v_v_1156_;
                            v_isShared_1169_ = v_isSharedCheck_1176_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1166_);
                            leanh::lean_inc(v_key_1165_);
                            leanh::lean_dec(v_v_1156_);
                            v___x_1168_ = leanh::lean_box(0);
                            v_isShared_1169_ = v_isSharedCheck_1176_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1177_ = leanh::lean_ctor_get(v_v_1156_, 0);
                        v_isSharedCheck_1187_ = (!leanh::lean_is_exclusive(v_v_1156_)) as u8;
                        if v_isSharedCheck_1187_ == 0 {
                            v___x_1179_ = v_v_1156_;
                            v_isShared_1180_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1177_);
                            leanh::lean_dec(v_v_1156_);
                            v___x_1179_ = leanh::lean_box(0);
                            v_isShared_1180_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1188_, 0, v_x_1143_);
                        leanh::lean_ctor_set(v___x_1188_, 1, v_x_1144_);
                        v___y_1160_ = v___x_1188_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1161_ = lean_array_fset(v_xs_x27_1158_, v_j_1150_, v___y_1160_);
                leanh::lean_dec(v_j_1150_);
                if v_isShared_1155_ == 0 {
                    leanh::lean_ctor_set(v___x_1154_, 0, v___x_1161_);
                    v___x_1163_ = v___x_1154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
                    v___x_1163_ = v_reuseFailAlloc_1164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1163_;
            }
            4 => {
                v___x_1170_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_1143_, v_key_1165_);
                if v___x_1170_ == 0 {
                    leanh::lean_del_object(v___x_1168_);
                    v___x_1171_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1165_,
                        v_val_1166_,
                        v_x_1143_,
                        v_x_1144_,
                    );
                    v___x_1172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                    v___y_1160_ = v___x_1172_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1166_);
                    leanh::lean_dec(v_key_1165_);
                    if v_isShared_1169_ == 0 {
                        leanh::lean_ctor_set(v___x_1168_, 1, v_x_1144_);
                        leanh::lean_ctor_set(v___x_1168_, 0, v_x_1143_);
                        v___x_1174_ = v___x_1168_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1175_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_x_1143_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_x_1144_);
                        v___x_1174_ = v_reuseFailAlloc_1175_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1160_ = v___x_1174_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1181_ = lean_usize_shift_right(v_x_1141_, v___x_1146_);
                v___x_1182_ = lean_usize_add(v_x_1142_, v___x_1147_);
                v___x_1183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_1177_, v___x_1181_, v___x_1182_, v_x_1143_, v_x_1144_);
                if v_isShared_1180_ == 0 {
                    leanh::lean_ctor_set(v___x_1179_, 0, v___x_1183_);
                    v___x_1185_ = v___x_1179_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1186_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
                    v___x_1185_ = v_reuseFailAlloc_1186_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1160_ = v___x_1185_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1195_ == 0 {
                    v___x_1197_ = v___x_1194_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_ks_1191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_vs_1192_);
                    v___x_1197_ = v_reuseFailAlloc_1211_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_1197_, v_x_1143_, v_x_1144_);
                v___x_1206_ = 7usize;
                v___x_1207_ = lean_usize_dec_le(v___x_1206_, v_x_1142_);
                if v___x_1207_ == 0 {
                    v___x_1208_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1198_);
                    v___x_1209_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
                    leanh::lean_dec(v___x_1208_);
                    v___y_1200_ = v___x_1210_;
                    state = 10;
                    continue;
                } else {
                    v___y_1200_ = v___x_1207_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1200_ == 0 {
                    v_ks_1201_ = leanh::lean_ctor_get(v_newNode_1198_, 0);
                    leanh::lean_inc_ref(v_ks_1201_);
                    v_vs_1202_ = leanh::lean_ctor_get(v_newNode_1198_, 1);
                    leanh::lean_inc_ref(v_vs_1202_);
                    leanh::lean_dec_ref(v_newNode_1198_);
                    v___x_1203_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2);
                    v___x_1205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_1142_, v_ks_1201_, v_vs_1202_, v___x_1203_, v___x_1204_);
                    leanh::lean_dec_ref(v_vs_1202_);
                    leanh::lean_dec_ref(v_ks_1201_);
                    return v___x_1205_;
                } else {
                    return v_newNode_1198_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(
    mut v_depth_1213_: usize,
    mut v_keys_1214_: *mut leanh::LeanObject,
    mut v_vals_1215_: *mut leanh::LeanObject,
    mut v_i_1216_: *mut leanh::LeanObject,
    mut v_entries_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v_k_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u64 = 0;
    let mut v_h_1223_: usize = 0;
    let mut v___x_1224_: usize = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: usize = 0;
    let mut v___x_1227_: usize = 0;
    let mut v___x_1228_: usize = 0;
    let mut v_h_1229_: usize = 0;
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1218_ = lean_array_get_size(v_keys_1214_);
                v___x_1219_ = lean_nat_dec_lt(v_i_1216_, v___x_1218_);
                if v___x_1219_ == 0 {
                    leanh::lean_dec(v_i_1216_);
                    return v_entries_1217_;
                } else {
                    v_k_1220_ = lean_array_fget_borrowed(v_keys_1214_, v_i_1216_);
                    v_v_1221_ = lean_array_fget_borrowed(v_vals_1215_, v_i_1216_);
                    v___x_1222_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_1220_);
                    v_h_1223_ = lean_uint64_to_usize(v___x_1222_);
                    v___x_1224_ = 5usize;
                    v___x_1225_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1226_ = 1usize;
                    v___x_1227_ = lean_usize_sub(v_depth_1213_, v___x_1226_);
                    v___x_1228_ = lean_usize_mul(v___x_1224_, v___x_1227_);
                    v_h_1229_ = lean_usize_shift_right(v_h_1223_, v___x_1228_);
                    v___x_1230_ = lean_nat_add(v_i_1216_, v___x_1225_);
                    leanh::lean_dec(v_i_1216_);
                    leanh::lean_inc(v_v_1221_);
                    leanh::lean_inc(v_k_1220_);
                    v___x_1231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_1217_, v_h_1229_, v_depth_1213_, v_k_1220_, v_v_1221_);
                    v_i_1216_ = v___x_1230_;
                    v_entries_1217_ = v___x_1231_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_depth_1233_: *mut leanh::LeanObject,
    mut v_keys_1234_: *mut leanh::LeanObject,
    mut v_vals_1235_: *mut leanh::LeanObject,
    mut v_i_1236_: *mut leanh::LeanObject,
    mut v_entries_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1238_: usize = 0;
    let mut v_res_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1238_ = leanh::lean_unbox_usize(v_depth_1233_);
    leanh::lean_dec(v_depth_1233_);
    v_res_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_1238_, v_keys_1234_, v_vals_1235_, v_i_1236_, v_entries_1237_);
    leanh::lean_dec_ref(v_vals_1235_);
    leanh::lean_dec_ref(v_keys_1234_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(
    mut v_x_1240_: *mut leanh::LeanObject,
    mut v_x_1241_: *mut leanh::LeanObject,
    mut v_x_1242_: *mut leanh::LeanObject,
    mut v_x_1243_: *mut leanh::LeanObject,
    mut v_x_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6178__boxed_1245_: usize = 0;
    let mut v_x_6179__boxed_1246_: usize = 0;
    let mut v_res_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6178__boxed_1245_ = leanh::lean_unbox_usize(v_x_1241_);
    leanh::lean_dec(v_x_1241_);
    v_x_6179__boxed_1246_ = leanh::lean_unbox_usize(v_x_1242_);
    leanh::lean_dec(v_x_1242_);
    v_res_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_1240_, v_x_6178__boxed_1245_, v_x_6179__boxed_1246_, v_x_1243_, v_x_1244_);
    return v_res_1247_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(
    mut v_x_1248_: *mut leanh::LeanObject,
    mut v_x_1249_: *mut leanh::LeanObject,
    mut v_x_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: u64 = 0;
    let mut v___x_1252_: usize = 0;
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_1249_);
    v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
    v___x_1253_ = 1usize;
    v___x_1254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_1248_, v___x_1252_, v___x_1253_, v_x_1249_, v_x_1250_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_Meta_mkAuxLemma___lam__0(
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_levelParams_1256_: *mut leanh::LeanObject,
    mut v___x_1257_: *mut leanh::LeanObject,
    mut v_x_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1259_, 0, v_a_1255_);
    leanh::lean_ctor_set(v___x_1259_, 1, v_levelParams_1256_);
    v___x_1260_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(
        v_x_1258_,
        v___x_1257_,
        v___x_1259_,
    );
    return v___x_1260_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(
    mut v_msgData_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = lean_st_ref_get(v___y_1265_);
    v_env_1268_ = leanh::lean_ctor_get(v___x_1267_, 0);
    leanh::lean_inc_ref(v_env_1268_);
    leanh::lean_dec(v___x_1267_);
    v___x_1269_ = lean_st_ref_get(v___y_1263_);
    v_mctx_1270_ = leanh::lean_ctor_get(v___x_1269_, 0);
    leanh::lean_inc_ref(v_mctx_1270_);
    leanh::lean_dec(v___x_1269_);
    v_lctx_1271_ = leanh::lean_ctor_get(v___y_1262_, 2);
    v_options_1272_ = leanh::lean_ctor_get(v___y_1264_, 2);
    leanh::lean_inc_ref(v_options_1272_);
    leanh::lean_inc_ref(v_lctx_1271_);
    v___x_1273_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1273_, 0, v_env_1268_);
    leanh::lean_ctor_set(v___x_1273_, 1, v_mctx_1270_);
    leanh::lean_ctor_set(v___x_1273_, 2, v_lctx_1271_);
    leanh::lean_ctor_set(v___x_1273_, 3, v_options_1272_);
    v___x_1274_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1274_, 0, v___x_1273_);
    leanh::lean_ctor_set(v___x_1274_, 1, v_msgData_1261_);
    v___x_1275_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(
    mut v_msgData_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
    leanh::lean_dec(v___y_1280_);
    leanh::lean_dec_ref(v___y_1279_);
    leanh::lean_dec(v___y_1278_);
    leanh::lean_dec_ref(v___y_1277_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(
    mut v_msg_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1289_ = leanh::lean_ctor_get(v___y_1286_, 5);
                v___x_1290_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
                v_a_1291_ = leanh::lean_ctor_get(v___x_1290_, 0);
                v_isSharedCheck_1299_ = (!leanh::lean_is_exclusive(v___x_1290_)) as u8;
                if v_isSharedCheck_1299_ == 0 {
                    v___x_1293_ = v___x_1290_;
                    v_isShared_1294_ = v_isSharedCheck_1299_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1291_);
                    leanh::lean_dec(v___x_1290_);
                    v___x_1293_ = leanh::lean_box(0);
                    v_isShared_1294_ = v_isSharedCheck_1299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1289_);
                v___x_1295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1295_, 0, v_ref_1289_);
                leanh::lean_ctor_set(v___x_1295_, 1, v_a_1291_);
                if v_isShared_1294_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1293_, 1);
                    leanh::lean_ctor_set(v___x_1293_, 0, v___x_1295_);
                    v___x_1297_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
                    v___x_1297_ = v_reuseFailAlloc_1298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_msg_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
    leanh::lean_dec(v___y_1304_);
    leanh::lean_dec_ref(v___y_1303_);
    leanh::lean_dec(v___y_1302_);
    leanh::lean_dec_ref(v___y_1301_);
    return v_res_1306_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0;
    v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2;
    v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4;
    v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6;
    v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8;
    v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(
    mut v_attrName_1322_: *mut leanh::LeanObject,
    mut v_declName_1323_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_asyncPrefix_x3f_1324_) == 0 {
                    v___x_1344_ = l_Lean_MessageData_nil;
                    v___y_1331_ = v___x_1344_;
                    state = 1;
                    continue;
                } else {
                    v_val_1345_ = leanh::lean_ctor_get(v_asyncPrefix_x3f_1324_, 0);
                    leanh::lean_inc(v_val_1345_);
                    leanh::lean_dec_ref_known(v_asyncPrefix_x3f_1324_, 1);
                    v___x_1346_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
                    v___x_1347_ = l_Lean_MessageData_ofName(v_val_1345_);
                    v___x_1348_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1348_, 0, v___x_1346_);
                    leanh::lean_ctor_set(v___x_1348_, 1, v___x_1347_);
                    v___x_1349_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
                    v___x_1350_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1348_);
                    leanh::lean_ctor_set(v___x_1350_, 1, v___x_1349_);
                    v___y_1331_ = v___x_1350_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1332_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
                v___x_1333_ = l_Lean_MessageData_ofName(v_attrName_1322_);
                v___x_1334_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1334_, 0, v___x_1332_);
                leanh::lean_ctor_set(v___x_1334_, 1, v___x_1333_);
                v___x_1335_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
                v___x_1336_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1336_, 0, v___x_1334_);
                leanh::lean_ctor_set(v___x_1336_, 1, v___x_1335_);
                v___x_1337_ = 0;
                v___x_1338_ = l_Lean_MessageData_ofConstName(v_declName_1323_, v___x_1337_);
                v___x_1339_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1339_, 0, v___x_1336_);
                leanh::lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                v___x_1340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
                v___x_1341_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1341_, 0, v___x_1339_);
                leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
                v___x_1342_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1342_, 0, v___x_1341_);
                leanh::lean_ctor_set(v___x_1342_, 1, v___y_1331_);
                v___x_1343_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_1342_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(
    mut v_attrName_1351_: *mut leanh::LeanObject,
    mut v_declName_1352_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_1351_, v_declName_1352_, v_asyncPrefix_x3f_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
    leanh::lean_dec(v___y_1357_);
    leanh::lean_dec_ref(v___y_1356_);
    leanh::lean_dec(v___y_1355_);
    leanh::lean_dec_ref(v___y_1354_);
    return v_res_1359_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0;
    v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(
    mut v_attrName_1363_: *mut leanh::LeanObject,
    mut v_declName_1364_: *mut leanh::LeanObject,
    mut v___y_1365_: *mut leanh::LeanObject,
    mut v___y_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
    v___x_1371_ = l_Lean_MessageData_ofName(v_attrName_1363_);
    v___x_1372_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1372_, 0, v___x_1370_);
    leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
    v___x_1373_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
    v___x_1374_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1374_, 0, v___x_1372_);
    leanh::lean_ctor_set(v___x_1374_, 1, v___x_1373_);
    v___x_1375_ = 0;
    v___x_1376_ = l_Lean_MessageData_ofConstName(v_declName_1364_, v___x_1375_);
    v___x_1377_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1374_);
    leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
    v___x_1378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
    v___x_1379_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1377_);
    leanh::lean_ctor_set(v___x_1379_, 1, v___x_1378_);
    v___x_1380_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_1379_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
    return v___x_1380_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(
    mut v_attrName_1381_: *mut leanh::LeanObject,
    mut v_declName_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_1381_, v_declName_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
    leanh::lean_dec(v___y_1386_);
    leanh::lean_dec_ref(v___y_1385_);
    leanh::lean_dec(v___y_1384_);
    leanh::lean_dec_ref(v___y_1383_);
    return v_res_1388_;
}
pub unsafe fn _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once
        ),
        _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0,
    );
    v___x_1391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1391_, 0, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once
        ),
        _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1,
    );
    v___x_1393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1393_, 0, v___x_1392_);
    leanh::lean_ctor_set(v___x_1393_, 1, v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once
        ),
        _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1,
    );
    v___x_1395_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1395_, 0, v___x_1394_);
    leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
    leanh::lean_ctor_set(v___x_1395_, 2, v___x_1394_);
    leanh::lean_ctor_set(v___x_1395_, 3, v___x_1394_);
    leanh::lean_ctor_set(v___x_1395_, 4, v___x_1394_);
    leanh::lean_ctor_set(v___x_1395_, 5, v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(
    mut v_attr_1396_: *mut leanh::LeanObject,
    mut v_decl_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1419_: u8 = 0;
    let mut v_asyncMode_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1441_: u8 = 0;
    let mut v_unused_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1444_: u8 = 0;
    let mut v_unused_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v_toAttributeImplCore_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1446_ = lean_st_ref_get(v___y_1401_);
                v_env_1447_ = leanh::lean_ctor_get(v___x_1446_, 0);
                leanh::lean_inc_ref(v_env_1447_);
                leanh::lean_dec(v___x_1446_);
                v___x_1462_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1447_, v_decl_1397_);
                if leanh::lean_obj_tag(v___x_1462_) == 0 {
                    v___y_1449_ = v___y_1398_;
                    v___y_1450_ = v___y_1399_;
                    v___y_1451_ = v___y_1400_;
                    v___y_1452_ = v___y_1401_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_1462_, 1);
                    leanh::lean_dec_ref(v_env_1447_);
                    v_attr_1463_ = leanh::lean_ctor_get(v_attr_1396_, 0);
                    leanh::lean_inc_ref(v_attr_1463_);
                    leanh::lean_dec_ref(v_attr_1396_);
                    v_toAttributeImplCore_1464_ = leanh::lean_ctor_get(v_attr_1463_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_1464_);
                    leanh::lean_dec_ref(v_attr_1463_);
                    v_name_1465_ = leanh::lean_ctor_get(v_toAttributeImplCore_1464_, 1);
                    leanh::lean_inc(v_name_1465_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_1464_);
                    v___x_1466_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_1465_, v_decl_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
                    return v___x_1466_;
                }
            }
            1 => {
                v___x_1406_ = lean_st_ref_take(v___y_1405_);
                v_ext_1407_ = leanh::lean_ctor_get(v_attr_1396_, 1);
                leanh::lean_inc_ref(v_ext_1407_);
                leanh::lean_dec_ref(v_attr_1396_);
                v_toEnvExtension_1408_ = leanh::lean_ctor_get(v_ext_1407_, 0);
                v_env_1409_ = leanh::lean_ctor_get(v___x_1406_, 0);
                v_nextMacroScope_1410_ = leanh::lean_ctor_get(v___x_1406_, 1);
                v_ngen_1411_ = leanh::lean_ctor_get(v___x_1406_, 2);
                v_auxDeclNGen_1412_ = leanh::lean_ctor_get(v___x_1406_, 3);
                v_traceState_1413_ = leanh::lean_ctor_get(v___x_1406_, 4);
                v_messages_1414_ = leanh::lean_ctor_get(v___x_1406_, 6);
                v_infoState_1415_ = leanh::lean_ctor_get(v___x_1406_, 7);
                v_snapshotTasks_1416_ = leanh::lean_ctor_get(v___x_1406_, 8);
                v_isSharedCheck_1444_ = (!leanh::lean_is_exclusive(v___x_1406_)) as u8;
                if v_isSharedCheck_1444_ == 0 {
                    v_unused_1445_ = leanh::lean_ctor_get(v___x_1406_, 5);
                    leanh::lean_dec(v_unused_1445_);
                    v___x_1418_ = v___x_1406_;
                    v_isShared_1419_ = v_isSharedCheck_1444_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1416_);
                    leanh::lean_inc(v_infoState_1415_);
                    leanh::lean_inc(v_messages_1414_);
                    leanh::lean_inc(v_traceState_1413_);
                    leanh::lean_inc(v_auxDeclNGen_1412_);
                    leanh::lean_inc(v_ngen_1411_);
                    leanh::lean_inc(v_nextMacroScope_1410_);
                    leanh::lean_inc(v_env_1409_);
                    leanh::lean_dec(v___x_1406_);
                    v___x_1418_ = leanh::lean_box(0);
                    v_isShared_1419_ = v_isSharedCheck_1444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_1420_ = leanh::lean_ctor_get(v_toEnvExtension_1408_, 2);
                leanh::lean_inc(v_asyncMode_1420_);
                leanh::lean_inc(v_decl_1397_);
                v___x_1421_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_1407_,
                    v_env_1409_,
                    v_decl_1397_,
                    v_asyncMode_1420_,
                    v_decl_1397_,
                );
                leanh::lean_dec(v_asyncMode_1420_);
                v___x_1422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
                if v_isShared_1419_ == 0 {
                    leanh::lean_ctor_set(v___x_1418_, 5, v___x_1422_);
                    leanh::lean_ctor_set(v___x_1418_, 0, v___x_1421_);
                    v___x_1424_ = v___x_1418_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_nextMacroScope_1410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_ngen_1411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_auxDeclNGen_1412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_traceState_1413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 5, v___x_1422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 6, v_messages_1414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 7, v_infoState_1415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 8, v_snapshotTasks_1416_);
                    v___x_1424_ = v_reuseFailAlloc_1443_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1425_ = lean_st_ref_set(v___y_1405_, v___x_1424_);
                v___x_1426_ = lean_st_ref_take(v___y_1404_);
                v_mctx_1427_ = leanh::lean_ctor_get(v___x_1426_, 0);
                v_zetaDeltaFVarIds_1428_ = leanh::lean_ctor_get(v___x_1426_, 2);
                v_postponed_1429_ = leanh::lean_ctor_get(v___x_1426_, 3);
                v_diag_1430_ = leanh::lean_ctor_get(v___x_1426_, 4);
                v_isSharedCheck_1441_ = (!leanh::lean_is_exclusive(v___x_1426_)) as u8;
                if v_isSharedCheck_1441_ == 0 {
                    v_unused_1442_ = leanh::lean_ctor_get(v___x_1426_, 1);
                    leanh::lean_dec(v_unused_1442_);
                    v___x_1432_ = v___x_1426_;
                    v_isShared_1433_ = v_isSharedCheck_1441_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1430_);
                    leanh::lean_inc(v_postponed_1429_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1428_);
                    leanh::lean_inc(v_mctx_1427_);
                    leanh::lean_dec(v___x_1426_);
                    v___x_1432_ = leanh::lean_box(0);
                    v_isShared_1433_ = v_isSharedCheck_1441_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
                if v_isShared_1433_ == 0 {
                    leanh::lean_ctor_set(v___x_1432_, 1, v___x_1434_);
                    v___x_1436_ = v___x_1432_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1440_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_mctx_1427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1434_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1440_,
                        2,
                        v_zetaDeltaFVarIds_1428_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_postponed_1429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_diag_1430_);
                    v___x_1436_ = v_reuseFailAlloc_1440_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1437_ = lean_st_ref_set(v___y_1404_, v___x_1436_);
                v___x_1438_ = leanh::lean_box(0);
                v___x_1439_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
                return v___x_1439_;
            }
            6 => {
                v_ext_1453_ = leanh::lean_ctor_get(v_attr_1396_, 1);
                v_toEnvExtension_1454_ = leanh::lean_ctor_get(v_ext_1453_, 0);
                v_attr_1455_ = leanh::lean_ctor_get(v_attr_1396_, 0);
                v_asyncMode_1456_ = leanh::lean_ctor_get(v_toEnvExtension_1454_, 2);
                leanh::lean_inc(v_decl_1397_);
                leanh::lean_inc_ref(v_env_1447_);
                v___x_1457_ = l_Lean_EnvExtension_asyncMayModify___redArg(
                    v_env_1447_,
                    v_decl_1397_,
                    v_asyncMode_1456_,
                );
                if v___x_1457_ == 0 {
                    leanh::lean_inc_ref(v_attr_1455_);
                    leanh::lean_dec_ref(v_attr_1396_);
                    v_toAttributeImplCore_1458_ = leanh::lean_ctor_get(v_attr_1455_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_1458_);
                    leanh::lean_dec_ref(v_attr_1455_);
                    v_name_1459_ = leanh::lean_ctor_get(v_toAttributeImplCore_1458_, 1);
                    leanh::lean_inc(v_name_1459_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_1458_);
                    v___x_1460_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1447_);
                    v___x_1461_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_1459_, v_decl_1397_, v___x_1460_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
                    return v___x_1461_;
                } else {
                    leanh::lean_dec_ref(v_env_1447_);
                    v___y_1404_ = v___y_1450_;
                    v___y_1405_ = v___y_1452_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(
    mut v_attr_1467_: *mut leanh::LeanObject,
    mut v_decl_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(
        v_attr_1467_,
        v_decl_1468_,
        v___y_1469_,
        v___y_1470_,
        v___y_1471_,
        v___y_1472_,
    );
    leanh::lean_dec(v___y_1472_);
    leanh::lean_dec_ref(v___y_1471_);
    leanh::lean_dec(v___y_1470_);
    leanh::lean_dec_ref(v___y_1469_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(
    mut v_keys_1475_: *mut leanh::LeanObject,
    mut v_vals_1476_: *mut leanh::LeanObject,
    mut v_i_1477_: *mut leanh::LeanObject,
    mut v_k_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = lean_array_get_size(v_keys_1475_);
                v___x_1480_ = lean_nat_dec_lt(v_i_1477_, v___x_1479_);
                if v___x_1480_ == 0 {
                    leanh::lean_dec(v_i_1477_);
                    v___x_1481_ = leanh::lean_box(0);
                    return v___x_1481_;
                } else {
                    v_k_x27_1482_ = lean_array_fget_borrowed(v_keys_1475_, v_i_1477_);
                    v___x_1483_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_1478_, v_k_x27_1482_);
                    if v___x_1483_ == 0 {
                        v___x_1484_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1485_ = lean_nat_add(v_i_1477_, v___x_1484_);
                        leanh::lean_dec(v_i_1477_);
                        v_i_1477_ = v___x_1485_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1487_ = lean_array_fget_borrowed(v_vals_1476_, v_i_1477_);
                        leanh::lean_dec(v_i_1477_);
                        leanh::lean_inc(v___x_1487_);
                        v___x_1488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                        return v___x_1488_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_keys_1489_: *mut leanh::LeanObject,
    mut v_vals_1490_: *mut leanh::LeanObject,
    mut v_i_1491_: *mut leanh::LeanObject,
    mut v_k_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1493_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_1489_, v_vals_1490_, v_i_1491_, v_k_1492_);
    leanh::lean_dec_ref(v_k_1492_);
    leanh::lean_dec_ref(v_vals_1490_);
    leanh::lean_dec_ref(v_keys_1489_);
    return v_res_1493_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(
    mut v_x_1494_: *mut leanh::LeanObject,
    mut v_x_1495_: usize,
    mut v_x_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: usize = 0;
    let mut v___x_1500_: usize = 0;
    let mut v___x_1501_: usize = 0;
    let mut v_j_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: usize = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1494_) == 0 {
                    v_es_1497_ = leanh::lean_ctor_get(v_x_1494_, 0);
                    v___x_1498_ = leanh::lean_box(2);
                    v___x_1499_ = 5usize;
                    v___x_1500_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
                    v___x_1501_ = lean_usize_land(v_x_1495_, v___x_1500_);
                    v_j_1502_ = lean_usize_to_nat(v___x_1501_);
                    v___x_1503_ = lean_array_get_borrowed(v___x_1498_, v_es_1497_, v_j_1502_);
                    leanh::lean_dec(v_j_1502_);
                    match leanh::lean_obj_tag(v___x_1503_) {
                        0 => {
                            v_key_1504_ = leanh::lean_ctor_get(v___x_1503_, 0);
                            v_val_1505_ = leanh::lean_ctor_get(v___x_1503_, 1);
                            v___x_1506_ =
                                l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_1496_, v_key_1504_);
                            if v___x_1506_ == 0 {
                                v___x_1507_ = leanh::lean_box(0);
                                return v___x_1507_;
                            } else {
                                leanh::lean_inc(v_val_1505_);
                                v___x_1508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1508_, 0, v_val_1505_);
                                return v___x_1508_;
                            }
                        }
                        1 => {
                            v_node_1509_ = leanh::lean_ctor_get(v___x_1503_, 0);
                            v___x_1510_ = lean_usize_shift_right(v_x_1495_, v___x_1499_);
                            v_x_1494_ = v_node_1509_;
                            v_x_1495_ = v___x_1510_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1512_ = leanh::lean_box(0);
                            return v___x_1512_;
                        }
                    }
                } else {
                    v_ks_1513_ = leanh::lean_ctor_get(v_x_1494_, 0);
                    v_vs_1514_ = leanh::lean_ctor_get(v_x_1494_, 1);
                    v___x_1515_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1516_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_1513_, v_vs_1514_, v___x_1515_, v_x_1496_);
                    return v___x_1516_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(
    mut v_x_1517_: *mut leanh::LeanObject,
    mut v_x_1518_: *mut leanh::LeanObject,
    mut v_x_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6733__boxed_1520_: usize = 0;
    let mut v_res_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6733__boxed_1520_ = leanh::lean_unbox_usize(v_x_1518_);
    leanh::lean_dec(v_x_1518_);
    v_res_1521_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_1517_, v_x_6733__boxed_1520_, v_x_1519_);
    leanh::lean_dec_ref(v_x_1519_);
    leanh::lean_dec_ref(v_x_1517_);
    return v_res_1521_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(
    mut v_x_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: u64 = 0;
    let mut v___x_1525_: usize = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_1523_);
    v___x_1525_ = lean_uint64_to_usize(v___x_1524_);
    v___x_1526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_1522_, v___x_1525_, v_x_1523_);
    return v___x_1526_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(
        v_x_1527_, v_x_1528_,
    );
    leanh::lean_dec_ref(v_x_1528_);
    leanh::lean_dec_ref(v_x_1527_);
    return v_res_1529_;
}
pub unsafe fn l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(
    mut v_x_1530_: *mut leanh::LeanObject,
    mut v_x_1531_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: u8 = 0;
    let mut v_head_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1530_) == 0 {
                    if leanh::lean_obj_tag(v_x_1531_) == 0 {
                        v___x_1532_ = 1;
                        return v___x_1532_;
                    } else {
                        v___x_1533_ = 0;
                        return v___x_1533_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_1531_) == 0 {
                        v___x_1534_ = 0;
                        return v___x_1534_;
                    } else {
                        v_head_1535_ = leanh::lean_ctor_get(v_x_1530_, 0);
                        v_tail_1536_ = leanh::lean_ctor_get(v_x_1530_, 1);
                        v_head_1537_ = leanh::lean_ctor_get(v_x_1531_, 0);
                        v_tail_1538_ = leanh::lean_ctor_get(v_x_1531_, 1);
                        v___x_1539_ = lean_name_eq(v_head_1535_, v_head_1537_);
                        if v___x_1539_ == 0 {
                            return v___x_1539_;
                        } else {
                            v_x_1530_ = v_tail_1536_;
                            v_x_1531_ = v_tail_1538_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(
    mut v_x_1541_: *mut leanh::LeanObject,
    mut v_x_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1543_: u8 = 0;
    let mut v_r_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_1541_, v_x_1542_);
    leanh::lean_dec(v_x_1542_);
    leanh::lean_dec(v_x_1541_);
    v_r_1544_ = leanh::lean_box((v_res_1543_) as usize);
    return v_r_1544_;
}
pub unsafe fn l_Lean_Meta_mkAuxLemma(
    mut v_levelParams_1548_: *mut leanh::LeanObject,
    mut v_type_1549_: *mut leanh::LeanObject,
    mut v_value_1550_: *mut leanh::LeanObject,
    mut v_kind_x3f_1551_: *mut leanh::LeanObject,
    mut v_cache_1552_: u8,
    mut v_inferRfl_1553_: u8,
    mut v_forceExpose_1554_: u8,
    mut v_defeq_1555_: u8,
    mut v_a_1556_: *mut leanh::LeanObject,
    mut v_a_1557_: *mut leanh::LeanObject,
    mut v_a_1558_: *mut leanh::LeanObject,
    mut v_a_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1565_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_unused_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v___y_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v___y_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: u8 = 0;
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: u8 = 0;
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_unused_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_unused_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v___y_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_a_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v___y_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: u8 = 0;
    let mut v___y_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v_fst_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v___y_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: u8 = 0;
    let mut v___y_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v_fst_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v___y_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1561_ = lean_st_ref_get(v_a_1559_);
                v_env_1562_ = leanh::lean_ctor_get(v___x_1561_, 0);
                leanh::lean_inc_ref_n(v_env_1562_, 2);
                leanh::lean_dec(v___x_1561_);
                v___x_1563_ = l_Lean_Meta_auxLemmasExt;
                v_asyncMode_1564_ = leanh::lean_ctor_get(v___x_1563_, 2);
                v_isExporting_1565_ = leanh::lean_ctor_get_uint8(
                    v_env_1562_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v___x_1566_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
                v___x_1567_ = leanh::lean_box(0);
                v___x_1780_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1566_,
                        v___x_1563_,
                        v_env_1562_,
                        v_asyncMode_1564_,
                        v___x_1567_,
                    );
                if v_isExporting_1565_ == 0 {
                    v___x_1829_ = 1;
                    v___y_1825_ = v___x_1829_;
                    state = 36;
                    continue;
                } else {
                    v___x_1830_ = 0;
                    v___y_1825_ = v___x_1830_;
                    state = 36;
                    continue;
                }
            }
            1 => {
                v___x_1573_ = lean_st_ref_take(v___y_1572_);
                v_env_1574_ = leanh::lean_ctor_get(v___x_1573_, 0);
                v_nextMacroScope_1575_ = leanh::lean_ctor_get(v___x_1573_, 1);
                v_ngen_1576_ = leanh::lean_ctor_get(v___x_1573_, 2);
                v_auxDeclNGen_1577_ = leanh::lean_ctor_get(v___x_1573_, 3);
                v_traceState_1578_ = leanh::lean_ctor_get(v___x_1573_, 4);
                v_messages_1579_ = leanh::lean_ctor_get(v___x_1573_, 6);
                v_infoState_1580_ = leanh::lean_ctor_get(v___x_1573_, 7);
                v_snapshotTasks_1581_ = leanh::lean_ctor_get(v___x_1573_, 8);
                v_isSharedCheck_1607_ = (!leanh::lean_is_exclusive(v___x_1573_)) as u8;
                if v_isSharedCheck_1607_ == 0 {
                    v_unused_1608_ = leanh::lean_ctor_get(v___x_1573_, 5);
                    leanh::lean_dec(v_unused_1608_);
                    v___x_1583_ = v___x_1573_;
                    v_isShared_1584_ = v_isSharedCheck_1607_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1581_);
                    leanh::lean_inc(v_infoState_1580_);
                    leanh::lean_inc(v_messages_1579_);
                    leanh::lean_inc(v_traceState_1578_);
                    leanh::lean_inc(v_auxDeclNGen_1577_);
                    leanh::lean_inc(v_ngen_1576_);
                    leanh::lean_inc(v_nextMacroScope_1575_);
                    leanh::lean_inc(v_env_1574_);
                    leanh::lean_dec(v___x_1573_);
                    v___x_1583_ = leanh::lean_box(0);
                    v_isShared_1584_ = v_isSharedCheck_1607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1585_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1563_,
                    v_env_1574_,
                    v___y_1569_,
                    v_asyncMode_1564_,
                    v___x_1567_,
                );
                v___x_1586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
                if v_isShared_1584_ == 0 {
                    leanh::lean_ctor_set(v___x_1583_, 5, v___x_1586_);
                    leanh::lean_ctor_set(v___x_1583_, 0, v___x_1585_);
                    v___x_1588_ = v___x_1583_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1585_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_nextMacroScope_1575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_ngen_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_auxDeclNGen_1577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_traceState_1578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 5, v___x_1586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_messages_1579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_infoState_1580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_snapshotTasks_1581_);
                    v___x_1588_ = v_reuseFailAlloc_1606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1589_ = lean_st_ref_set(v___y_1572_, v___x_1588_);
                v___x_1590_ = lean_st_ref_take(v___y_1571_);
                v_mctx_1591_ = leanh::lean_ctor_get(v___x_1590_, 0);
                v_zetaDeltaFVarIds_1592_ = leanh::lean_ctor_get(v___x_1590_, 2);
                v_postponed_1593_ = leanh::lean_ctor_get(v___x_1590_, 3);
                v_diag_1594_ = leanh::lean_ctor_get(v___x_1590_, 4);
                v_isSharedCheck_1604_ = (!leanh::lean_is_exclusive(v___x_1590_)) as u8;
                if v_isSharedCheck_1604_ == 0 {
                    v_unused_1605_ = leanh::lean_ctor_get(v___x_1590_, 1);
                    leanh::lean_dec(v_unused_1605_);
                    v___x_1596_ = v___x_1590_;
                    v_isShared_1597_ = v_isSharedCheck_1604_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1594_);
                    leanh::lean_inc(v_postponed_1593_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1592_);
                    leanh::lean_inc(v_mctx_1591_);
                    leanh::lean_dec(v___x_1590_);
                    v___x_1596_ = leanh::lean_box(0);
                    v_isShared_1597_ = v_isSharedCheck_1604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
                if v_isShared_1597_ == 0 {
                    leanh::lean_ctor_set(v___x_1596_, 1, v___x_1598_);
                    v___x_1600_ = v___x_1596_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_mctx_1591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1598_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1603_,
                        2,
                        v_zetaDeltaFVarIds_1592_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_postponed_1593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_diag_1594_);
                    v___x_1600_ = v_reuseFailAlloc_1603_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1601_ = lean_st_ref_set(v___y_1571_, v___x_1600_);
                v___x_1602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1602_, 0, v___y_1570_);
                return v___x_1602_;
            }
            6 => {
                if v_inferRfl_1553_ == 0 {
                    v___y_1569_ = v___y_1610_;
                    v___y_1570_ = v___y_1611_;
                    v___y_1571_ = v___y_1613_;
                    v___y_1572_ = v___y_1615_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v___y_1611_);
                    v___x_1616_ = l_Lean_inferDefEqAttr(
                        v___y_1611_,
                        v___y_1612_,
                        v___y_1613_,
                        v___y_1614_,
                        v___y_1615_,
                    );
                    if leanh::lean_obj_tag(v___x_1616_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1616_, 1);
                        v___y_1569_ = v___y_1610_;
                        v___y_1570_ = v___y_1611_;
                        v___y_1571_ = v___y_1613_;
                        v___y_1572_ = v___y_1615_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1611_);
                        leanh::lean_dec_ref(v___y_1610_);
                        v_a_1617_ = leanh::lean_ctor_get(v___x_1616_, 0);
                        v_isSharedCheck_1624_ =
                            (!leanh::lean_is_exclusive(v___x_1616_)) as u8;
                        if v_isSharedCheck_1624_ == 0 {
                            v___x_1619_ = v___x_1616_;
                            v_isShared_1620_ = v_isSharedCheck_1624_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1617_);
                            leanh::lean_dec(v___x_1616_);
                            v___x_1619_ = leanh::lean_box(0);
                            v_isShared_1620_ = v_isSharedCheck_1624_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_1620_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
                    v___x_1622_ = v_reuseFailAlloc_1623_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1622_;
            }
            9 => {
                v___x_1633_ =
                    l_Lean_addDecl(v___y_1632_, v_forceExpose_1554_, v___y_1629_, v___y_1627_);
                if leanh::lean_obj_tag(v___x_1633_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1633_, 1);
                    if v_defeq_1555_ == 0 {
                        v___y_1610_ = v___y_1630_;
                        v___y_1611_ = v___y_1631_;
                        v___y_1612_ = v___y_1626_;
                        v___y_1613_ = v___y_1628_;
                        v___y_1614_ = v___y_1629_;
                        v___y_1615_ = v___y_1627_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1634_ = l_Lean_defeqAttr;
                        leanh::lean_inc(v___y_1631_);
                        v___x_1635_ =
                            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(
                                v___x_1634_,
                                v___y_1631_,
                                v___y_1626_,
                                v___y_1628_,
                                v___y_1629_,
                                v___y_1627_,
                            );
                        if leanh::lean_obj_tag(v___x_1635_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1635_, 1);
                            v___y_1610_ = v___y_1630_;
                            v___y_1611_ = v___y_1631_;
                            v___y_1612_ = v___y_1626_;
                            v___y_1613_ = v___y_1628_;
                            v___y_1614_ = v___y_1629_;
                            v___y_1615_ = v___y_1627_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_1631_);
                            leanh::lean_dec_ref(v___y_1630_);
                            v_a_1636_ = leanh::lean_ctor_get(v___x_1635_, 0);
                            v_isSharedCheck_1643_ =
                                (!leanh::lean_is_exclusive(v___x_1635_)) as u8;
                            if v_isSharedCheck_1643_ == 0 {
                                v___x_1638_ = v___x_1635_;
                                v_isShared_1639_ = v_isSharedCheck_1643_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1636_);
                                leanh::lean_dec(v___x_1635_);
                                v___x_1638_ = leanh::lean_box(0);
                                v_isShared_1639_ = v_isSharedCheck_1643_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1631_);
                    leanh::lean_dec_ref(v___y_1630_);
                    v_a_1644_ = leanh::lean_ctor_get(v___x_1633_, 0);
                    v_isSharedCheck_1651_ = (!leanh::lean_is_exclusive(v___x_1633_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v___x_1646_ = v___x_1633_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1644_);
                        leanh::lean_dec(v___x_1633_);
                        v___x_1646_ = leanh::lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1641_;
            }
            12 => {
                if v_isShared_1647_ == 0 {
                    v___x_1649_ = v___x_1646_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1649_;
            }
            14 => {
                if v___y_1659_ == 0 {
                    leanh::lean_inc_n(v___y_1658_, 2);
                    v___x_1660_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1660_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1660_, 1, v_levelParams_1548_);
                    leanh::lean_ctor_set(v___x_1660_, 2, v_type_1549_);
                    v___x_1661_ = leanh::lean_box(0);
                    v___x_1662_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1662_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1662_, 1, v___x_1661_);
                    v___x_1663_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1663_, 0, v___x_1660_);
                    leanh::lean_ctor_set(v___x_1663_, 1, v_value_1550_);
                    leanh::lean_ctor_set(v___x_1663_, 2, v___x_1662_);
                    v___x_1664_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
                    v___y_1626_ = v___y_1653_;
                    v___y_1627_ = v___y_1654_;
                    v___y_1628_ = v___y_1656_;
                    v___y_1629_ = v___y_1655_;
                    v___y_1630_ = v___y_1657_;
                    v___y_1631_ = v___y_1658_;
                    v___y_1632_ = v___x_1664_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc_n(v___y_1658_, 2);
                    v___x_1665_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1665_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1665_, 1, v_levelParams_1548_);
                    leanh::lean_ctor_set(v___x_1665_, 2, v_type_1549_);
                    v___x_1666_ = leanh::lean_box(0);
                    v___x_1667_ = 0;
                    v___x_1668_ = leanh::lean_box(0);
                    v___x_1669_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1669_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1669_, 1, v___x_1668_);
                    v___x_1670_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_1670_, 0, v___x_1665_);
                    leanh::lean_ctor_set(v___x_1670_, 1, v_value_1550_);
                    leanh::lean_ctor_set(v___x_1670_, 2, v___x_1666_);
                    leanh::lean_ctor_set(v___x_1670_, 3, v___x_1669_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1670_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_1667_,
                    );
                    v___x_1671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1671_, 0, v___x_1670_);
                    v___y_1626_ = v___y_1653_;
                    v___y_1627_ = v___y_1654_;
                    v___y_1628_ = v___y_1656_;
                    v___y_1629_ = v___y_1655_;
                    v___y_1630_ = v___y_1657_;
                    v___y_1631_ = v___y_1658_;
                    v___y_1632_ = v___x_1671_;
                    state = 9;
                    continue;
                }
            }
            15 => {
                v___x_1679_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(
                    v___y_1674_,
                    v___y_1678_,
                );
                v_a_1680_ = leanh::lean_ctor_get(v___x_1679_, 0);
                leanh::lean_inc_n(v_a_1680_, 2);
                leanh::lean_dec_ref(v___x_1679_);
                leanh::lean_inc(v_levelParams_1548_);
                v___f_1681_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_mkAuxLemma___lam__0 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1681_, 0, v_a_1680_);
                leanh::lean_closure_set(v___f_1681_, 1, v_levelParams_1548_);
                leanh::lean_closure_set(v___f_1681_, 2, v___y_1673_);
                leanh::lean_inc_ref(v_env_1562_);
                v___x_1682_ = l_Lean_Environment_hasUnsafe(v_env_1562_, v_type_1549_);
                if v___x_1682_ == 0 {
                    v___x_1683_ = l_Lean_Environment_hasUnsafe(v_env_1562_, v_value_1550_);
                    v___y_1653_ = v___y_1675_;
                    v___y_1654_ = v___y_1678_;
                    v___y_1655_ = v___y_1677_;
                    v___y_1656_ = v___y_1676_;
                    v___y_1657_ = v___f_1681_;
                    v___y_1658_ = v_a_1680_;
                    v___y_1659_ = v___x_1683_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_1562_);
                    v___y_1653_ = v___y_1675_;
                    v___y_1654_ = v___y_1678_;
                    v___y_1655_ = v___y_1677_;
                    v___y_1656_ = v___y_1676_;
                    v___y_1657_ = v___f_1681_;
                    v___y_1658_ = v_a_1680_;
                    v___y_1659_ = v___x_1682_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_1689_ = lean_st_ref_take(v___y_1688_);
                v_env_1690_ = leanh::lean_ctor_get(v___x_1689_, 0);
                v_nextMacroScope_1691_ = leanh::lean_ctor_get(v___x_1689_, 1);
                v_ngen_1692_ = leanh::lean_ctor_get(v___x_1689_, 2);
                v_auxDeclNGen_1693_ = leanh::lean_ctor_get(v___x_1689_, 3);
                v_traceState_1694_ = leanh::lean_ctor_get(v___x_1689_, 4);
                v_messages_1695_ = leanh::lean_ctor_get(v___x_1689_, 6);
                v_infoState_1696_ = leanh::lean_ctor_get(v___x_1689_, 7);
                v_snapshotTasks_1697_ = leanh::lean_ctor_get(v___x_1689_, 8);
                v_isSharedCheck_1723_ = (!leanh::lean_is_exclusive(v___x_1689_)) as u8;
                if v_isSharedCheck_1723_ == 0 {
                    v_unused_1724_ = leanh::lean_ctor_get(v___x_1689_, 5);
                    leanh::lean_dec(v_unused_1724_);
                    v___x_1699_ = v___x_1689_;
                    v_isShared_1700_ = v_isSharedCheck_1723_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1697_);
                    leanh::lean_inc(v_infoState_1696_);
                    leanh::lean_inc(v_messages_1695_);
                    leanh::lean_inc(v_traceState_1694_);
                    leanh::lean_inc(v_auxDeclNGen_1693_);
                    leanh::lean_inc(v_ngen_1692_);
                    leanh::lean_inc(v_nextMacroScope_1691_);
                    leanh::lean_inc(v_env_1690_);
                    leanh::lean_dec(v___x_1689_);
                    v___x_1699_ = leanh::lean_box(0);
                    v_isShared_1700_ = v_isSharedCheck_1723_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1701_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1563_,
                    v_env_1690_,
                    v___y_1685_,
                    v_asyncMode_1564_,
                    v___x_1567_,
                );
                v___x_1702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
                if v_isShared_1700_ == 0 {
                    leanh::lean_ctor_set(v___x_1699_, 5, v___x_1702_);
                    leanh::lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1704_ = v___x_1699_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_nextMacroScope_1691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_ngen_1692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_auxDeclNGen_1693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_traceState_1694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 5, v___x_1702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_messages_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_infoState_1696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_snapshotTasks_1697_);
                    v___x_1704_ = v_reuseFailAlloc_1722_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1705_ = lean_st_ref_set(v___y_1688_, v___x_1704_);
                v___x_1706_ = lean_st_ref_take(v___y_1687_);
                v_mctx_1707_ = leanh::lean_ctor_get(v___x_1706_, 0);
                v_zetaDeltaFVarIds_1708_ = leanh::lean_ctor_get(v___x_1706_, 2);
                v_postponed_1709_ = leanh::lean_ctor_get(v___x_1706_, 3);
                v_diag_1710_ = leanh::lean_ctor_get(v___x_1706_, 4);
                v_isSharedCheck_1720_ = (!leanh::lean_is_exclusive(v___x_1706_)) as u8;
                if v_isSharedCheck_1720_ == 0 {
                    v_unused_1721_ = leanh::lean_ctor_get(v___x_1706_, 1);
                    leanh::lean_dec(v_unused_1721_);
                    v___x_1712_ = v___x_1706_;
                    v_isShared_1713_ = v_isSharedCheck_1720_;
                    state = 19;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1710_);
                    leanh::lean_inc(v_postponed_1709_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1708_);
                    leanh::lean_inc(v_mctx_1707_);
                    leanh::lean_dec(v___x_1706_);
                    v___x_1712_ = leanh::lean_box(0);
                    v_isShared_1713_ = v_isSharedCheck_1720_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1714_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once), _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
                if v_isShared_1713_ == 0 {
                    leanh::lean_ctor_set(v___x_1712_, 1, v___x_1714_);
                    v___x_1716_ = v___x_1712_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_mctx_1707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1714_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1719_,
                        2,
                        v_zetaDeltaFVarIds_1708_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_postponed_1709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_diag_1710_);
                    v___x_1716_ = v_reuseFailAlloc_1719_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_1717_ = lean_st_ref_set(v___y_1687_, v___x_1716_);
                v___x_1718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1718_, 0, v___y_1686_);
                return v___x_1718_;
            }
            21 => {
                if v_inferRfl_1553_ == 0 {
                    v___y_1685_ = v___y_1726_;
                    v___y_1686_ = v___y_1727_;
                    v___y_1687_ = v___y_1729_;
                    v___y_1688_ = v___y_1731_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_inc(v___y_1727_);
                    v___x_1732_ = l_Lean_inferDefEqAttr(
                        v___y_1727_,
                        v___y_1728_,
                        v___y_1729_,
                        v___y_1730_,
                        v___y_1731_,
                    );
                    if leanh::lean_obj_tag(v___x_1732_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1732_, 1);
                        v___y_1685_ = v___y_1726_;
                        v___y_1686_ = v___y_1727_;
                        v___y_1687_ = v___y_1729_;
                        v___y_1688_ = v___y_1731_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1727_);
                        leanh::lean_dec_ref(v___y_1726_);
                        v_a_1733_ = leanh::lean_ctor_get(v___x_1732_, 0);
                        v_isSharedCheck_1740_ =
                            (!leanh::lean_is_exclusive(v___x_1732_)) as u8;
                        if v_isSharedCheck_1740_ == 0 {
                            v___x_1735_ = v___x_1732_;
                            v_isShared_1736_ = v_isSharedCheck_1740_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1733_);
                            leanh::lean_dec(v___x_1732_);
                            v___x_1735_ = leanh::lean_box(0);
                            v_isShared_1736_ = v_isSharedCheck_1740_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            22 => {
                if v_isShared_1736_ == 0 {
                    v___x_1738_ = v___x_1735_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1739_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1738_;
            }
            24 => {
                v___x_1745_ =
                    l_Lean_addDecl(v___y_1744_, v_forceExpose_1554_, v_a_1558_, v_a_1559_);
                if leanh::lean_obj_tag(v___x_1745_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1745_, 1);
                    if v_defeq_1555_ == 0 {
                        v___y_1726_ = v___y_1742_;
                        v___y_1727_ = v___y_1743_;
                        v___y_1728_ = v_a_1556_;
                        v___y_1729_ = v_a_1557_;
                        v___y_1730_ = v_a_1558_;
                        v___y_1731_ = v_a_1559_;
                        state = 21;
                        continue;
                    } else {
                        v___x_1746_ = l_Lean_defeqAttr;
                        leanh::lean_inc(v___y_1743_);
                        v___x_1747_ =
                            l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(
                                v___x_1746_,
                                v___y_1743_,
                                v_a_1556_,
                                v_a_1557_,
                                v_a_1558_,
                                v_a_1559_,
                            );
                        if leanh::lean_obj_tag(v___x_1747_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1747_, 1);
                            v___y_1726_ = v___y_1742_;
                            v___y_1727_ = v___y_1743_;
                            v___y_1728_ = v_a_1556_;
                            v___y_1729_ = v_a_1557_;
                            v___y_1730_ = v_a_1558_;
                            v___y_1731_ = v_a_1559_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_1743_);
                            leanh::lean_dec_ref(v___y_1742_);
                            v_a_1748_ = leanh::lean_ctor_get(v___x_1747_, 0);
                            v_isSharedCheck_1755_ =
                                (!leanh::lean_is_exclusive(v___x_1747_)) as u8;
                            if v_isSharedCheck_1755_ == 0 {
                                v___x_1750_ = v___x_1747_;
                                v_isShared_1751_ = v_isSharedCheck_1755_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1748_);
                                leanh::lean_dec(v___x_1747_);
                                v___x_1750_ = leanh::lean_box(0);
                                v_isShared_1751_ = v_isSharedCheck_1755_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1743_);
                    leanh::lean_dec_ref(v___y_1742_);
                    v_a_1756_ = leanh::lean_ctor_get(v___x_1745_, 0);
                    v_isSharedCheck_1763_ = (!leanh::lean_is_exclusive(v___x_1745_)) as u8;
                    if v_isSharedCheck_1763_ == 0 {
                        v___x_1758_ = v___x_1745_;
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1756_);
                        leanh::lean_dec(v___x_1745_);
                        v___x_1758_ = leanh::lean_box(0);
                        v_isShared_1759_ = v_isSharedCheck_1763_;
                        state = 27;
                        continue;
                    }
                }
            }
            25 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1753_;
            }
            27 => {
                if v_isShared_1759_ == 0 {
                    v___x_1761_ = v___x_1758_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
                    v___x_1761_ = v_reuseFailAlloc_1762_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1761_;
            }
            29 => {
                if v___y_1767_ == 0 {
                    leanh::lean_inc_n(v___y_1766_, 2);
                    v___x_1768_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1768_, 0, v___y_1766_);
                    leanh::lean_ctor_set(v___x_1768_, 1, v_levelParams_1548_);
                    leanh::lean_ctor_set(v___x_1768_, 2, v_type_1549_);
                    v___x_1769_ = leanh::lean_box(0);
                    v___x_1770_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1770_, 0, v___y_1766_);
                    leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                    v___x_1771_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1771_, 0, v___x_1768_);
                    leanh::lean_ctor_set(v___x_1771_, 1, v_value_1550_);
                    leanh::lean_ctor_set(v___x_1771_, 2, v___x_1770_);
                    v___x_1772_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                    v___y_1742_ = v___y_1765_;
                    v___y_1743_ = v___y_1766_;
                    v___y_1744_ = v___x_1772_;
                    state = 24;
                    continue;
                } else {
                    leanh::lean_inc_n(v___y_1766_, 2);
                    v___x_1773_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1773_, 0, v___y_1766_);
                    leanh::lean_ctor_set(v___x_1773_, 1, v_levelParams_1548_);
                    leanh::lean_ctor_set(v___x_1773_, 2, v_type_1549_);
                    v___x_1774_ = leanh::lean_box(0);
                    v___x_1775_ = 0;
                    v___x_1776_ = leanh::lean_box(0);
                    v___x_1777_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1777_, 0, v___y_1766_);
                    leanh::lean_ctor_set(v___x_1777_, 1, v___x_1776_);
                    v___x_1778_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1773_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_value_1550_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v___x_1774_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v___x_1777_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1778_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_1775_,
                    );
                    v___x_1779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1779_, 0, v___x_1778_);
                    v___y_1742_ = v___y_1765_;
                    v___y_1743_ = v___y_1766_;
                    v___y_1744_ = v___x_1779_;
                    state = 24;
                    continue;
                }
            }
            30 => {
                if v___y_1784_ == 0 {
                    leanh::lean_dec(v___x_1780_);
                    v___y_1673_ = v___y_1782_;
                    v___y_1674_ = v___y_1783_;
                    v___y_1675_ = v___y_1785_;
                    v___y_1676_ = v___y_1786_;
                    v___y_1677_ = v___y_1787_;
                    v___y_1678_ = v___y_1788_;
                    state = 15;
                    continue;
                } else {
                    v___x_1789_ = 0;
                    leanh::lean_inc_ref(v_type_1549_);
                    v___x_1790_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    leanh::lean_ctor_set(v___x_1790_, 0, v_type_1549_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1790_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1789_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1790_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                        v_defeq_1555_,
                    );
                    v___x_1791_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_1780_, v___x_1790_);
                    leanh::lean_dec_ref_known(v___x_1790_, 1);
                    leanh::lean_dec(v___x_1780_);
                    if leanh::lean_obj_tag(v___x_1791_) == 1 {
                        v_val_1792_ = leanh::lean_ctor_get(v___x_1791_, 0);
                        v_isSharedCheck_1802_ =
                            (!leanh::lean_is_exclusive(v___x_1791_)) as u8;
                        if v_isSharedCheck_1802_ == 0 {
                            v___x_1794_ = v___x_1791_;
                            v_isShared_1795_ = v_isSharedCheck_1802_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1792_);
                            leanh::lean_dec(v___x_1791_);
                            v___x_1794_ = leanh::lean_box(0);
                            v_isShared_1795_ = v_isSharedCheck_1802_;
                            state = 31;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1791_);
                        v___y_1673_ = v___y_1782_;
                        v___y_1674_ = v___y_1783_;
                        v___y_1675_ = v___y_1785_;
                        v___y_1676_ = v___y_1786_;
                        v___y_1677_ = v___y_1787_;
                        v___y_1678_ = v___y_1788_;
                        state = 15;
                        continue;
                    }
                }
            }
            31 => {
                v_fst_1796_ = leanh::lean_ctor_get(v_val_1792_, 0);
                leanh::lean_inc(v_fst_1796_);
                v_snd_1797_ = leanh::lean_ctor_get(v_val_1792_, 1);
                leanh::lean_inc(v_snd_1797_);
                leanh::lean_dec(v_val_1792_);
                v___x_1798_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(
                    v_levelParams_1548_,
                    v_snd_1797_,
                );
                leanh::lean_dec(v_snd_1797_);
                if v___x_1798_ == 0 {
                    leanh::lean_dec(v_fst_1796_);
                    leanh::lean_del_object(v___x_1794_);
                    v___y_1673_ = v___y_1782_;
                    v___y_1674_ = v___y_1783_;
                    v___y_1675_ = v___y_1785_;
                    v___y_1676_ = v___y_1786_;
                    v___y_1677_ = v___y_1787_;
                    v___y_1678_ = v___y_1788_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1783_);
                    leanh::lean_dec_ref(v___y_1782_);
                    leanh::lean_dec_ref(v_env_1562_);
                    leanh::lean_dec_ref(v_value_1550_);
                    leanh::lean_dec_ref(v_type_1549_);
                    leanh::lean_dec(v_levelParams_1548_);
                    if v_isShared_1795_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1794_, 0);
                        leanh::lean_ctor_set(v___x_1794_, 0, v_fst_1796_);
                        v___x_1800_ = v___x_1794_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_1801_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_fst_1796_);
                        v___x_1800_ = v_reuseFailAlloc_1801_;
                        state = 32;
                        continue;
                    }
                }
            }
            32 => {
                return v___x_1800_;
            }
            33 => {
                if v_cache_1552_ == 0 {
                    leanh::lean_dec(v___x_1780_);
                    v___x_1807_ =
                        l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(
                            v___y_1806_,
                            v_a_1559_,
                        );
                    v_a_1808_ = leanh::lean_ctor_get(v___x_1807_, 0);
                    leanh::lean_inc_n(v_a_1808_, 2);
                    leanh::lean_dec_ref(v___x_1807_);
                    leanh::lean_inc(v_levelParams_1548_);
                    v___f_1809_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_mkAuxLemma___lam__0 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1809_, 0, v_a_1808_);
                    leanh::lean_closure_set(v___f_1809_, 1, v_levelParams_1548_);
                    leanh::lean_closure_set(v___f_1809_, 2, v___y_1804_);
                    leanh::lean_inc_ref(v_env_1562_);
                    v___x_1810_ = l_Lean_Environment_hasUnsafe(v_env_1562_, v_type_1549_);
                    if v___x_1810_ == 0 {
                        v___x_1811_ = l_Lean_Environment_hasUnsafe(v_env_1562_, v_value_1550_);
                        v___y_1765_ = v___f_1809_;
                        v___y_1766_ = v_a_1808_;
                        v___y_1767_ = v___x_1811_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_env_1562_);
                        v___y_1765_ = v___f_1809_;
                        v___y_1766_ = v_a_1808_;
                        v___y_1767_ = v___x_1810_;
                        state = 29;
                        continue;
                    }
                } else {
                    v___x_1812_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_1780_, v___y_1804_);
                    if leanh::lean_obj_tag(v___x_1812_) == 1 {
                        v_val_1813_ = leanh::lean_ctor_get(v___x_1812_, 0);
                        v_isSharedCheck_1823_ =
                            (!leanh::lean_is_exclusive(v___x_1812_)) as u8;
                        if v_isSharedCheck_1823_ == 0 {
                            v___x_1815_ = v___x_1812_;
                            v_isShared_1816_ = v_isSharedCheck_1823_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1813_);
                            leanh::lean_dec(v___x_1812_);
                            v___x_1815_ = leanh::lean_box(0);
                            v_isShared_1816_ = v_isSharedCheck_1823_;
                            state = 34;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1812_);
                        v___y_1782_ = v___y_1804_;
                        v___y_1783_ = v___y_1806_;
                        v___y_1784_ = v___y_1805_;
                        v___y_1785_ = v_a_1556_;
                        v___y_1786_ = v_a_1557_;
                        v___y_1787_ = v_a_1558_;
                        v___y_1788_ = v_a_1559_;
                        state = 30;
                        continue;
                    }
                }
            }
            34 => {
                v_fst_1817_ = leanh::lean_ctor_get(v_val_1813_, 0);
                leanh::lean_inc(v_fst_1817_);
                v_snd_1818_ = leanh::lean_ctor_get(v_val_1813_, 1);
                leanh::lean_inc(v_snd_1818_);
                leanh::lean_dec(v_val_1813_);
                v___x_1819_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(
                    v_levelParams_1548_,
                    v_snd_1818_,
                );
                leanh::lean_dec(v_snd_1818_);
                if v___x_1819_ == 0 {
                    leanh::lean_dec(v_fst_1817_);
                    leanh::lean_del_object(v___x_1815_);
                    v___y_1782_ = v___y_1804_;
                    v___y_1783_ = v___y_1806_;
                    v___y_1784_ = v___y_1805_;
                    v___y_1785_ = v_a_1556_;
                    v___y_1786_ = v_a_1557_;
                    v___y_1787_ = v_a_1558_;
                    v___y_1788_ = v_a_1559_;
                    state = 30;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1806_);
                    leanh::lean_dec_ref(v___y_1804_);
                    leanh::lean_dec(v___x_1780_);
                    leanh::lean_dec_ref(v_env_1562_);
                    leanh::lean_dec_ref(v_value_1550_);
                    leanh::lean_dec_ref(v_type_1549_);
                    leanh::lean_dec(v_levelParams_1548_);
                    if v_isShared_1816_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1815_, 0);
                        leanh::lean_ctor_set(v___x_1815_, 0, v_fst_1817_);
                        v___x_1821_ = v___x_1815_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_fst_1817_);
                        v___x_1821_ = v_reuseFailAlloc_1822_;
                        state = 35;
                        continue;
                    }
                }
            }
            35 => {
                return v___x_1821_;
            }
            36 => {
                leanh::lean_inc_ref(v_type_1549_);
                v___x_1826_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v___x_1826_, 0, v_type_1549_);
                leanh::lean_ctor_set_uint8(
                    v___x_1826_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_1825_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1826_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_defeq_1555_,
                );
                if leanh::lean_obj_tag(v_kind_x3f_1551_) == 0 {
                    v___x_1827_ = l_Lean_Meta_mkAuxLemma___closed__1;
                    v___y_1804_ = v___x_1826_;
                    v___y_1805_ = v___y_1825_;
                    v___y_1806_ = v___x_1827_;
                    state = 33;
                    continue;
                } else {
                    v_val_1828_ = leanh::lean_ctor_get(v_kind_x3f_1551_, 0);
                    leanh::lean_inc(v_val_1828_);
                    leanh::lean_dec_ref_known(v_kind_x3f_1551_, 1);
                    v___y_1804_ = v___x_1826_;
                    v___y_1805_ = v___y_1825_;
                    v___y_1806_ = v_val_1828_;
                    state = 33;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkAuxLemma___boxed(
    mut v_levelParams_1831_: *mut leanh::LeanObject,
    mut v_type_1832_: *mut leanh::LeanObject,
    mut v_value_1833_: *mut leanh::LeanObject,
    mut v_kind_x3f_1834_: *mut leanh::LeanObject,
    mut v_cache_1835_: *mut leanh::LeanObject,
    mut v_inferRfl_1836_: *mut leanh::LeanObject,
    mut v_forceExpose_1837_: *mut leanh::LeanObject,
    mut v_defeq_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
    mut v_a_1842_: *mut leanh::LeanObject,
    mut v_a_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_boxed_1844_: u8 = 0;
    let mut v_inferRfl_boxed_1845_: u8 = 0;
    let mut v_forceExpose_boxed_1846_: u8 = 0;
    let mut v_defeq_boxed_1847_: u8 = 0;
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cache_boxed_1844_ = (leanh::lean_unbox(v_cache_1835_) as u8);
    v_inferRfl_boxed_1845_ = (leanh::lean_unbox(v_inferRfl_1836_) as u8);
    v_forceExpose_boxed_1846_ = (leanh::lean_unbox(v_forceExpose_1837_) as u8);
    v_defeq_boxed_1847_ = (leanh::lean_unbox(v_defeq_1838_) as u8);
    v_res_1848_ = l_Lean_Meta_mkAuxLemma(
        v_levelParams_1831_,
        v_type_1832_,
        v_value_1833_,
        v_kind_x3f_1834_,
        v_cache_boxed_1844_,
        v_inferRfl_boxed_1845_,
        v_forceExpose_boxed_1846_,
        v_defeq_boxed_1847_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
        v_a_1842_,
    );
    leanh::lean_dec(v_a_1842_);
    leanh::lean_dec_ref(v_a_1841_);
    leanh::lean_dec(v_a_1840_);
    leanh::lean_dec_ref(v_a_1839_);
    return v_res_1848_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(
    mut v_00_u03b2_1849_: *mut leanh::LeanObject,
    mut v_x_1850_: *mut leanh::LeanObject,
    mut v_x_1851_: *mut leanh::LeanObject,
    mut v_x_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(
        v_x_1850_, v_x_1851_, v_x_1852_,
    );
    return v___x_1853_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(
    mut v_00_u03b2_1854_: *mut leanh::LeanObject,
    mut v_x_1855_: *mut leanh::LeanObject,
    mut v_x_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(
        v_x_1855_, v_x_1856_,
    );
    return v___x_1857_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(
    mut v_00_u03b2_1858_: *mut leanh::LeanObject,
    mut v_x_1859_: *mut leanh::LeanObject,
    mut v_x_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(
        v_00_u03b2_1858_,
        v_x_1859_,
        v_x_1860_,
    );
    leanh::lean_dec_ref(v_x_1860_);
    leanh::lean_dec_ref(v_x_1859_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(
    mut v_00_u03b2_1862_: *mut leanh::LeanObject,
    mut v_x_1863_: *mut leanh::LeanObject,
    mut v_x_1864_: usize,
    mut v_x_1865_: usize,
    mut v_x_1866_: *mut leanh::LeanObject,
    mut v_x_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_1863_, v_x_1864_, v_x_1865_, v_x_1866_, v_x_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(
    mut v_00_u03b2_1869_: *mut leanh::LeanObject,
    mut v_x_1870_: *mut leanh::LeanObject,
    mut v_x_1871_: *mut leanh::LeanObject,
    mut v_x_1872_: *mut leanh::LeanObject,
    mut v_x_1873_: *mut leanh::LeanObject,
    mut v_x_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7370__boxed_1875_: usize = 0;
    let mut v_x_7371__boxed_1876_: usize = 0;
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7370__boxed_1875_ = leanh::lean_unbox_usize(v_x_1871_);
    leanh::lean_dec(v_x_1871_);
    v_x_7371__boxed_1876_ = leanh::lean_unbox_usize(v_x_1872_);
    leanh::lean_dec(v_x_1872_);
    v_res_1877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_1869_, v_x_1870_, v_x_7370__boxed_1875_, v_x_7371__boxed_1876_, v_x_1873_, v_x_1874_);
    return v_res_1877_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(
    mut v_00_u03b1_1878_: *mut leanh::LeanObject,
    mut v_attrName_1879_: *mut leanh::LeanObject,
    mut v_declName_1880_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_1879_, v_declName_1880_, v_asyncPrefix_x3f_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
    return v___x_1887_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(
    mut v_00_u03b1_1888_: *mut leanh::LeanObject,
    mut v_attrName_1889_: *mut leanh::LeanObject,
    mut v_declName_1890_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_1888_, v_attrName_1889_, v_declName_1890_, v_asyncPrefix_x3f_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
    leanh::lean_dec(v___y_1895_);
    leanh::lean_dec_ref(v___y_1894_);
    leanh::lean_dec(v___y_1893_);
    leanh::lean_dec_ref(v___y_1892_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(
    mut v_00_u03b1_1898_: *mut leanh::LeanObject,
    mut v_attrName_1899_: *mut leanh::LeanObject,
    mut v_declName_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1906_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_1899_, v_declName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(
    mut v_00_u03b1_1907_: *mut leanh::LeanObject,
    mut v_attrName_1908_: *mut leanh::LeanObject,
    mut v_declName_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_1907_, v_attrName_1908_, v_declName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
    leanh::lean_dec(v___y_1913_);
    leanh::lean_dec_ref(v___y_1912_);
    leanh::lean_dec(v___y_1911_);
    leanh::lean_dec_ref(v___y_1910_);
    return v_res_1915_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(
    mut v_00_u03b2_1916_: *mut leanh::LeanObject,
    mut v_x_1917_: *mut leanh::LeanObject,
    mut v_x_1918_: usize,
    mut v_x_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_1917_, v_x_1918_, v_x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(
    mut v_00_u03b2_1921_: *mut leanh::LeanObject,
    mut v_x_1922_: *mut leanh::LeanObject,
    mut v_x_1923_: *mut leanh::LeanObject,
    mut v_x_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7421__boxed_1925_: usize = 0;
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7421__boxed_1925_ = leanh::lean_unbox_usize(v_x_1923_);
    leanh::lean_dec(v_x_1923_);
    v_res_1926_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_1921_, v_x_1922_, v_x_7421__boxed_1925_, v_x_1924_);
    leanh::lean_dec_ref(v_x_1924_);
    leanh::lean_dec_ref(v_x_1922_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1927_: *mut leanh::LeanObject,
    mut v_n_1928_: *mut leanh::LeanObject,
    mut v_k_1929_: *mut leanh::LeanObject,
    mut v_v_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_1928_, v_k_1929_, v_v_1930_);
    return v___x_1931_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(
    mut v_00_u03b2_1932_: *mut leanh::LeanObject,
    mut v_depth_1933_: usize,
    mut v_keys_1934_: *mut leanh::LeanObject,
    mut v_vals_1935_: *mut leanh::LeanObject,
    mut v_heq_1936_: *mut leanh::LeanObject,
    mut v_i_1937_: *mut leanh::LeanObject,
    mut v_entries_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_1933_, v_keys_1934_, v_vals_1935_, v_i_1937_, v_entries_1938_);
    return v___x_1939_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_1940_: *mut leanh::LeanObject,
    mut v_depth_1941_: *mut leanh::LeanObject,
    mut v_keys_1942_: *mut leanh::LeanObject,
    mut v_vals_1943_: *mut leanh::LeanObject,
    mut v_heq_1944_: *mut leanh::LeanObject,
    mut v_i_1945_: *mut leanh::LeanObject,
    mut v_entries_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1947_ = leanh::lean_unbox_usize(v_depth_1941_);
    leanh::lean_dec(v_depth_1941_);
    v_res_1948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_1940_, v_depth_boxed_1947_, v_keys_1942_, v_vals_1943_, v_heq_1944_, v_i_1945_, v_entries_1946_);
    leanh::lean_dec_ref(v_vals_1943_);
    leanh::lean_dec_ref(v_keys_1942_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(
    mut v_00_u03b1_1949_: *mut leanh::LeanObject,
    mut v_msg_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_1957_: *mut leanh::LeanObject,
    mut v_msg_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_1957_, v_msg_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
    leanh::lean_dec(v___y_1962_);
    leanh::lean_dec_ref(v___y_1961_);
    leanh::lean_dec(v___y_1960_);
    leanh::lean_dec_ref(v___y_1959_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(
    mut v_00_u03b2_1965_: *mut leanh::LeanObject,
    mut v_keys_1966_: *mut leanh::LeanObject,
    mut v_vals_1967_: *mut leanh::LeanObject,
    mut v_heq_1968_: *mut leanh::LeanObject,
    mut v_i_1969_: *mut leanh::LeanObject,
    mut v_k_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_1966_, v_vals_1967_, v_i_1969_, v_k_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_1972_: *mut leanh::LeanObject,
    mut v_keys_1973_: *mut leanh::LeanObject,
    mut v_vals_1974_: *mut leanh::LeanObject,
    mut v_heq_1975_: *mut leanh::LeanObject,
    mut v_i_1976_: *mut leanh::LeanObject,
    mut v_k_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_1972_, v_keys_1973_, v_vals_1974_, v_heq_1975_, v_i_1976_, v_k_1977_);
    leanh::lean_dec_ref(v_k_1977_);
    leanh::lean_dec_ref(v_vals_1974_);
    leanh::lean_dec_ref(v_keys_1973_);
    return v_res_1978_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(
    mut v_00_u03b2_1979_: *mut leanh::LeanObject,
    mut v_x_1980_: *mut leanh::LeanObject,
    mut v_x_1981_: *mut leanh::LeanObject,
    mut v_x_1982_: *mut leanh::LeanObject,
    mut v_x_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_1980_, v_x_1981_, v_x_1982_, v_x_1983_);
    return v___x_1984_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_AuxLemma(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DefEqAttrib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedAuxLemmas_default = _init_l_Lean_Meta_instInhabitedAuxLemmas_default();
    leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas_default);
    l_Lean_Meta_instInhabitedAuxLemmas = _init_l_Lean_Meta_instInhabitedAuxLemmas();
    leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas);
    res = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_auxLemmasExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_auxLemmasExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_AuxLemma(
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
pub unsafe fn initialize_Lean_Meta_Tactic_AuxLemma(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DefEqAttrib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_AuxLemma(builtin);
}
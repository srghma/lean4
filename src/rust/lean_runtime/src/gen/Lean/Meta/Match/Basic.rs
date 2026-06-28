// Lean compiler output
// Module: Lean.Meta.Match.Basic
// Imports: Lean.Meta.Tactic.FVarSubst Lean.Meta.CollectFVars Lean.Meta.Match.Value Lean.Meta.AppBuilder Lean.Meta.Match.NamedPatterns
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_isNat;
use crate::r#gen::Init::Prelude::{l_Array_extract___redArg, l_Lean_Name_mkStr1};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_const___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar,
    l_Lean_Expr_replaceFVarId, l_Lean_Expr_sort___override, l_Lean_inaccessible_x3f,
    l_Lean_instBEqFVarId_beq, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkInaccessible,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_replaceFVarId, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_joinSep, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkArrayLit,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
};
use crate::r#gen::Lean::Meta::CollectFVars::{
    initialize_Lean_Meta_CollectFVars, l_Lean_Expr_collectFVars, l_Lean_LocalDecl_collectFVars,
    runtime_initialize_Lean_Meta_CollectFVars,
};
use crate::r#gen::Lean::Meta::Match::NamedPatterns::{
    initialize_Lean_Meta_Match_NamedPatterns, l_Lean_Meta_Match_isNamedPattern_x3f,
    l_Lean_Meta_Match_mkNamedPattern, runtime_initialize_Lean_Meta_Match_NamedPatterns,
};
use crate::r#gen::Lean::Meta::Match::Value::{
    initialize_Lean_Meta_Match_Value, l_Lean_Meta_isMatchValue,
    runtime_initialize_Lean_Meta_Match_Value,
};
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_LocalDecl_applyFVarSubst,
    l_Lean_Meta_FVarSubst_apply, l_Lean_Meta_FVarSubst_find_x3f, l_Lean_Meta_FVarSubst_get,
    l_Lean_Meta_FVarSubst_insert, runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::CollectFVars::l_Lean_CollectFVars_State_add;
use crate::r#gen::Lean::Util::Recognizers::l_Lean_Expr_arrayLit_x3f;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109,
            121, 0,
        ],
    };
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value)
                as *mut LeanObject,
            17542774118954891045 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedPattern_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedPattern_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedPattern: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [46, 40, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value:
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
    m_data: [32, 0],
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value
) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [35, 91, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Pattern_toMessageData___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltLHS_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedAltLHS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_instInhabitedAlt_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedAlt_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedAlt: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [10, 32, 32, 124, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 137, 139, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 40, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value
) as *mut LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [124, 45, 32, 0],
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [10, 0],
    };
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Alt_toMessageData___closed__6_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Alt_toMessageData___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Alt_toMessageData___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Example_toMessageData___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_Example_toMessageData___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Example_toMessageData___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_Example_toMessageData___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [35, 0],
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_Example_toMessageData___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_Example_toMessageData___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Example_toMessageData___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Example_toMessageData___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_Example_toMessageData___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Match_instInhabitedProblem_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedProblem_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_instInhabitedProblem: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value: LeanStringObject<
    22,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        114, 101, 109, 97, 105, 110, 105, 110, 103, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115,
        58, 32, 0,
    ],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value: LeanStringObject<
    15,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        10, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 115, 58, 0,
    ],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [10, 101, 120, 97, 109, 112, 108, 101, 115, 58, 0],
};
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_toPattern___closed__0_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 97, 116, 116, 101, 114, 110, 0,
    ],
};
static mut l_Lean_Meta_Match_toPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_toPattern___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_toPattern___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_toPattern___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_toPattern___closed__2_value: LeanStringObject<62> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110,
        99, 101, 32, 111, 102, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99,
        108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 110, 97, 109, 101, 100, 80, 97, 116, 116,
        101, 114, 110, 39, 0,
    ],
};
static mut l_Lean_Meta_Match_toPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_toPattern___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_toPattern___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_toPattern___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_toPattern___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_toPattern___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 111, 110, 103, 114, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_congrEqnThmSuffixBase: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 111, 110, 103, 114, 95, 101, 113, 95, 0],
    };
static mut l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 111, 110, 103, 114, 95, 101, 113, 95, 49, 0],
    };
static mut l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Match_congrEqn1ThmSuffix: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value) as *mut LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorIdx(mut v_x_2475_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_2475_) {
        0 => {
            let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
            v___x_2476_ = lean_unsigned_to_nat(0);
            return v___x_2476_;
        }
        1 => {
            let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
            v___x_2477_ = lean_unsigned_to_nat(1);
            return v___x_2477_;
        }
        2 => {
            let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
            v___x_2478_ = lean_unsigned_to_nat(2);
            return v___x_2478_;
        }
        3 => {
            let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
            v___x_2479_ = lean_unsigned_to_nat(3);
            return v___x_2479_;
        }
        4 => {
            let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
            v___x_2480_ = lean_unsigned_to_nat(4);
            return v___x_2480_;
        }
        _ => {
            let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
            v___x_2481_ = lean_unsigned_to_nat(5);
            return v___x_2481_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorIdx___boxed(
    mut v_x_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2483_: *mut LeanObject = core::ptr::null_mut();
    v_res_2483_ = l_Lean_Meta_Match_Pattern_ctorIdx(v_x_2482_);
    lean_dec_ref(v_x_2482_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim___redArg(
    mut v_t_2484_: *mut LeanObject,
    mut v_k_2485_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_2484_) {
        1 => {
            let mut v_fvarId_2486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
            v_fvarId_2486_ = lean_ctor_get(v_t_2484_, 0);
            lean_inc(v_fvarId_2486_);
            lean_dec_ref_known(v_t_2484_, 1);
            v___x_2487_ = lean_apply_1(v_k_2485_, v_fvarId_2486_);
            return v___x_2487_;
        }
        2 => {
            let mut v_ctorName_2488_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_2489_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_2490_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fields_2491_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
            v_ctorName_2488_ = lean_ctor_get(v_t_2484_, 0);
            lean_inc(v_ctorName_2488_);
            v_us_2489_ = lean_ctor_get(v_t_2484_, 1);
            lean_inc(v_us_2489_);
            v_params_2490_ = lean_ctor_get(v_t_2484_, 2);
            lean_inc(v_params_2490_);
            v_fields_2491_ = lean_ctor_get(v_t_2484_, 3);
            lean_inc(v_fields_2491_);
            lean_dec_ref_known(v_t_2484_, 4);
            v___x_2492_ = lean_apply_4(
                v_k_2485_,
                v_ctorName_2488_,
                v_us_2489_,
                v_params_2490_,
                v_fields_2491_,
            );
            return v___x_2492_;
        }
        4 => {
            let mut v_type_2493_: *mut LeanObject = core::ptr::null_mut();
            let mut v_xs_2494_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
            v_type_2493_ = lean_ctor_get(v_t_2484_, 0);
            lean_inc_ref(v_type_2493_);
            v_xs_2494_ = lean_ctor_get(v_t_2484_, 1);
            lean_inc(v_xs_2494_);
            lean_dec_ref_known(v_t_2484_, 2);
            v___x_2495_ = lean_apply_2(v_k_2485_, v_type_2493_, v_xs_2494_);
            return v___x_2495_;
        }
        5 => {
            let mut v_varId_2496_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2497_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hId_2498_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
            v_varId_2496_ = lean_ctor_get(v_t_2484_, 0);
            lean_inc(v_varId_2496_);
            v_p_2497_ = lean_ctor_get(v_t_2484_, 1);
            lean_inc_ref(v_p_2497_);
            v_hId_2498_ = lean_ctor_get(v_t_2484_, 2);
            lean_inc(v_hId_2498_);
            lean_dec_ref_known(v_t_2484_, 3);
            v___x_2499_ = lean_apply_3(v_k_2485_, v_varId_2496_, v_p_2497_, v_hId_2498_);
            return v___x_2499_;
        }
        _ => {
            let mut v_e_2500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
            v_e_2500_ = lean_ctor_get(v_t_2484_, 0);
            lean_inc_ref(v_e_2500_);
            lean_dec_ref(v_t_2484_);
            v___x_2501_ = lean_apply_1(v_k_2485_, v_e_2500_);
            return v___x_2501_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim(
    mut v_motive__1_2502_: *mut LeanObject,
    mut v_ctorIdx_2503_: *mut LeanObject,
    mut v_t_2504_: *mut LeanObject,
    mut v_h_2505_: *mut LeanObject,
    mut v_k_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    v___x_2507_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2504_, v_k_2506_);
    return v___x_2507_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctorElim___boxed(
    mut v_motive__1_2508_: *mut LeanObject,
    mut v_ctorIdx_2509_: *mut LeanObject,
    mut v_t_2510_: *mut LeanObject,
    mut v_h_2511_: *mut LeanObject,
    mut v_k_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2513_: *mut LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Lean_Meta_Match_Pattern_ctorElim(
        v_motive__1_2508_,
        v_ctorIdx_2509_,
        v_t_2510_,
        v_h_2511_,
        v_k_2512_,
    );
    lean_dec(v_ctorIdx_2509_);
    return v_res_2513_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(
    mut v_t_2514_: *mut LeanObject,
    mut v_inaccessible_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2514_, v_inaccessible_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_inaccessible_elim(
    mut v_motive__1_2517_: *mut LeanObject,
    mut v_t_2518_: *mut LeanObject,
    mut v_h_2519_: *mut LeanObject,
    mut v_inaccessible_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2518_, v_inaccessible_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_var_elim___redArg(
    mut v_t_2522_: *mut LeanObject,
    mut v_var_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2522_, v_var_2523_);
    return v___x_2524_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_var_elim(
    mut v_motive__1_2525_: *mut LeanObject,
    mut v_t_2526_: *mut LeanObject,
    mut v_h_2527_: *mut LeanObject,
    mut v_var_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2526_, v_var_2528_);
    return v___x_2529_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctor_elim___redArg(
    mut v_t_2530_: *mut LeanObject,
    mut v_ctor_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2530_, v_ctor_2531_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_ctor_elim(
    mut v_motive__1_2533_: *mut LeanObject,
    mut v_t_2534_: *mut LeanObject,
    mut v_h_2535_: *mut LeanObject,
    mut v_ctor_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2534_, v_ctor_2536_);
    return v___x_2537_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_val_elim___redArg(
    mut v_t_2538_: *mut LeanObject,
    mut v_val_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2538_, v_val_2539_);
    return v___x_2540_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_val_elim(
    mut v_motive__1_2541_: *mut LeanObject,
    mut v_t_2542_: *mut LeanObject,
    mut v_h_2543_: *mut LeanObject,
    mut v_val_2544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2545_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2542_, v_val_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(
    mut v_t_2546_: *mut LeanObject,
    mut v_arrayLit_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2546_, v_arrayLit_2547_);
    return v___x_2548_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_arrayLit_elim(
    mut v_motive__1_2549_: *mut LeanObject,
    mut v_t_2550_: *mut LeanObject,
    mut v_h_2551_: *mut LeanObject,
    mut v_arrayLit_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2550_, v_arrayLit_2552_);
    return v___x_2553_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_as_elim___redArg(
    mut v_t_2554_: *mut LeanObject,
    mut v_as_2555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    v___x_2556_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2554_, v_as_2555_);
    return v___x_2556_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_as_elim(
    mut v_motive__1_2557_: *mut LeanObject,
    mut v_t_2558_: *mut LeanObject,
    mut v_h_2559_: *mut LeanObject,
    mut v_as_2560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    v___x_2561_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_2558_, v_as_2560_);
    return v___x_2561_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2() -> *mut LeanObject
{
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2565_ = lean_box(0);
    v___x_2566_ = l_Lean_Meta_Match_instInhabitedPattern_default___closed__1;
    v___x_2567_ = l_Lean_Expr_const___override(v___x_2566_, v___x_2565_);
    return v___x_2567_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3() -> *mut LeanObject
{
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___x_2568_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2,
    );
    v___x_2569_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    return v___x_2569_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern_default() -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3,
    );
    return v___x_2570_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedPattern() -> *mut LeanObject {
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___x_2571_ = l_Lean_Meta_Match_instInhabitedPattern_default;
    return v___x_2571_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1() -> *mut LeanObject {
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    v___x_2573_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__0;
    v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3() -> *mut LeanObject {
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__2;
    v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
    return v___x_2577_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5() -> *mut LeanObject {
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__4;
    v___x_2580_ = l_Lean_stringToMessageData(v___x_2579_);
    return v___x_2580_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6() -> *mut LeanObject {
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    v___x_2581_ = lean_box(0);
    v___x_2582_ = l_Lean_MessageData_ofFormat(v___x_2581_);
    return v___x_2582_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1;
    v___x_2587_ = l_Lean_MessageData_ofFormat(v___x_2586_);
    return v___x_2587_;
}
pub unsafe fn l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(
    mut v_x_2588_: *mut LeanObject,
    mut v_x_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2589_) == 0 {
                    return v_x_2588_;
                } else {
                    v_head_2590_ = lean_ctor_get(v_x_2589_, 0);
                    v_tail_2591_ = lean_ctor_get(v_x_2589_, 1);
                    v_isSharedCheck_2602_ = (!lean_is_exclusive(v_x_2589_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2593_ = v_x_2589_;
                        v_isShared_2594_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2591_);
                        lean_inc(v_head_2590_);
                        lean_dec(v_x_2589_);
                        v___x_2593_ = lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2595_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once), _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2);
                if v_isShared_2594_ == 0 {
                    lean_ctor_set_tag(v___x_2593_, 7);
                    lean_ctor_set(v___x_2593_, 1, v___x_2595_);
                    lean_ctor_set(v___x_2593_, 0, v_x_2588_);
                    v___x_2597_ = v___x_2593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_x_2588_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2595_);
                    v___x_2597_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2598_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_2590_);
                v___x_2599_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2599_, 0, v___x_2597_);
                lean_ctor_set(v___x_2599_, 1, v___x_2598_);
                v_x_2588_ = v___x_2599_;
                v_x_2589_ = v_tail_2591_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8() -> *mut LeanObject {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__7;
    v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
    return v___x_2605_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11() -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__10;
    v___x_2610_ = l_Lean_MessageData_ofFormat(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13() -> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__12;
    v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15() -> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2615_ = l_Lean_Meta_Match_Pattern_toMessageData___closed__14;
    v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
    return v___x_2616_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toMessageData(
    mut v_x_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_unused_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varId_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2617_) {
                0 => {
                    v_e_2618_ = lean_ctor_get(v_x_2617_, 0);
                    lean_inc_ref(v_e_2618_);
                    lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2619_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1,
                    );
                    v___x_2620_ = l_Lean_MessageData_ofExpr(v_e_2618_);
                    v___x_2621_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2621_, 0, v___x_2619_);
                    lean_ctor_set(v___x_2621_, 1, v___x_2620_);
                    v___x_2622_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                    );
                    v___x_2623_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2623_, 0, v___x_2621_);
                    lean_ctor_set(v___x_2623_, 1, v___x_2622_);
                    return v___x_2623_;
                }
                1 => {
                    v_fvarId_2624_ = lean_ctor_get(v_x_2617_, 0);
                    lean_inc(v_fvarId_2624_);
                    lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2625_ = l_Lean_mkFVar(v_fvarId_2624_);
                    v___x_2626_ = l_Lean_MessageData_ofExpr(v___x_2625_);
                    return v___x_2626_;
                }
                2 => {
                    v_fields_2627_ = lean_ctor_get(v_x_2617_, 3);
                    if lean_obj_tag(v_fields_2627_) == 0 {
                        v_ctorName_2628_ = lean_ctor_get(v_x_2617_, 0);
                        lean_inc(v_ctorName_2628_);
                        lean_dec_ref_known(v_x_2617_, 4);
                        v___x_2629_ = l_Lean_MessageData_ofName(v_ctorName_2628_);
                        return v___x_2629_;
                    } else {
                        lean_inc(v_fields_2627_);
                        v_ctorName_2630_ = lean_ctor_get(v_x_2617_, 0);
                        lean_inc(v_ctorName_2630_);
                        lean_dec_ref_known(v_x_2617_, 4);
                        v___x_2631_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5,
                        );
                        v___x_2632_ = l_Lean_MessageData_ofName(v_ctorName_2630_);
                        v___x_2633_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2633_, 0, v___x_2631_);
                        lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                        v___x_2634_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6,
                        );
                        v___x_2635_ =
                            l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(
                                v___x_2634_,
                                v_fields_2627_,
                            );
                        v___x_2636_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2636_, 0, v___x_2633_);
                        lean_ctor_set(v___x_2636_, 1, v___x_2635_);
                        v___x_2637_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                            ),
                            _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                        );
                        v___x_2638_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2638_, 0, v___x_2636_);
                        lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                        return v___x_2638_;
                    }
                }
                3 => {
                    v_e_2639_ = lean_ctor_get(v_x_2617_, 0);
                    lean_inc_ref(v_e_2639_);
                    lean_dec_ref_known(v_x_2617_, 1);
                    v___x_2640_ = l_Lean_MessageData_ofExpr(v_e_2639_);
                    return v___x_2640_;
                }
                4 => {
                    v_xs_2641_ = lean_ctor_get(v_x_2617_, 1);
                    v_isSharedCheck_2655_ = (!lean_is_exclusive(v_x_2617_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v_unused_2656_ = lean_ctor_get(v_x_2617_, 0);
                        lean_dec(v_unused_2656_);
                        v___x_2643_ = v_x_2617_;
                        v_isShared_2644_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_xs_2641_);
                        lean_dec(v_x_2617_);
                        v___x_2643_ = lean_box(0);
                        v_isShared_2644_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_varId_2657_ = lean_ctor_get(v_x_2617_, 0);
                    lean_inc(v_varId_2657_);
                    v_p_2658_ = lean_ctor_get(v_x_2617_, 1);
                    lean_inc_ref(v_p_2658_);
                    lean_dec_ref_known(v_x_2617_, 3);
                    v___x_2659_ = l_Lean_mkFVar(v_varId_2657_);
                    v___x_2660_ = l_Lean_MessageData_ofExpr(v___x_2659_);
                    v___x_2661_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15,
                    );
                    v___x_2662_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2662_, 0, v___x_2660_);
                    lean_ctor_set(v___x_2662_, 1, v___x_2661_);
                    v___x_2663_ = l_Lean_Meta_Match_Pattern_toMessageData(v_p_2658_);
                    v___x_2664_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2664_, 0, v___x_2662_);
                    lean_ctor_set(v___x_2664_, 1, v___x_2663_);
                    return v___x_2664_;
                }
            },
            1 => {
                v___x_2645_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8,
                );
                v___x_2646_ = lean_box(0);
                v___x_2647_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
                        v_xs_2641_,
                        v___x_2646_,
                    );
                v___x_2648_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11,
                );
                v___x_2649_ = l_Lean_MessageData_joinSep(v___x_2647_, v___x_2648_);
                if v_isShared_2644_ == 0 {
                    lean_ctor_set_tag(v___x_2643_, 7);
                    lean_ctor_set(v___x_2643_, 1, v___x_2649_);
                    lean_ctor_set(v___x_2643_, 0, v___x_2645_);
                    v___x_2651_ = v___x_2643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2645_);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2649_);
                    v___x_2651_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2652_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13,
                );
                v___x_2653_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2653_, 0, v___x_2651_);
                lean_ctor_set(v___x_2653_, 1, v___x_2652_);
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2665_) == 0 {
                    v___x_2667_ = l_List_reverse___redArg(v_a_2666_);
                    return v___x_2667_;
                } else {
                    v_head_2668_ = lean_ctor_get(v_a_2665_, 0);
                    v_tail_2669_ = lean_ctor_get(v_a_2665_, 1);
                    v_isSharedCheck_2678_ = (!lean_is_exclusive(v_a_2665_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2671_ = v_a_2665_;
                        v_isShared_2672_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2669_);
                        lean_inc(v_head_2668_);
                        lean_dec(v_a_2665_);
                        v___x_2671_ = lean_box(0);
                        v_isShared_2672_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2673_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_2668_);
                if v_isShared_2672_ == 0 {
                    lean_ctor_set(v___x_2671_, 1, v_a_2666_);
                    lean_ctor_set(v___x_2671_, 0, v___x_2673_);
                    v___x_2675_ = v___x_2671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2673_);
                    lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2666_);
                    v___x_2675_ = v_reuseFailAlloc_2677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2665_ = v_tail_2669_;
                v_a_2666_ = v___x_2675_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
    mut v_annotate_2679_: u8,
    mut v_p_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_e_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_fvarId_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v_ctorName_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_a_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_e_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_type_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_p_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varId_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hId_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_p_2680_) {
                0 => {
                    if v_annotate_2679_ == 0 {
                        v_e_2686_ = lean_ctor_get(v_p_2680_, 0);
                        v_isSharedCheck_2693_ = (!lean_is_exclusive(v_p_2680_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v___x_2688_ = v_p_2680_;
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_e_2686_);
                            lean_dec(v_p_2680_);
                            v___x_2688_ = lean_box(0);
                            v_isShared_2689_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_e_2694_ = lean_ctor_get(v_p_2680_, 0);
                        v_isSharedCheck_2702_ = (!lean_is_exclusive(v_p_2680_)) as u8;
                        if v_isSharedCheck_2702_ == 0 {
                            v___x_2696_ = v_p_2680_;
                            v_isShared_2697_ = v_isSharedCheck_2702_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_e_2694_);
                            lean_dec(v_p_2680_);
                            v___x_2696_ = lean_box(0);
                            v_isShared_2697_ = v_isSharedCheck_2702_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_2703_ = lean_ctor_get(v_p_2680_, 0);
                    v_isSharedCheck_2711_ = (!lean_is_exclusive(v_p_2680_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2705_ = v_p_2680_;
                        v_isShared_2706_ = v_isSharedCheck_2711_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_fvarId_2703_);
                        lean_dec(v_p_2680_);
                        v___x_2705_ = lean_box(0);
                        v_isShared_2706_ = v_isSharedCheck_2711_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_ctorName_2712_ = lean_ctor_get(v_p_2680_, 0);
                    lean_inc(v_ctorName_2712_);
                    v_us_2713_ = lean_ctor_get(v_p_2680_, 1);
                    lean_inc(v_us_2713_);
                    v_params_2714_ = lean_ctor_get(v_p_2680_, 2);
                    lean_inc(v_params_2714_);
                    v_fields_2715_ = lean_ctor_get(v_p_2680_, 3);
                    lean_inc(v_fields_2715_);
                    lean_dec_ref_known(v_p_2680_, 4);
                    v___x_2716_ = lean_box(0);
                    v___x_2717_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_2679_, v_fields_2715_, v___x_2716_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                    if lean_obj_tag(v___x_2717_) == 0 {
                        v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
                        v_isSharedCheck_2729_ = (!lean_is_exclusive(v___x_2717_)) as u8;
                        if v_isSharedCheck_2729_ == 0 {
                            v___x_2720_ = v___x_2717_;
                            v_isShared_2721_ = v_isSharedCheck_2729_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2718_);
                            lean_dec(v___x_2717_);
                            v___x_2720_ = lean_box(0);
                            v_isShared_2721_ = v_isSharedCheck_2729_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_params_2714_);
                        lean_dec(v_us_2713_);
                        lean_dec(v_ctorName_2712_);
                        v_a_2730_ = lean_ctor_get(v___x_2717_, 0);
                        v_isSharedCheck_2737_ = (!lean_is_exclusive(v___x_2717_)) as u8;
                        if v_isSharedCheck_2737_ == 0 {
                            v___x_2732_ = v___x_2717_;
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2730_);
                            lean_dec(v___x_2717_);
                            v___x_2732_ = lean_box(0);
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 9;
                            continue;
                        }
                    }
                }
                3 => {
                    v_e_2738_ = lean_ctor_get(v_p_2680_, 0);
                    v_isSharedCheck_2745_ = (!lean_is_exclusive(v_p_2680_)) as u8;
                    if v_isSharedCheck_2745_ == 0 {
                        v___x_2740_ = v_p_2680_;
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_e_2738_);
                        lean_dec(v_p_2680_);
                        v___x_2740_ = lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 11;
                        continue;
                    }
                }
                4 => {
                    v_type_2746_ = lean_ctor_get(v_p_2680_, 0);
                    lean_inc_ref(v_type_2746_);
                    v_xs_2747_ = lean_ctor_get(v_p_2680_, 1);
                    lean_inc(v_xs_2747_);
                    lean_dec_ref_known(v_p_2680_, 2);
                    v___x_2748_ = lean_box(0);
                    v___x_2749_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_2679_, v_xs_2747_, v___x_2748_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                    if lean_obj_tag(v___x_2749_) == 0 {
                        v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
                        lean_inc(v_a_2750_);
                        lean_dec_ref_known(v___x_2749_, 1);
                        v___x_2751_ = l_Lean_Meta_mkArrayLit(
                            v_type_2746_,
                            v_a_2750_,
                            v_a_2681_,
                            v_a_2682_,
                            v_a_2683_,
                            v_a_2684_,
                        );
                        return v___x_2751_;
                    } else {
                        lean_dec_ref(v_type_2746_);
                        v_a_2752_ = lean_ctor_get(v___x_2749_, 0);
                        v_isSharedCheck_2759_ = (!lean_is_exclusive(v___x_2749_)) as u8;
                        if v_isSharedCheck_2759_ == 0 {
                            v___x_2754_ = v___x_2749_;
                            v_isShared_2755_ = v_isSharedCheck_2759_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_2752_);
                            lean_dec(v___x_2749_);
                            v___x_2754_ = lean_box(0);
                            v_isShared_2755_ = v_isSharedCheck_2759_;
                            state = 13;
                            continue;
                        }
                    }
                }
                _ => {
                    if v_annotate_2679_ == 0 {
                        v_p_2760_ = lean_ctor_get(v_p_2680_, 1);
                        lean_inc_ref(v_p_2760_);
                        lean_dec_ref_known(v_p_2680_, 3);
                        v_p_2680_ = v_p_2760_;
                        state = 0;
                        continue;
                    } else {
                        v_varId_2762_ = lean_ctor_get(v_p_2680_, 0);
                        lean_inc(v_varId_2762_);
                        v_p_2763_ = lean_ctor_get(v_p_2680_, 1);
                        lean_inc_ref(v_p_2763_);
                        v_hId_2764_ = lean_ctor_get(v_p_2680_, 2);
                        lean_inc(v_hId_2764_);
                        lean_dec_ref_known(v_p_2680_, 3);
                        v___x_2765_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_2679_, v_p_2763_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
                        if lean_obj_tag(v___x_2765_) == 0 {
                            v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
                            lean_inc(v_a_2766_);
                            lean_dec_ref_known(v___x_2765_, 1);
                            v___x_2767_ = l_Lean_mkFVar(v_varId_2762_);
                            v___x_2768_ = l_Lean_mkFVar(v_hId_2764_);
                            v___x_2769_ = l_Lean_Meta_Match_mkNamedPattern(
                                v___x_2767_,
                                v___x_2768_,
                                v_a_2766_,
                                v_a_2681_,
                                v_a_2682_,
                                v_a_2683_,
                                v_a_2684_,
                            );
                            return v___x_2769_;
                        } else {
                            lean_dec(v_hId_2764_);
                            lean_dec(v_varId_2762_);
                            return v___x_2765_;
                        }
                    }
                }
            },
            1 => {
                if v_isShared_2689_ == 0 {
                    v___x_2691_ = v___x_2688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_e_2686_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2691_;
            }
            3 => {
                v___x_2698_ = l_Lean_mkInaccessible(v_e_2694_);
                if v_isShared_2697_ == 0 {
                    lean_ctor_set(v___x_2696_, 0, v___x_2698_);
                    v___x_2700_ = v___x_2696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
                    v___x_2700_ = v_reuseFailAlloc_2701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2700_;
            }
            5 => {
                v___x_2707_ = l_Lean_mkFVar(v_fvarId_2703_);
                if v_isShared_2706_ == 0 {
                    lean_ctor_set_tag(v___x_2705_, 0);
                    lean_ctor_set(v___x_2705_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2705_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2709_;
            }
            7 => {
                v___x_2722_ = l_Lean_mkConst(v_ctorName_2712_, v_us_2713_);
                v___x_2723_ = l_List_appendTR___redArg(v_params_2714_, v_a_2718_);
                v___x_2724_ = lean_array_mk(v___x_2723_);
                v___x_2725_ = l_Lean_mkAppN(v___x_2722_, v___x_2724_);
                lean_dec_ref(v___x_2724_);
                if v_isShared_2721_ == 0 {
                    lean_ctor_set(v___x_2720_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2720_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2727_;
            }
            9 => {
                if v_isShared_2733_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2735_;
            }
            11 => {
                if v_isShared_2741_ == 0 {
                    lean_ctor_set_tag(v___x_2740_, 0);
                    v___x_2743_ = v___x_2740_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_e_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2743_;
            }
            13 => {
                if v_isShared_2755_ == 0 {
                    v___x_2757_ = v___x_2754_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
                    v___x_2757_ = v_reuseFailAlloc_2758_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(
    mut v_annotate_2770_: u8,
    mut v_x_2771_: *mut LeanObject,
    mut v_x_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2771_) == 0 {
                    v___x_2778_ = l_List_reverse___redArg(v_x_2772_);
                    v___x_2779_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2779_, 0, v___x_2778_);
                    return v___x_2779_;
                } else {
                    v_head_2780_ = lean_ctor_get(v_x_2771_, 0);
                    v_tail_2781_ = lean_ctor_get(v_x_2771_, 1);
                    v_isSharedCheck_2799_ = (!lean_is_exclusive(v_x_2771_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2783_ = v_x_2771_;
                        v_isShared_2784_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2781_);
                        lean_inc(v_head_2780_);
                        lean_dec(v_x_2771_);
                        v___x_2783_ = lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2785_ =
                    l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
                        v_annotate_2770_,
                        v_head_2780_,
                        v___y_2773_,
                        v___y_2774_,
                        v___y_2775_,
                        v___y_2776_,
                    );
                if lean_obj_tag(v___x_2785_) == 0 {
                    v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
                    lean_inc(v_a_2786_);
                    lean_dec_ref_known(v___x_2785_, 1);
                    if v_isShared_2784_ == 0 {
                        lean_ctor_set(v___x_2783_, 1, v_x_2772_);
                        lean_ctor_set(v___x_2783_, 0, v_a_2786_);
                        v___x_2788_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2786_);
                        lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_x_2772_);
                        v___x_2788_ = v_reuseFailAlloc_2790_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2783_);
                    lean_dec(v_tail_2781_);
                    lean_dec(v_x_2772_);
                    v_a_2791_ = lean_ctor_get(v___x_2785_, 0);
                    v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2785_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v___x_2793_ = v___x_2785_;
                        v_isShared_2794_ = v_isSharedCheck_2798_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2791_);
                        lean_dec(v___x_2785_);
                        v___x_2793_ = lean_box(0);
                        v_isShared_2794_ = v_isSharedCheck_2798_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_2771_ = v_tail_2781_;
                v_x_2772_ = v___x_2788_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2794_ == 0 {
                    v___x_2796_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(
    mut v_annotate_2800_: *mut LeanObject,
    mut v_x_2801_: *mut LeanObject,
    mut v_x_2802_: *mut LeanObject,
    mut v___y_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_annotate_boxed_2808_: u8 = 0;
    let mut v_res_2809_: *mut LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2808_ = (lean_unbox(v_annotate_2800_) as u8);
    v_res_2809_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_boxed_2808_, v_x_2801_, v_x_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
    lean_dec(v___y_2806_);
    lean_dec_ref(v___y_2805_);
    lean_dec(v___y_2804_);
    lean_dec_ref(v___y_2803_);
    return v_res_2809_;
}
pub unsafe fn l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(
    mut v_annotate_2810_: *mut LeanObject,
    mut v_p_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: *mut LeanObject,
    mut v_a_2815_: *mut LeanObject,
    mut v_a_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_annotate_boxed_2817_: u8 = 0;
    let mut v_res_2818_: *mut LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2817_ = (lean_unbox(v_annotate_2810_) as u8);
    v_res_2818_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
        v_annotate_boxed_2817_,
        v_p_2811_,
        v_a_2812_,
        v_a_2813_,
        v_a_2814_,
        v_a_2815_,
    );
    lean_dec(v_a_2815_);
    lean_dec_ref(v_a_2814_);
    lean_dec(v_a_2813_);
    lean_dec_ref(v_a_2812_);
    return v_res_2818_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toExpr(
    mut v_p_2819_: *mut LeanObject,
    mut v_annotate_2820_: u8,
    mut v_a_2821_: *mut LeanObject,
    mut v_a_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    v___x_2826_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(
        v_annotate_2820_,
        v_p_2819_,
        v_a_2821_,
        v_a_2822_,
        v_a_2823_,
        v_a_2824_,
    );
    return v___x_2826_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_toExpr___boxed(
    mut v_p_2827_: *mut LeanObject,
    mut v_annotate_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
    mut v_a_2831_: *mut LeanObject,
    mut v_a_2832_: *mut LeanObject,
    mut v_a_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_annotate_boxed_2834_: u8 = 0;
    let mut v_res_2835_: *mut LeanObject = core::ptr::null_mut();
    v_annotate_boxed_2834_ = (lean_unbox(v_annotate_2828_) as u8);
    v_res_2835_ = l_Lean_Meta_Match_Pattern_toExpr(
        v_p_2827_,
        v_annotate_boxed_2834_,
        v_a_2829_,
        v_a_2830_,
        v_a_2831_,
        v_a_2832_,
    );
    lean_dec(v_a_2832_);
    lean_dec_ref(v_a_2831_);
    lean_dec(v_a_2830_);
    lean_dec_ref(v_a_2829_);
    return v_res_2835_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(
    mut v_s_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2837_) == 0 {
                    lean_dec(v_s_2836_);
                    v___x_2839_ = l_List_reverse___redArg(v_a_2838_);
                    return v___x_2839_;
                } else {
                    v_head_2840_ = lean_ctor_get(v_a_2837_, 0);
                    v_tail_2841_ = lean_ctor_get(v_a_2837_, 1);
                    v_isSharedCheck_2850_ = (!lean_is_exclusive(v_a_2837_)) as u8;
                    if v_isSharedCheck_2850_ == 0 {
                        v___x_2843_ = v_a_2837_;
                        v_isShared_2844_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2841_);
                        lean_inc(v_head_2840_);
                        lean_dec(v_a_2837_);
                        v___x_2843_ = lean_box(0);
                        v_isShared_2844_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_s_2836_);
                v___x_2845_ = l_Lean_Meta_FVarSubst_apply(v_s_2836_, v_head_2840_);
                lean_dec(v_head_2840_);
                if v_isShared_2844_ == 0 {
                    lean_ctor_set(v___x_2843_, 1, v_a_2838_);
                    lean_ctor_set(v___x_2843_, 0, v___x_2845_);
                    v___x_2847_ = v___x_2843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2845_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_a_2838_);
                    v___x_2847_ = v_reuseFailAlloc_2849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2837_ = v_tail_2841_;
                v_a_2838_ = v___x_2847_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_applyFVarSubst(
    mut v_s_2851_: *mut LeanObject,
    mut v_x_2852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_fvarId_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v_val_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_e_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_type_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_varId_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hId_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2852_) {
                0 => {
                    v_e_2853_ = lean_ctor_get(v_x_2852_, 0);
                    v_isSharedCheck_2861_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2855_ = v_x_2852_;
                        v_isShared_2856_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_e_2853_);
                        lean_dec(v_x_2852_);
                        v___x_2855_ = lean_box(0);
                        v_isShared_2856_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_fvarId_2862_ = lean_ctor_get(v_x_2852_, 0);
                    v___x_2863_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2851_, v_fvarId_2862_);
                    lean_dec(v_s_2851_);
                    if lean_obj_tag(v___x_2863_) == 0 {
                        return v_x_2852_;
                    } else {
                        v_isSharedCheck_2871_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                        if v_isSharedCheck_2871_ == 0 {
                            v_unused_2872_ = lean_ctor_get(v_x_2852_, 0);
                            lean_dec(v_unused_2872_);
                            v___x_2865_ = v_x_2852_;
                            v_isShared_2866_ = v_isSharedCheck_2871_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_2852_);
                            v___x_2865_ = lean_box(0);
                            v_isShared_2866_ = v_isSharedCheck_2871_;
                            state = 3;
                            continue;
                        }
                    }
                }
                2 => {
                    v_ctorName_2873_ = lean_ctor_get(v_x_2852_, 0);
                    v_us_2874_ = lean_ctor_get(v_x_2852_, 1);
                    v_params_2875_ = lean_ctor_get(v_x_2852_, 2);
                    v_fields_2876_ = lean_ctor_get(v_x_2852_, 3);
                    v_isSharedCheck_2886_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2878_ = v_x_2852_;
                        v_isShared_2879_ = v_isSharedCheck_2886_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_fields_2876_);
                        lean_inc(v_params_2875_);
                        lean_inc(v_us_2874_);
                        lean_inc(v_ctorName_2873_);
                        lean_dec(v_x_2852_);
                        v___x_2878_ = lean_box(0);
                        v_isShared_2879_ = v_isSharedCheck_2886_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_e_2887_ = lean_ctor_get(v_x_2852_, 0);
                    v_isSharedCheck_2895_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2889_ = v_x_2852_;
                        v_isShared_2890_ = v_isSharedCheck_2895_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_e_2887_);
                        lean_dec(v_x_2852_);
                        v___x_2889_ = lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2895_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_type_2896_ = lean_ctor_get(v_x_2852_, 0);
                    v_xs_2897_ = lean_ctor_get(v_x_2852_, 1);
                    v_isSharedCheck_2907_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2907_ == 0 {
                        v___x_2899_ = v_x_2852_;
                        v_isShared_2900_ = v_isSharedCheck_2907_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_xs_2897_);
                        lean_inc(v_type_2896_);
                        lean_dec(v_x_2852_);
                        v___x_2899_ = lean_box(0);
                        v_isShared_2900_ = v_isSharedCheck_2907_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    v_varId_2908_ = lean_ctor_get(v_x_2852_, 0);
                    v_p_2909_ = lean_ctor_get(v_x_2852_, 1);
                    v_hId_2910_ = lean_ctor_get(v_x_2852_, 2);
                    v_isSharedCheck_2920_ = (!lean_is_exclusive(v_x_2852_)) as u8;
                    if v_isSharedCheck_2920_ == 0 {
                        v___x_2912_ = v_x_2852_;
                        v_isShared_2913_ = v_isSharedCheck_2920_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_hId_2910_);
                        lean_inc(v_p_2909_);
                        lean_inc(v_varId_2908_);
                        lean_dec(v_x_2852_);
                        v___x_2912_ = lean_box(0);
                        v_isShared_2913_ = v_isSharedCheck_2920_;
                        state = 11;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2857_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_e_2853_);
                lean_dec_ref(v_e_2853_);
                if v_isShared_2856_ == 0 {
                    lean_ctor_set(v___x_2855_, 0, v___x_2857_);
                    v___x_2859_ = v___x_2855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2859_;
            }
            3 => {
                v_val_2867_ = lean_ctor_get(v___x_2863_, 0);
                lean_inc(v_val_2867_);
                lean_dec_ref_known(v___x_2863_, 1);
                if v_isShared_2866_ == 0 {
                    lean_ctor_set_tag(v___x_2865_, 0);
                    lean_ctor_set(v___x_2865_, 0, v_val_2867_);
                    v___x_2869_ = v___x_2865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_val_2867_);
                    v___x_2869_ = v_reuseFailAlloc_2870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2869_;
            }
            5 => {
                v___x_2880_ = lean_box(0);
                lean_inc(v_s_2851_);
                v___x_2881_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(
                        v_s_2851_,
                        v_params_2875_,
                        v___x_2880_,
                    );
                v___x_2882_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
                        v_s_2851_,
                        v_fields_2876_,
                        v___x_2880_,
                    );
                if v_isShared_2879_ == 0 {
                    lean_ctor_set(v___x_2878_, 3, v___x_2882_);
                    lean_ctor_set(v___x_2878_, 2, v___x_2881_);
                    v___x_2884_ = v___x_2878_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_ctorName_2873_);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_us_2874_);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 2, v___x_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2885_, 3, v___x_2882_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2884_;
            }
            7 => {
                v___x_2891_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_e_2887_);
                lean_dec_ref(v_e_2887_);
                if v_isShared_2890_ == 0 {
                    lean_ctor_set(v___x_2889_, 0, v___x_2891_);
                    v___x_2893_ = v___x_2889_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2893_;
            }
            9 => {
                lean_inc(v_s_2851_);
                v___x_2901_ = l_Lean_Meta_FVarSubst_apply(v_s_2851_, v_type_2896_);
                lean_dec_ref(v_type_2896_);
                v___x_2902_ = lean_box(0);
                v___x_2903_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
                        v_s_2851_,
                        v_xs_2897_,
                        v___x_2902_,
                    );
                if v_isShared_2900_ == 0 {
                    lean_ctor_set(v___x_2899_, 1, v___x_2903_);
                    lean_ctor_set(v___x_2899_, 0, v___x_2901_);
                    v___x_2905_ = v___x_2899_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2901_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2906_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2905_;
            }
            11 => {
                v___x_2914_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2851_, v_varId_2908_);
                if lean_obj_tag(v___x_2914_) == 0 {
                    v___x_2915_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_2851_, v_p_2909_);
                    if v_isShared_2913_ == 0 {
                        lean_ctor_set(v___x_2912_, 1, v___x_2915_);
                        v___x_2917_ = v___x_2912_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2918_ = lean_alloc_ctor(5, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_varId_2908_);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2915_);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_hId_2910_);
                        v___x_2917_ = v_reuseFailAlloc_2918_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2914_, 1);
                    lean_del_object(v___x_2912_);
                    lean_dec(v_hId_2910_);
                    lean_dec(v_varId_2908_);
                    v_x_2852_ = v_p_2909_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                return v___x_2917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(
    mut v_s_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2922_) == 0 {
                    lean_dec(v_s_2921_);
                    v___x_2924_ = l_List_reverse___redArg(v_a_2923_);
                    return v___x_2924_;
                } else {
                    v_head_2925_ = lean_ctor_get(v_a_2922_, 0);
                    v_tail_2926_ = lean_ctor_get(v_a_2922_, 1);
                    v_isSharedCheck_2935_ = (!lean_is_exclusive(v_a_2922_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v___x_2928_ = v_a_2922_;
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2926_);
                        lean_inc(v_head_2925_);
                        lean_dec(v_a_2922_);
                        v___x_2928_ = lean_box(0);
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_s_2921_);
                v___x_2930_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_2921_, v_head_2925_);
                if v_isShared_2929_ == 0 {
                    lean_ctor_set(v___x_2928_, 1, v_a_2923_);
                    lean_ctor_set(v___x_2928_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2930_);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_a_2923_);
                    v___x_2932_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2922_ = v_tail_2926_;
                v_a_2923_ = v___x_2932_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Pattern_replaceFVarId(
    mut v_fvarId_2936_: *mut LeanObject,
    mut v_v_2937_: *mut LeanObject,
    mut v_p_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v_s_2939_ = lean_box(0);
    v___x_2940_ = l_Lean_Meta_FVarSubst_insert(v_s_2939_, v_fvarId_2936_, v_v_2937_);
    v___x_2941_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v___x_2940_, v_p_2938_);
    return v___x_2941_;
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(
    mut v_x_2942_: *mut LeanObject,
) -> u8 {
    let mut v___x_2943_: u8 = 0;
    let mut v_head_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2942_) == 0 {
                    v___x_2943_ = 0;
                    return v___x_2943_;
                } else {
                    v_head_2944_ = lean_ctor_get(v_x_2942_, 0);
                    v_tail_2945_ = lean_ctor_get(v_x_2942_, 1);
                    v___x_2946_ = l_Lean_Expr_hasExprMVar(v_head_2944_);
                    if v___x_2946_ == 0 {
                        v_x_2942_ = v_tail_2945_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2946_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(
    mut v_x_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: u8 = 0;
    let mut v_r_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_2948_);
    lean_dec(v_x_2948_);
    v_r_2950_ = lean_box((v_res_2949_) as usize);
    return v_r_2950_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_hasExprMVar(mut v_x_2951_: *mut LeanObject) -> u8 {
    let mut v_e_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: u8 = 0;
    let mut v_params_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: u8 = 0;
    let mut v_e_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v_p_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2951_) {
                0 => {
                    v_e_2952_ = lean_ctor_get(v_x_2951_, 0);
                    v___x_2953_ = l_Lean_Expr_hasExprMVar(v_e_2952_);
                    return v___x_2953_;
                }
                2 => {
                    v_params_2954_ = lean_ctor_get(v_x_2951_, 2);
                    v_fields_2955_ = lean_ctor_get(v_x_2951_, 3);
                    v___x_2956_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(
                        v_params_2954_,
                    );
                    if v___x_2956_ == 0 {
                        v___x_2957_ =
                            l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
                                v_fields_2955_,
                            );
                        return v___x_2957_;
                    } else {
                        return v___x_2956_;
                    }
                }
                3 => {
                    v_e_2958_ = lean_ctor_get(v_x_2951_, 0);
                    v___x_2959_ = l_Lean_Expr_hasExprMVar(v_e_2958_);
                    return v___x_2959_;
                }
                5 => {
                    v_p_2960_ = lean_ctor_get(v_x_2951_, 1);
                    v_x_2951_ = v_p_2960_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_type_2962_ = lean_ctor_get(v_x_2951_, 0);
                    v_xs_2963_ = lean_ctor_get(v_x_2951_, 1);
                    v___x_2964_ = l_Lean_Expr_hasExprMVar(v_type_2962_);
                    if v___x_2964_ == 0 {
                        v___x_2965_ =
                            l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
                                v_xs_2963_,
                            );
                        return v___x_2965_;
                    } else {
                        return v___x_2964_;
                    }
                }
                _ => {
                    v___x_2966_ = 0;
                    return v___x_2966_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(
    mut v_x_2967_: *mut LeanObject,
) -> u8 {
    let mut v___x_2968_: u8 = 0;
    let mut v_head_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2967_) == 0 {
                    v___x_2968_ = 0;
                    return v___x_2968_;
                } else {
                    v_head_2969_ = lean_ctor_get(v_x_2967_, 0);
                    v_tail_2970_ = lean_ctor_get(v_x_2967_, 1);
                    v___x_2971_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_head_2969_);
                    if v___x_2971_ == 0 {
                        v_x_2967_ = v_tail_2970_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2971_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(
    mut v_x_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2974_: u8 = 0;
    let mut v_r_2975_: *mut LeanObject = core::ptr::null_mut();
    v_res_2974_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_2973_);
    lean_dec(v_x_2973_);
    v_r_2975_ = lean_box((v_res_2974_) as usize);
    return v_r_2975_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(
    mut v_x_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2977_: u8 = 0;
    let mut v_r_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_2976_);
    lean_dec_ref(v_x_2976_);
    v_r_2978_ = lean_box((v_res_2977_) as usize);
    return v_r_2978_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
    mut v_as_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_2979_) == 0 {
                    v___x_2986_ = lean_box(0);
                    v___x_2987_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                    return v___x_2987_;
                } else {
                    v_head_2988_ = lean_ctor_get(v_as_2979_, 0);
                    lean_inc(v_head_2988_);
                    v_tail_2989_ = lean_ctor_get(v_as_2979_, 1);
                    lean_inc(v_tail_2989_);
                    lean_dec_ref_known(v_as_2979_, 2);
                    v___x_2990_ = l_Lean_Expr_collectFVars(
                        v_head_2988_,
                        v___y_2980_,
                        v___y_2981_,
                        v___y_2982_,
                        v___y_2983_,
                        v___y_2984_,
                    );
                    if lean_obj_tag(v___x_2990_) == 0 {
                        lean_dec_ref_known(v___x_2990_, 1);
                        v_as_2979_ = v_tail_2989_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_2989_);
                        return v___x_2990_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(
    mut v_as_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
        v_as_2992_,
        v___y_2993_,
        v___y_2994_,
        v___y_2995_,
        v___y_2996_,
        v___y_2997_,
    );
    lean_dec(v___y_2997_);
    lean_dec_ref(v___y_2996_);
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    lean_dec(v___y_2993_);
    return v_res_2999_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_collectFVars(
    mut v_p_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_params_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varId_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hId_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_p_3000_) {
                1 => {
                    v_fvarId_3007_ = lean_ctor_get(v_p_3000_, 0);
                    v_isSharedCheck_3018_ = (!lean_is_exclusive(v_p_3000_)) as u8;
                    if v_isSharedCheck_3018_ == 0 {
                        v___x_3009_ = v_p_3000_;
                        v_isShared_3010_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_3007_);
                        lean_dec(v_p_3000_);
                        v___x_3009_ = lean_box(0);
                        v_isShared_3010_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_params_3019_ = lean_ctor_get(v_p_3000_, 2);
                    lean_inc(v_params_3019_);
                    v_fields_3020_ = lean_ctor_get(v_p_3000_, 3);
                    lean_inc(v_fields_3020_);
                    lean_dec_ref_known(v_p_3000_, 4);
                    v___x_3021_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(
                        v_params_3019_,
                        v_a_3001_,
                        v_a_3002_,
                        v_a_3003_,
                        v_a_3004_,
                        v_a_3005_,
                    );
                    if lean_obj_tag(v___x_3021_) == 0 {
                        lean_dec_ref_known(v___x_3021_, 1);
                        v___x_3022_ =
                            l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
                                v_fields_3020_,
                                v_a_3001_,
                                v_a_3002_,
                                v_a_3003_,
                                v_a_3004_,
                                v_a_3005_,
                            );
                        return v___x_3022_;
                    } else {
                        lean_dec(v_fields_3020_);
                        return v___x_3021_;
                    }
                }
                4 => {
                    v_type_3023_ = lean_ctor_get(v_p_3000_, 0);
                    lean_inc_ref(v_type_3023_);
                    v_xs_3024_ = lean_ctor_get(v_p_3000_, 1);
                    lean_inc(v_xs_3024_);
                    lean_dec_ref_known(v_p_3000_, 2);
                    v___x_3025_ = l_Lean_Expr_collectFVars(
                        v_type_3023_,
                        v_a_3001_,
                        v_a_3002_,
                        v_a_3003_,
                        v_a_3004_,
                        v_a_3005_,
                    );
                    if lean_obj_tag(v___x_3025_) == 0 {
                        lean_dec_ref_known(v___x_3025_, 1);
                        v___x_3026_ =
                            l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
                                v_xs_3024_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_,
                            );
                        return v___x_3026_;
                    } else {
                        lean_dec(v_xs_3024_);
                        return v___x_3025_;
                    }
                }
                5 => {
                    v_varId_3027_ = lean_ctor_get(v_p_3000_, 0);
                    lean_inc(v_varId_3027_);
                    v_p_3028_ = lean_ctor_get(v_p_3000_, 1);
                    lean_inc_ref(v_p_3028_);
                    v_hId_3029_ = lean_ctor_get(v_p_3000_, 2);
                    lean_inc(v_hId_3029_);
                    lean_dec_ref_known(v_p_3000_, 3);
                    v___x_3030_ = lean_st_ref_take(v_a_3001_);
                    v___x_3031_ = l_Lean_CollectFVars_State_add(v___x_3030_, v_varId_3027_);
                    v___x_3032_ = l_Lean_CollectFVars_State_add(v___x_3031_, v_hId_3029_);
                    v___x_3033_ = lean_st_ref_set(v_a_3001_, v___x_3032_);
                    v_p_3000_ = v_p_3028_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_e_3035_ = lean_ctor_get(v_p_3000_, 0);
                    lean_inc_ref(v_e_3035_);
                    lean_dec_ref(v_p_3000_);
                    v___x_3036_ = l_Lean_Expr_collectFVars(
                        v_e_3035_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_,
                    );
                    return v___x_3036_;
                }
            },
            1 => {
                v___x_3011_ = lean_st_ref_take(v_a_3001_);
                v___x_3012_ = l_Lean_CollectFVars_State_add(v___x_3011_, v_fvarId_3007_);
                v___x_3013_ = lean_st_ref_set(v_a_3001_, v___x_3012_);
                v___x_3014_ = lean_box(0);
                if v_isShared_3010_ == 0 {
                    lean_ctor_set_tag(v___x_3009_, 0);
                    lean_ctor_set(v___x_3009_, 0, v___x_3014_);
                    v___x_3016_ = v___x_3009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
    mut v_as_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3037_) == 0 {
                    v___x_3044_ = lean_box(0);
                    v___x_3045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3045_, 0, v___x_3044_);
                    return v___x_3045_;
                } else {
                    v_head_3046_ = lean_ctor_get(v_as_3037_, 0);
                    lean_inc(v_head_3046_);
                    v_tail_3047_ = lean_ctor_get(v_as_3037_, 1);
                    lean_inc(v_tail_3047_);
                    lean_dec_ref_known(v_as_3037_, 2);
                    v___x_3048_ = l_Lean_Meta_Match_Pattern_collectFVars(
                        v_head_3046_,
                        v___y_3038_,
                        v___y_3039_,
                        v___y_3040_,
                        v___y_3041_,
                        v___y_3042_,
                    );
                    if lean_obj_tag(v___x_3048_) == 0 {
                        lean_dec_ref_known(v___x_3048_, 1);
                        v_as_3037_ = v_tail_3047_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_3047_);
                        return v___x_3048_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(
    mut v_as_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
    mut v___y_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(
        v_as_3050_,
        v___y_3051_,
        v___y_3052_,
        v___y_3053_,
        v___y_3054_,
        v___y_3055_,
    );
    lean_dec(v___y_3055_);
    lean_dec_ref(v___y_3054_);
    lean_dec(v___y_3053_);
    lean_dec_ref(v___y_3052_);
    lean_dec(v___y_3051_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_Meta_Match_Pattern_collectFVars___boxed(
    mut v_p_3058_: *mut LeanObject,
    mut v_a_3059_: *mut LeanObject,
    mut v_a_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3065_: *mut LeanObject = core::ptr::null_mut();
    v_res_3065_ = l_Lean_Meta_Match_Pattern_collectFVars(
        v_p_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_,
    );
    lean_dec(v_a_3063_);
    lean_dec_ref(v_a_3062_);
    lean_dec(v_a_3061_);
    lean_dec_ref(v_a_3060_);
    lean_dec(v_a_3059_);
    return v_res_3065_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
    mut v_e_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_unused_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3069_ = l_Lean_Expr_hasMVar(v_e_3066_);
                if v___x_3069_ == 0 {
                    v___x_3070_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3070_, 0, v_e_3066_);
                    return v___x_3070_;
                } else {
                    v___x_3071_ = lean_st_ref_get(v___y_3067_);
                    v_mctx_3072_ = lean_ctor_get(v___x_3071_, 0);
                    lean_inc_ref(v_mctx_3072_);
                    lean_dec(v___x_3071_);
                    v___x_3073_ = l_Lean_instantiateMVarsCore(v_mctx_3072_, v_e_3066_);
                    v_fst_3074_ = lean_ctor_get(v___x_3073_, 0);
                    lean_inc(v_fst_3074_);
                    v_snd_3075_ = lean_ctor_get(v___x_3073_, 1);
                    lean_inc(v_snd_3075_);
                    lean_dec_ref(v___x_3073_);
                    v___x_3076_ = lean_st_ref_take(v___y_3067_);
                    v_cache_3077_ = lean_ctor_get(v___x_3076_, 1);
                    v_zetaDeltaFVarIds_3078_ = lean_ctor_get(v___x_3076_, 2);
                    v_postponed_3079_ = lean_ctor_get(v___x_3076_, 3);
                    v_diag_3080_ = lean_ctor_get(v___x_3076_, 4);
                    v_isSharedCheck_3089_ = (!lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3089_ == 0 {
                        v_unused_3090_ = lean_ctor_get(v___x_3076_, 0);
                        lean_dec(v_unused_3090_);
                        v___x_3082_ = v___x_3076_;
                        v_isShared_3083_ = v_isSharedCheck_3089_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3080_);
                        lean_inc(v_postponed_3079_);
                        lean_inc(v_zetaDeltaFVarIds_3078_);
                        lean_inc(v_cache_3077_);
                        lean_dec(v___x_3076_);
                        v___x_3082_ = lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3089_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3083_ == 0 {
                    lean_ctor_set(v___x_3082_, 0, v_snd_3075_);
                    v___x_3085_ = v___x_3082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_snd_3075_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_cache_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_zetaDeltaFVarIds_3078_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_postponed_3079_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_diag_3080_);
                    v___x_3085_ = v_reuseFailAlloc_3088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3086_ = lean_st_ref_set(v___y_3067_, v___x_3085_);
                v___x_3087_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3087_, 0, v_fst_3074_);
                return v___x_3087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(
    mut v_e_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3094_: *mut LeanObject = core::ptr::null_mut();
    v_res_3094_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
            v_e_3091_,
            v___y_3092_,
        );
    lean_dec(v___y_3092_);
    return v_res_3094_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(
    mut v_e_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    v___x_3101_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(
            v_e_3095_,
            v___y_3097_,
        );
    return v___x_3101_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(
    mut v_e_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(
        v_e_3102_,
        v___y_3103_,
        v___y_3104_,
        v___y_3105_,
        v___y_3106_,
    );
    lean_dec(v___y_3106_);
    lean_dec_ref(v___y_3105_);
    lean_dec(v___y_3104_);
    lean_dec_ref(v___y_3103_);
    return v_res_3108_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
    mut v_x_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3109_) == 0 {
                    v___x_3116_ = l_List_reverse___redArg(v_x_3110_);
                    v___x_3117_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3117_, 0, v___x_3116_);
                    return v___x_3117_;
                } else {
                    v_head_3118_ = lean_ctor_get(v_x_3109_, 0);
                    v_tail_3119_ = lean_ctor_get(v_x_3109_, 1);
                    v_isSharedCheck_3129_ = (!lean_is_exclusive(v_x_3109_)) as u8;
                    if v_isSharedCheck_3129_ == 0 {
                        v___x_3121_ = v_x_3109_;
                        v_isShared_3122_ = v_isSharedCheck_3129_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3119_);
                        lean_inc(v_head_3118_);
                        lean_dec(v_x_3109_);
                        v___x_3121_ = lean_box(0);
                        v_isShared_3122_ = v_isSharedCheck_3129_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3123_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_3118_, v___y_3112_);
                v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
                lean_inc(v_a_3124_);
                lean_dec_ref(v___x_3123_);
                if v_isShared_3122_ == 0 {
                    lean_ctor_set(v___x_3121_, 1, v_x_3110_);
                    lean_ctor_set(v___x_3121_, 0, v_a_3124_);
                    v___x_3126_ = v___x_3121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3124_);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_x_3110_);
                    v___x_3126_ = v_reuseFailAlloc_3128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_3109_ = v_tail_3119_;
                v_x_3110_ = v___x_3126_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(
    mut v_x_3130_: *mut LeanObject,
    mut v_x_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_res_3137_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
        v_x_3130_,
        v_x_3131_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
    );
    lean_dec(v___y_3135_);
    lean_dec_ref(v___y_3134_);
    lean_dec(v___y_3133_);
    lean_dec_ref(v___y_3132_);
    return v_res_3137_;
}
pub unsafe fn l_Lean_Meta_Match_instantiatePatternMVars(
    mut v_x_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_a_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_e_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_ctorName_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v_a_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_varId_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hId_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_type_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v_a_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3279_: u8 = 0;
    let mut v_a_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3138_) {
                0 => {
                    v_e_3144_ = lean_ctor_get(v_x_3138_, 0);
                    v_isSharedCheck_3168_ = (!lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3146_ = v_x_3138_;
                        v_isShared_3147_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_e_3144_);
                        lean_dec(v_x_3138_);
                        v___x_3146_ = lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_e_3169_ = lean_ctor_get(v_x_3138_, 0);
                    v_isSharedCheck_3193_ = (!lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3193_ == 0 {
                        v___x_3171_ = v_x_3138_;
                        v_isShared_3172_ = v_isSharedCheck_3193_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_e_3169_);
                        lean_dec(v_x_3138_);
                        v___x_3171_ = lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3193_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_ctorName_3194_ = lean_ctor_get(v_x_3138_, 0);
                    v_us_3195_ = lean_ctor_get(v_x_3138_, 1);
                    v_params_3196_ = lean_ctor_get(v_x_3138_, 2);
                    v_fields_3197_ = lean_ctor_get(v_x_3138_, 3);
                    v_isSharedCheck_3232_ = (!lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3199_ = v_x_3138_;
                        v_isShared_3200_ = v_isSharedCheck_3232_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_fields_3197_);
                        lean_inc(v_params_3196_);
                        lean_inc(v_us_3195_);
                        lean_inc(v_ctorName_3194_);
                        lean_dec(v_x_3138_);
                        v___x_3199_ = lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3232_;
                        state = 13;
                        continue;
                    }
                }
                5 => {
                    v_varId_3233_ = lean_ctor_get(v_x_3138_, 0);
                    v_p_3234_ = lean_ctor_get(v_x_3138_, 1);
                    v_hId_3235_ = lean_ctor_get(v_x_3138_, 2);
                    v_isSharedCheck_3251_ = (!lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3251_ == 0 {
                        v___x_3237_ = v_x_3138_;
                        v_isShared_3238_ = v_isSharedCheck_3251_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_hId_3235_);
                        lean_inc(v_p_3234_);
                        lean_inc(v_varId_3233_);
                        lean_dec(v_x_3138_);
                        v___x_3237_ = lean_box(0);
                        v_isShared_3238_ = v_isSharedCheck_3251_;
                        state = 21;
                        continue;
                    }
                }
                4 => {
                    v_type_3252_ = lean_ctor_get(v_x_3138_, 0);
                    v_xs_3253_ = lean_ctor_get(v_x_3138_, 1);
                    v_isSharedCheck_3288_ = (!lean_is_exclusive(v_x_3138_)) as u8;
                    if v_isSharedCheck_3288_ == 0 {
                        v___x_3255_ = v_x_3138_;
                        v_isShared_3256_ = v_isSharedCheck_3288_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_xs_3253_);
                        lean_inc(v_type_3252_);
                        lean_dec(v_x_3138_);
                        v___x_3255_ = lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3288_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    v___x_3289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3289_, 0, v_x_3138_);
                    return v___x_3289_;
                }
            },
            1 => {
                v___x_3148_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_3144_, v_a_3140_);
                if lean_obj_tag(v___x_3148_) == 0 {
                    v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
                    v_isSharedCheck_3159_ = (!lean_is_exclusive(v___x_3148_)) as u8;
                    if v_isSharedCheck_3159_ == 0 {
                        v___x_3151_ = v___x_3148_;
                        v_isShared_3152_ = v_isSharedCheck_3159_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3149_);
                        lean_dec(v___x_3148_);
                        v___x_3151_ = lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3159_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3146_);
                    v_a_3160_ = lean_ctor_get(v___x_3148_, 0);
                    v_isSharedCheck_3167_ = (!lean_is_exclusive(v___x_3148_)) as u8;
                    if v_isSharedCheck_3167_ == 0 {
                        v___x_3162_ = v___x_3148_;
                        v_isShared_3163_ = v_isSharedCheck_3167_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3160_);
                        lean_dec(v___x_3148_);
                        v___x_3162_ = lean_box(0);
                        v_isShared_3163_ = v_isSharedCheck_3167_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3147_ == 0 {
                    lean_ctor_set(v___x_3146_, 0, v_a_3149_);
                    v___x_3154_ = v___x_3146_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3152_ == 0 {
                    lean_ctor_set(v___x_3151_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3156_;
            }
            5 => {
                if v_isShared_3163_ == 0 {
                    v___x_3165_ = v___x_3162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
                    v___x_3165_ = v_reuseFailAlloc_3166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3165_;
            }
            7 => {
                v___x_3173_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_3169_, v_a_3140_);
                if lean_obj_tag(v___x_3173_) == 0 {
                    v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3184_ = (!lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3184_ == 0 {
                        v___x_3176_ = v___x_3173_;
                        v_isShared_3177_ = v_isSharedCheck_3184_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3174_);
                        lean_dec(v___x_3173_);
                        v___x_3176_ = lean_box(0);
                        v_isShared_3177_ = v_isSharedCheck_3184_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3171_);
                    v_a_3185_ = lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3192_ = (!lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3192_ == 0 {
                        v___x_3187_ = v___x_3173_;
                        v_isShared_3188_ = v_isSharedCheck_3192_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3185_);
                        lean_dec(v___x_3173_);
                        v___x_3187_ = lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3192_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3172_ == 0 {
                    lean_ctor_set(v___x_3171_, 0, v_a_3174_);
                    v___x_3179_ = v___x_3171_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3183_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3177_ == 0 {
                    lean_ctor_set(v___x_3176_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3176_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3181_;
            }
            11 => {
                if v_isShared_3188_ == 0 {
                    v___x_3190_ = v___x_3187_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3191_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3190_;
            }
            13 => {
                v___x_3201_ = lean_box(0);
                v___x_3202_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(
                        v_params_3196_,
                        v___x_3201_,
                        v_a_3139_,
                        v_a_3140_,
                        v_a_3141_,
                        v_a_3142_,
                    );
                if lean_obj_tag(v___x_3202_) == 0 {
                    v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
                    lean_inc(v_a_3203_);
                    lean_dec_ref_known(v___x_3202_, 1);
                    v___x_3204_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_fields_3197_,
                            v___x_3201_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                        );
                    if lean_obj_tag(v___x_3204_) == 0 {
                        v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
                        v_isSharedCheck_3215_ = (!lean_is_exclusive(v___x_3204_)) as u8;
                        if v_isSharedCheck_3215_ == 0 {
                            v___x_3207_ = v___x_3204_;
                            v_isShared_3208_ = v_isSharedCheck_3215_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3205_);
                            lean_dec(v___x_3204_);
                            v___x_3207_ = lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3215_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3203_);
                        lean_del_object(v___x_3199_);
                        lean_dec(v_us_3195_);
                        lean_dec(v_ctorName_3194_);
                        v_a_3216_ = lean_ctor_get(v___x_3204_, 0);
                        v_isSharedCheck_3223_ = (!lean_is_exclusive(v___x_3204_)) as u8;
                        if v_isSharedCheck_3223_ == 0 {
                            v___x_3218_ = v___x_3204_;
                            v_isShared_3219_ = v_isSharedCheck_3223_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3216_);
                            lean_dec(v___x_3204_);
                            v___x_3218_ = lean_box(0);
                            v_isShared_3219_ = v_isSharedCheck_3223_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3199_);
                    lean_dec(v_fields_3197_);
                    lean_dec(v_us_3195_);
                    lean_dec(v_ctorName_3194_);
                    v_a_3224_ = lean_ctor_get(v___x_3202_, 0);
                    v_isSharedCheck_3231_ = (!lean_is_exclusive(v___x_3202_)) as u8;
                    if v_isSharedCheck_3231_ == 0 {
                        v___x_3226_ = v___x_3202_;
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3224_);
                        lean_dec(v___x_3202_);
                        v___x_3226_ = lean_box(0);
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 19;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3200_ == 0 {
                    lean_ctor_set(v___x_3199_, 3, v_a_3205_);
                    lean_ctor_set(v___x_3199_, 2, v_a_3203_);
                    v___x_3210_ = v___x_3199_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_ctorName_3194_);
                    lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_us_3195_);
                    lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_a_3203_);
                    lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_a_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3214_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3208_ == 0 {
                    lean_ctor_set(v___x_3207_, 0, v___x_3210_);
                    v___x_3212_ = v___x_3207_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
                    v___x_3212_ = v_reuseFailAlloc_3213_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3212_;
            }
            17 => {
                if v_isShared_3219_ == 0 {
                    v___x_3221_ = v___x_3218_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3221_;
            }
            19 => {
                if v_isShared_3227_ == 0 {
                    v___x_3229_ = v___x_3226_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3229_;
            }
            21 => {
                v___x_3239_ = l_Lean_Meta_Match_instantiatePatternMVars(
                    v_p_3234_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_,
                );
                if lean_obj_tag(v___x_3239_) == 0 {
                    v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
                    v_isSharedCheck_3250_ = (!lean_is_exclusive(v___x_3239_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v___x_3242_ = v___x_3239_;
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_3240_);
                        lean_dec(v___x_3239_);
                        v___x_3242_ = lean_box(0);
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3237_);
                    lean_dec(v_hId_3235_);
                    lean_dec(v_varId_3233_);
                    return v___x_3239_;
                }
            }
            22 => {
                if v_isShared_3238_ == 0 {
                    lean_ctor_set(v___x_3237_, 1, v_a_3240_);
                    v___x_3245_ = v___x_3237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = lean_alloc_ctor(5, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_varId_3233_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_a_3240_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_hId_3235_);
                    v___x_3245_ = v_reuseFailAlloc_3249_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3243_ == 0 {
                    lean_ctor_set(v___x_3242_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3242_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3247_;
            }
            25 => {
                v___x_3257_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3252_, v_a_3140_);
                if lean_obj_tag(v___x_3257_) == 0 {
                    v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                    lean_inc(v_a_3258_);
                    lean_dec_ref_known(v___x_3257_, 1);
                    v___x_3259_ = lean_box(0);
                    v___x_3260_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_xs_3253_,
                            v___x_3259_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                        );
                    if lean_obj_tag(v___x_3260_) == 0 {
                        v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
                        v_isSharedCheck_3271_ = (!lean_is_exclusive(v___x_3260_)) as u8;
                        if v_isSharedCheck_3271_ == 0 {
                            v___x_3263_ = v___x_3260_;
                            v_isShared_3264_ = v_isSharedCheck_3271_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_3261_);
                            lean_dec(v___x_3260_);
                            v___x_3263_ = lean_box(0);
                            v_isShared_3264_ = v_isSharedCheck_3271_;
                            state = 26;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3258_);
                        lean_del_object(v___x_3255_);
                        v_a_3272_ = lean_ctor_get(v___x_3260_, 0);
                        v_isSharedCheck_3279_ = (!lean_is_exclusive(v___x_3260_)) as u8;
                        if v_isSharedCheck_3279_ == 0 {
                            v___x_3274_ = v___x_3260_;
                            v_isShared_3275_ = v_isSharedCheck_3279_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_3272_);
                            lean_dec(v___x_3260_);
                            v___x_3274_ = lean_box(0);
                            v_isShared_3275_ = v_isSharedCheck_3279_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3255_);
                    lean_dec(v_xs_3253_);
                    v_a_3280_ = lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3287_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3282_ = v___x_3257_;
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_3280_);
                        lean_dec(v___x_3257_);
                        v___x_3282_ = lean_box(0);
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 31;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_3256_ == 0 {
                    lean_ctor_set(v___x_3255_, 1, v_a_3261_);
                    lean_ctor_set(v___x_3255_, 0, v_a_3258_);
                    v___x_3266_ = v___x_3255_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3258_);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_a_3261_);
                    v___x_3266_ = v_reuseFailAlloc_3270_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3264_ == 0 {
                    lean_ctor_set(v___x_3263_, 0, v___x_3266_);
                    v___x_3268_ = v___x_3263_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
                    v___x_3268_ = v_reuseFailAlloc_3269_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3268_;
            }
            29 => {
                if v_isShared_3275_ == 0 {
                    v___x_3277_ = v___x_3274_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
                    v___x_3277_ = v_reuseFailAlloc_3278_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3277_;
            }
            31 => {
                if v_isShared_3283_ == 0 {
                    v___x_3285_ = v___x_3282_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
                    v___x_3285_ = v_reuseFailAlloc_3286_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
    mut v_x_3290_: *mut LeanObject,
    mut v_x_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3303_: u8 = 0;
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3290_) == 0 {
                    v___x_3297_ = l_List_reverse___redArg(v_x_3291_);
                    v___x_3298_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3298_, 0, v___x_3297_);
                    return v___x_3298_;
                } else {
                    v_head_3299_ = lean_ctor_get(v_x_3290_, 0);
                    v_tail_3300_ = lean_ctor_get(v_x_3290_, 1);
                    v_isSharedCheck_3318_ = (!lean_is_exclusive(v_x_3290_)) as u8;
                    if v_isSharedCheck_3318_ == 0 {
                        v___x_3302_ = v_x_3290_;
                        v_isShared_3303_ = v_isSharedCheck_3318_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3300_);
                        lean_inc(v_head_3299_);
                        lean_dec(v_x_3290_);
                        v___x_3302_ = lean_box(0);
                        v_isShared_3303_ = v_isSharedCheck_3318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3304_ = l_Lean_Meta_Match_instantiatePatternMVars(
                    v_head_3299_,
                    v___y_3292_,
                    v___y_3293_,
                    v___y_3294_,
                    v___y_3295_,
                );
                if lean_obj_tag(v___x_3304_) == 0 {
                    v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
                    lean_inc(v_a_3305_);
                    lean_dec_ref_known(v___x_3304_, 1);
                    if v_isShared_3303_ == 0 {
                        lean_ctor_set(v___x_3302_, 1, v_x_3291_);
                        lean_ctor_set(v___x_3302_, 0, v_a_3305_);
                        v___x_3307_ = v___x_3302_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3305_);
                        lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_x_3291_);
                        v___x_3307_ = v_reuseFailAlloc_3309_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3302_);
                    lean_dec(v_tail_3300_);
                    lean_dec(v_x_3291_);
                    v_a_3310_ = lean_ctor_get(v___x_3304_, 0);
                    v_isSharedCheck_3317_ = (!lean_is_exclusive(v___x_3304_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3312_ = v___x_3304_;
                        v_isShared_3313_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3310_);
                        lean_dec(v___x_3304_);
                        v___x_3312_ = lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3290_ = v_tail_3300_;
                v_x_3291_ = v___x_3307_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3313_ == 0 {
                    v___x_3315_ = v___x_3312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
                    v___x_3315_ = v_reuseFailAlloc_3316_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(
    mut v_x_3319_: *mut LeanObject,
    mut v_x_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3326_: *mut LeanObject = core::ptr::null_mut();
    v_res_3326_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
        v_x_3319_,
        v_x_3320_,
        v___y_3321_,
        v___y_3322_,
        v___y_3323_,
        v___y_3324_,
    );
    lean_dec(v___y_3324_);
    lean_dec_ref(v___y_3323_);
    lean_dec(v___y_3322_);
    lean_dec_ref(v___y_3321_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_Meta_Match_instantiatePatternMVars___boxed(
    mut v_x_3327_: *mut LeanObject,
    mut v_a_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Meta_Match_instantiatePatternMVars(
        v_x_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_,
    );
    lean_dec(v_a_3331_);
    lean_dec_ref(v_a_3330_);
    lean_dec(v_a_3329_);
    lean_dec_ref(v_a_3328_);
    return v_res_3333_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
    mut v_as_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3339_) == 0 {
                    v___x_3346_ = lean_box(0);
                    v___x_3347_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3347_, 0, v___x_3346_);
                    return v___x_3347_;
                } else {
                    v_head_3348_ = lean_ctor_get(v_as_3339_, 0);
                    lean_inc(v_head_3348_);
                    v_tail_3349_ = lean_ctor_get(v_as_3339_, 1);
                    lean_inc(v_tail_3349_);
                    lean_dec_ref_known(v_as_3339_, 2);
                    v___x_3350_ = l_Lean_LocalDecl_collectFVars(
                        v_head_3348_,
                        v___y_3340_,
                        v___y_3341_,
                        v___y_3342_,
                        v___y_3343_,
                        v___y_3344_,
                    );
                    if lean_obj_tag(v___x_3350_) == 0 {
                        lean_dec_ref_known(v___x_3350_, 1);
                        v_as_3339_ = v_tail_3349_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_3349_);
                        return v___x_3350_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(
    mut v_as_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
        v_as_3352_,
        v___y_3353_,
        v___y_3354_,
        v___y_3355_,
        v___y_3356_,
        v___y_3357_,
    );
    lean_dec(v___y_3357_);
    lean_dec_ref(v___y_3356_);
    lean_dec(v___y_3355_);
    lean_dec_ref(v___y_3354_);
    lean_dec(v___y_3353_);
    return v_res_3359_;
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
    mut v_as_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3360_) == 0 {
                    v___x_3367_ = lean_box(0);
                    v___x_3368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3368_, 0, v___x_3367_);
                    return v___x_3368_;
                } else {
                    v_head_3369_ = lean_ctor_get(v_as_3360_, 0);
                    lean_inc(v_head_3369_);
                    v_tail_3370_ = lean_ctor_get(v_as_3360_, 1);
                    lean_inc(v_tail_3370_);
                    lean_dec_ref_known(v_as_3360_, 2);
                    v___x_3371_ = l_Lean_Meta_Match_Pattern_collectFVars(
                        v_head_3369_,
                        v___y_3361_,
                        v___y_3362_,
                        v___y_3363_,
                        v___y_3364_,
                        v___y_3365_,
                    );
                    if lean_obj_tag(v___x_3371_) == 0 {
                        lean_dec_ref_known(v___x_3371_, 1);
                        v_as_3360_ = v_tail_3370_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_3370_);
                        return v___x_3371_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(
    mut v_as_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3380_: *mut LeanObject = core::ptr::null_mut();
    v_res_3380_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
        v_as_3373_,
        v___y_3374_,
        v___y_3375_,
        v___y_3376_,
        v___y_3377_,
        v___y_3378_,
    );
    lean_dec(v___y_3378_);
    lean_dec_ref(v___y_3377_);
    lean_dec(v___y_3376_);
    lean_dec_ref(v___y_3375_);
    lean_dec(v___y_3374_);
    return v_res_3380_;
}
pub unsafe fn l_Lean_Meta_Match_AltLHS_collectFVars(
    mut v_altLHS_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarDecls_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v_fvarDecls_3388_ = lean_ctor_get(v_altLHS_3381_, 1);
    lean_inc(v_fvarDecls_3388_);
    v_patterns_3389_ = lean_ctor_get(v_altLHS_3381_, 2);
    lean_inc(v_patterns_3389_);
    lean_dec_ref(v_altLHS_3381_);
    v___x_3390_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(
        v_fvarDecls_3388_,
        v_a_3382_,
        v_a_3383_,
        v_a_3384_,
        v_a_3385_,
        v_a_3386_,
    );
    if lean_obj_tag(v___x_3390_) == 0 {
        let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3390_, 1);
        v___x_3391_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(
            v_patterns_3389_,
            v_a_3382_,
            v_a_3383_,
            v_a_3384_,
            v_a_3385_,
            v_a_3386_,
        );
        return v___x_3391_;
    } else {
        lean_dec(v_patterns_3389_);
        return v___x_3390_;
    }
}
pub unsafe fn l_Lean_Meta_Match_AltLHS_collectFVars___boxed(
    mut v_altLHS_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
    mut v_a_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3399_: *mut LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_Lean_Meta_Match_AltLHS_collectFVars(
        v_altLHS_3392_,
        v_a_3393_,
        v_a_3394_,
        v_a_3395_,
        v_a_3396_,
        v_a_3397_,
    );
    lean_dec(v_a_3397_);
    lean_dec_ref(v_a_3396_);
    lean_dec(v_a_3395_);
    lean_dec_ref(v_a_3394_);
    lean_dec(v_a_3393_);
    return v_res_3399_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(
    mut v_localDecl_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_index_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bi_3407_: u8 = 0;
    let mut v_kind_3408_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_index_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_3430_: u8 = 0;
    let mut v_kind_3431_: u8 = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_isSharedCheck_3449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_localDecl_3400_) == 0 {
                    v_index_3403_ = lean_ctor_get(v_localDecl_3400_, 0);
                    v_fvarId_3404_ = lean_ctor_get(v_localDecl_3400_, 1);
                    v_userName_3405_ = lean_ctor_get(v_localDecl_3400_, 2);
                    v_type_3406_ = lean_ctor_get(v_localDecl_3400_, 3);
                    v_bi_3407_ = lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    v_kind_3408_ = lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    v_isSharedCheck_3424_ = (!lean_is_exclusive(v_localDecl_3400_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3410_ = v_localDecl_3400_;
                        v_isShared_3411_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_type_3406_);
                        lean_inc(v_userName_3405_);
                        lean_inc(v_fvarId_3404_);
                        lean_inc(v_index_3403_);
                        lean_dec(v_localDecl_3400_);
                        v___x_3410_ = lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_index_3425_ = lean_ctor_get(v_localDecl_3400_, 0);
                    v_fvarId_3426_ = lean_ctor_get(v_localDecl_3400_, 1);
                    v_userName_3427_ = lean_ctor_get(v_localDecl_3400_, 2);
                    v_type_3428_ = lean_ctor_get(v_localDecl_3400_, 3);
                    v_value_3429_ = lean_ctor_get(v_localDecl_3400_, 4);
                    v_nondep_3430_ = lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_kind_3431_ = lean_ctor_get_uint8(
                        v_localDecl_3400_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    );
                    v_isSharedCheck_3449_ = (!lean_is_exclusive(v_localDecl_3400_)) as u8;
                    if v_isSharedCheck_3449_ == 0 {
                        v___x_3433_ = v_localDecl_3400_;
                        v_isShared_3434_ = v_isSharedCheck_3449_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_value_3429_);
                        lean_inc(v_type_3428_);
                        lean_inc(v_userName_3427_);
                        lean_inc(v_fvarId_3426_);
                        lean_inc(v_index_3425_);
                        lean_dec(v_localDecl_3400_);
                        v___x_3433_ = lean_box(0);
                        v_isShared_3434_ = v_isSharedCheck_3449_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3412_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3406_, v___y_3401_);
                v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
                v_isSharedCheck_3423_ = (!lean_is_exclusive(v___x_3412_)) as u8;
                if v_isSharedCheck_3423_ == 0 {
                    v___x_3415_ = v___x_3412_;
                    v_isShared_3416_ = v_isSharedCheck_3423_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3413_);
                    lean_dec(v___x_3412_);
                    v___x_3415_ = lean_box(0);
                    v_isShared_3416_ = v_isSharedCheck_3423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3411_ == 0 {
                    lean_ctor_set(v___x_3410_, 3, v_a_3413_);
                    v___x_3418_ = v___x_3410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_index_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_fvarId_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_userName_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_a_3413_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3422_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_bi_3407_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3422_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_kind_3408_,
                    );
                    v___x_3418_ = v_reuseFailAlloc_3422_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3416_ == 0 {
                    lean_ctor_set(v___x_3415_, 0, v___x_3418_);
                    v___x_3420_ = v___x_3415_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
                    v___x_3420_ = v_reuseFailAlloc_3421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3420_;
            }
            5 => {
                v___x_3435_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_3428_, v___y_3401_);
                v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
                lean_inc(v_a_3436_);
                lean_dec_ref(v___x_3435_);
                v___x_3437_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_3429_, v___y_3401_);
                v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
                v_isSharedCheck_3448_ = (!lean_is_exclusive(v___x_3437_)) as u8;
                if v_isSharedCheck_3448_ == 0 {
                    v___x_3440_ = v___x_3437_;
                    v_isShared_3441_ = v_isSharedCheck_3448_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_a_3438_);
                    lean_dec(v___x_3437_);
                    v___x_3440_ = lean_box(0);
                    v_isShared_3441_ = v_isSharedCheck_3448_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3434_ == 0 {
                    lean_ctor_set(v___x_3433_, 4, v_a_3438_);
                    lean_ctor_set(v___x_3433_, 3, v_a_3436_);
                    v___x_3443_ = v___x_3433_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 5, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_index_3425_);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_fvarId_3426_);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_userName_3427_);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_a_3436_);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_a_3438_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3447_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_nondep_3430_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3447_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v_kind_3431_,
                    );
                    v___x_3443_ = v_reuseFailAlloc_3447_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3441_ == 0 {
                    lean_ctor_set(v___x_3440_, 0, v___x_3443_);
                    v___x_3445_ = v___x_3440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(
    mut v_localDecl_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3453_: *mut LeanObject = core::ptr::null_mut();
    v_res_3453_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_3450_, v___y_3451_);
    lean_dec(v___y_3451_);
    return v_res_3453_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
    mut v_x_3454_: *mut LeanObject,
    mut v_x_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3454_) == 0 {
                    v___x_3461_ = l_List_reverse___redArg(v_x_3455_);
                    v___x_3462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3462_, 0, v___x_3461_);
                    return v___x_3462_;
                } else {
                    v_head_3463_ = lean_ctor_get(v_x_3454_, 0);
                    v_tail_3464_ = lean_ctor_get(v_x_3454_, 1);
                    v_isSharedCheck_3482_ = (!lean_is_exclusive(v_x_3454_)) as u8;
                    if v_isSharedCheck_3482_ == 0 {
                        v___x_3466_ = v_x_3454_;
                        v_isShared_3467_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3464_);
                        lean_inc(v_head_3463_);
                        lean_dec(v_x_3454_);
                        v___x_3466_ = lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3468_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_3463_, v___y_3457_);
                if lean_obj_tag(v___x_3468_) == 0 {
                    v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
                    lean_inc(v_a_3469_);
                    lean_dec_ref_known(v___x_3468_, 1);
                    if v_isShared_3467_ == 0 {
                        lean_ctor_set(v___x_3466_, 1, v_x_3455_);
                        lean_ctor_set(v___x_3466_, 0, v_a_3469_);
                        v___x_3471_ = v___x_3466_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3469_);
                        lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_x_3455_);
                        v___x_3471_ = v_reuseFailAlloc_3473_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3466_);
                    lean_dec(v_tail_3464_);
                    lean_dec(v_x_3455_);
                    v_a_3474_ = lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3481_ = (!lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3468_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3474_);
                        lean_dec(v___x_3468_);
                        v___x_3476_ = lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3454_ = v_tail_3464_;
                v_x_3455_ = v___x_3471_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(
    mut v_x_3483_: *mut LeanObject,
    mut v_x_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3490_: *mut LeanObject = core::ptr::null_mut();
    v_res_3490_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
        v_x_3483_,
        v_x_3484_,
        v___y_3485_,
        v___y_3486_,
        v___y_3487_,
        v___y_3488_,
    );
    lean_dec(v___y_3488_);
    lean_dec_ref(v___y_3487_);
    lean_dec(v___y_3486_);
    lean_dec_ref(v___y_3485_);
    return v_res_3490_;
}
pub unsafe fn l_Lean_Meta_Match_instantiateAltLHSMVars(
    mut v_altLHS_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_a_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3529_: u8 = 0;
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3497_ = lean_ctor_get(v_altLHS_3491_, 0);
                v_fvarDecls_3498_ = lean_ctor_get(v_altLHS_3491_, 1);
                v_patterns_3499_ = lean_ctor_get(v_altLHS_3491_, 2);
                v_isSharedCheck_3534_ = (!lean_is_exclusive(v_altLHS_3491_)) as u8;
                if v_isSharedCheck_3534_ == 0 {
                    v___x_3501_ = v_altLHS_3491_;
                    v_isShared_3502_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_patterns_3499_);
                    lean_inc(v_fvarDecls_3498_);
                    lean_inc(v_ref_3497_);
                    lean_dec(v_altLHS_3491_);
                    v___x_3501_ = lean_box(0);
                    v_isShared_3502_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3503_ = lean_box(0);
                v___x_3504_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(
                        v_fvarDecls_3498_,
                        v___x_3503_,
                        v_a_3492_,
                        v_a_3493_,
                        v_a_3494_,
                        v_a_3495_,
                    );
                if lean_obj_tag(v___x_3504_) == 0 {
                    v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
                    lean_inc(v_a_3505_);
                    lean_dec_ref_known(v___x_3504_, 1);
                    v___x_3506_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(
                            v_patterns_3499_,
                            v___x_3503_,
                            v_a_3492_,
                            v_a_3493_,
                            v_a_3494_,
                            v_a_3495_,
                        );
                    if lean_obj_tag(v___x_3506_) == 0 {
                        v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
                        v_isSharedCheck_3517_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3517_ == 0 {
                            v___x_3509_ = v___x_3506_;
                            v_isShared_3510_ = v_isSharedCheck_3517_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3507_);
                            lean_dec(v___x_3506_);
                            v___x_3509_ = lean_box(0);
                            v_isShared_3510_ = v_isSharedCheck_3517_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3505_);
                        lean_del_object(v___x_3501_);
                        lean_dec(v_ref_3497_);
                        v_a_3518_ = lean_ctor_get(v___x_3506_, 0);
                        v_isSharedCheck_3525_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3525_ == 0 {
                            v___x_3520_ = v___x_3506_;
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3518_);
                            lean_dec(v___x_3506_);
                            v___x_3520_ = lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3501_);
                    lean_dec(v_patterns_3499_);
                    lean_dec(v_ref_3497_);
                    v_a_3526_ = lean_ctor_get(v___x_3504_, 0);
                    v_isSharedCheck_3533_ = (!lean_is_exclusive(v___x_3504_)) as u8;
                    if v_isSharedCheck_3533_ == 0 {
                        v___x_3528_ = v___x_3504_;
                        v_isShared_3529_ = v_isSharedCheck_3533_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3526_);
                        lean_dec(v___x_3504_);
                        v___x_3528_ = lean_box(0);
                        v_isShared_3529_ = v_isSharedCheck_3533_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3502_ == 0 {
                    lean_ctor_set(v___x_3501_, 2, v_a_3507_);
                    lean_ctor_set(v___x_3501_, 1, v_a_3505_);
                    v___x_3512_ = v___x_3501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_ref_3497_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_a_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_a_3507_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3510_ == 0 {
                    lean_ctor_set(v___x_3509_, 0, v___x_3512_);
                    v___x_3514_ = v___x_3509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
                    v___x_3514_ = v_reuseFailAlloc_3515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3514_;
            }
            5 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3523_;
            }
            7 => {
                if v_isShared_3529_ == 0 {
                    v___x_3531_ = v___x_3528_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(
    mut v_altLHS_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lean_Meta_Match_instantiateAltLHSMVars(
        v_altLHS_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
        v_a_3539_,
    );
    lean_dec(v_a_3539_);
    lean_dec_ref(v_a_3538_);
    lean_dec(v_a_3537_);
    lean_dec_ref(v_a_3536_);
    return v_res_3541_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(
    mut v_localDecl_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_3542_, v___y_3544_);
    return v___x_3548_;
}
pub unsafe fn l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(
    mut v_localDecl_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3555_: *mut LeanObject = core::ptr::null_mut();
    v_res_3555_ =
        l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(
            v_localDecl_3549_,
            v___y_3550_,
            v___y_3551_,
            v___y_3552_,
            v___y_3553_,
        );
    lean_dec(v___y_3553_);
    lean_dec_ref(v___y_3552_);
    lean_dec(v___y_3551_);
    lean_dec_ref(v___y_3550_);
    return v_res_3555_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1() -> *mut LeanObject {
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Meta_Match_instInhabitedAlt_default___closed__0;
    v___x_3559_ = lean_box(0);
    v___x_3560_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once),
        _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2,
    );
    v___x_3561_ = lean_unsigned_to_nat(0);
    v___x_3562_ = lean_box(0);
    v___x_3563_ = lean_alloc_ctor(0, 7, (0) as u32);
    lean_ctor_set(v___x_3563_, 0, v___x_3562_);
    lean_ctor_set(v___x_3563_, 1, v___x_3561_);
    lean_ctor_set(v___x_3563_, 2, v___x_3560_);
    lean_ctor_set(v___x_3563_, 3, v___x_3559_);
    lean_ctor_set(v___x_3563_, 4, v___x_3559_);
    lean_ctor_set(v___x_3563_, 5, v___x_3559_);
    lean_ctor_set(v___x_3563_, 6, v___x_3558_);
    return v___x_3563_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt_default() -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    v___x_3564_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once),
        _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1,
    );
    return v___x_3564_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedAlt() -> *mut LeanObject {
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    v___x_3565_ = l_Lean_Meta_Match_instInhabitedAlt_default;
    return v___x_3565_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
    mut v_msgData_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    v___x_3572_ = lean_st_ref_get(v___y_3570_);
    v_env_3573_ = lean_ctor_get(v___x_3572_, 0);
    lean_inc_ref(v_env_3573_);
    lean_dec(v___x_3572_);
    v___x_3574_ = lean_st_ref_get(v___y_3568_);
    v_mctx_3575_ = lean_ctor_get(v___x_3574_, 0);
    lean_inc_ref(v_mctx_3575_);
    lean_dec(v___x_3574_);
    v_lctx_3576_ = lean_ctor_get(v___y_3567_, 2);
    v_options_3577_ = lean_ctor_get(v___y_3569_, 2);
    lean_inc_ref(v_options_3577_);
    lean_inc_ref(v_lctx_3576_);
    v___x_3578_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3578_, 0, v_env_3573_);
    lean_ctor_set(v___x_3578_, 1, v_mctx_3575_);
    lean_ctor_set(v___x_3578_, 2, v_lctx_3576_);
    lean_ctor_set(v___x_3578_, 3, v_options_3577_);
    v___x_3579_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3579_, 0, v___x_3578_);
    lean_ctor_set(v___x_3579_, 1, v_msgData_3566_);
    v___x_3580_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3580_, 0, v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(
    mut v_msgData_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3587_: *mut LeanObject = core::ptr::null_mut();
    v_res_3587_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
        v_msgData_3581_,
        v___y_3582_,
        v___y_3583_,
        v___y_3584_,
        v___y_3585_,
    );
    lean_dec(v___y_3585_);
    lean_dec_ref(v___y_3584_);
    lean_dec(v___y_3583_);
    lean_dec_ref(v___y_3582_);
    return v_res_3587_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(
    mut v_decls_3588_: *mut LeanObject,
    mut v_x_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
    mut v___y_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
    mut v___y_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_a_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(
                    lean_box(0),
                    v_decls_3588_,
                    v_x_3589_,
                    v___y_3590_,
                    v___y_3591_,
                    v___y_3592_,
                    v___y_3593_,
                );
                if lean_obj_tag(v___x_3595_) == 0 {
                    v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3603_ = (!lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3603_ == 0 {
                        v___x_3598_ = v___x_3595_;
                        v_isShared_3599_ = v_isSharedCheck_3603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3596_);
                        lean_dec(v___x_3595_);
                        v___x_3598_ = lean_box(0);
                        v_isShared_3599_ = v_isSharedCheck_3603_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3604_ = lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3611_ = (!lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3611_ == 0 {
                        v___x_3606_ = v___x_3595_;
                        v_isShared_3607_ = v_isSharedCheck_3611_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3604_);
                        lean_dec(v___x_3595_);
                        v___x_3606_ = lean_box(0);
                        v_isShared_3607_ = v_isSharedCheck_3611_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3599_ == 0 {
                    v___x_3601_ = v___x_3598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
                    v___x_3601_ = v_reuseFailAlloc_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3601_;
            }
            3 => {
                if v_isShared_3607_ == 0 {
                    v___x_3609_ = v___x_3606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
                    v___x_3609_ = v_reuseFailAlloc_3610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(
    mut v_decls_3612_: *mut LeanObject,
    mut v_x_3613_: *mut LeanObject,
    mut v___y_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
    mut v___y_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3619_: *mut LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_3612_, v_x_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
    lean_dec(v___y_3617_);
    lean_dec_ref(v___y_3616_);
    lean_dec(v___y_3615_);
    lean_dec_ref(v___y_3614_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(
    mut v_00_u03b1_3620_: *mut LeanObject,
    mut v_decls_3621_: *mut LeanObject,
    mut v_x_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    v___x_3628_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(
    mut v_00_u03b1_3629_: *mut LeanObject,
    mut v_decls_3630_: *mut LeanObject,
    mut v_x_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3637_: *mut LeanObject = core::ptr::null_mut();
    v_res_3637_ =
        l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(
            v_00_u03b1_3629_,
            v_decls_3630_,
            v_x_3631_,
            v___y_3632_,
            v___y_3633_,
            v___y_3634_,
            v___y_3635_,
        );
    lean_dec(v___y_3635_);
    lean_dec_ref(v___y_3634_);
    lean_dec(v___y_3633_);
    lean_dec_ref(v___y_3632_);
    return v_res_3637_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    v___x_3639_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0;
    v___x_3640_ = l_Lean_stringToMessageData(v___x_3639_);
    return v___x_3640_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    v___x_3642_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2;
    v___x_3643_ = l_Lean_stringToMessageData(v___x_3642_);
    return v___x_3643_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
    mut v_as_x27_3644_: *mut LeanObject,
    mut v_b_3645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3644_) == 0 {
                    v___x_3647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3647_, 0, v_b_3645_);
                    return v___x_3647_;
                } else {
                    v_head_3648_ = lean_ctor_get(v_as_x27_3644_, 0);
                    v_tail_3649_ = lean_ctor_get(v_as_x27_3644_, 1);
                    v_fst_3650_ = lean_ctor_get(v_head_3648_, 0);
                    v_snd_3651_ = lean_ctor_get(v_head_3648_, 1);
                    v___x_3652_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
                    v___x_3653_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3653_, 0, v_b_3645_);
                    lean_ctor_set(v___x_3653_, 1, v___x_3652_);
                    lean_inc(v_fst_3650_);
                    v___x_3654_ = l_Lean_MessageData_ofExpr(v_fst_3650_);
                    v___x_3655_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                    lean_ctor_set(v___x_3655_, 1, v___x_3654_);
                    v___x_3656_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
                    v___x_3657_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3657_, 0, v___x_3655_);
                    lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                    lean_inc(v_snd_3651_);
                    v___x_3658_ = l_Lean_MessageData_ofExpr(v_snd_3651_);
                    v___x_3659_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3659_, 0, v___x_3657_);
                    lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                    v_as_x27_3644_ = v_tail_3649_;
                    v_b_3645_ = v___x_3659_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(
    mut v_as_x27_3661_: *mut LeanObject,
    mut v_b_3662_: *mut LeanObject,
    mut v___y_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3664_: *mut LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_as_x27_3661_,
        v_b_3662_,
    );
    lean_dec(v_as_x27_3661_);
    return v_res_3664_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___lam__0(
    mut v_cnstrs_3665_: *mut LeanObject,
    mut v_msg_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_cnstrs_3665_,
        v_msg_3666_,
    );
    v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
    lean_inc(v_a_3673_);
    lean_dec_ref(v___x_3672_);
    v___x_3674_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
        v_a_3673_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
    );
    return v___x_3674_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(
    mut v_cnstrs_3675_: *mut LeanObject,
    mut v_msg_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3682_: *mut LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(
        v_cnstrs_3675_,
        v_msg_3676_,
        v___y_3677_,
        v___y_3678_,
        v___y_3679_,
        v___y_3680_,
    );
    lean_dec(v___y_3680_);
    lean_dec_ref(v___y_3679_);
    lean_dec(v___y_3678_);
    lean_dec_ref(v___y_3677_);
    lean_dec(v_cnstrs_3675_);
    return v_res_3682_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
    mut v_a_3683_: *mut LeanObject,
    mut v_a_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3683_) == 0 {
                    v___x_3685_ = l_List_reverse___redArg(v_a_3684_);
                    return v___x_3685_;
                } else {
                    v_head_3686_ = lean_ctor_get(v_a_3683_, 0);
                    v_tail_3687_ = lean_ctor_get(v_a_3683_, 1);
                    v_isSharedCheck_3695_ = (!lean_is_exclusive(v_a_3683_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3689_ = v_a_3683_;
                        v_isShared_3690_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3687_);
                        lean_inc(v_head_3686_);
                        lean_dec(v_a_3683_);
                        v___x_3689_ = lean_box(0);
                        v_isShared_3690_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3690_ == 0 {
                    lean_ctor_set(v___x_3689_, 1, v_a_3684_);
                    v___x_3692_ = v___x_3689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_head_3686_);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_a_3684_);
                    v___x_3692_ = v_reuseFailAlloc_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3683_ = v_tail_3687_;
                v_a_3684_ = v___x_3692_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(
    mut v_a_3699_: *mut LeanObject,
    mut v_a_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3699_) == 0 {
                    v___x_3701_ = l_List_reverse___redArg(v_a_3700_);
                    return v___x_3701_;
                } else {
                    v_head_3702_ = lean_ctor_get(v_a_3699_, 0);
                    v_tail_3703_ = lean_ctor_get(v_a_3699_, 1);
                    v_isSharedCheck_3720_ = (!lean_is_exclusive(v_a_3699_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3705_ = v_a_3699_;
                        v_isShared_3706_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3703_);
                        lean_inc(v_head_3702_);
                        lean_dec(v_a_3699_);
                        v___x_3705_ = lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_3702_);
                v___x_3707_ = l_Lean_LocalDecl_toExpr(v_head_3702_);
                v___x_3708_ = l_Lean_MessageData_ofExpr(v___x_3707_);
                v___x_3709_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
                v___x_3710_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3710_, 0, v___x_3708_);
                lean_ctor_set(v___x_3710_, 1, v___x_3709_);
                v___x_3711_ = l_Lean_LocalDecl_type(v_head_3702_);
                lean_dec(v_head_3702_);
                v___x_3712_ = l_Lean_MessageData_ofExpr(v___x_3711_);
                v___x_3713_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3713_, 0, v___x_3710_);
                lean_ctor_set(v___x_3713_, 1, v___x_3712_);
                v___x_3714_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                );
                v___x_3715_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3715_, 0, v___x_3713_);
                lean_ctor_set(v___x_3715_, 1, v___x_3714_);
                if v_isShared_3706_ == 0 {
                    lean_ctor_set(v___x_3705_, 1, v_a_3700_);
                    lean_ctor_set(v___x_3705_, 0, v___x_3715_);
                    v___x_3717_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3715_);
                    lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_a_3700_);
                    v___x_3717_ = v_reuseFailAlloc_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3699_ = v_tail_3703_;
                v_a_3700_ = v___x_3717_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1() -> *mut LeanObject {
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_Meta_Match_Alt_toMessageData___closed__0;
    v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3() -> *mut LeanObject {
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    v___x_3725_ = l_Lean_Meta_Match_Alt_toMessageData___closed__2;
    v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
    return v___x_3726_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5() -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    v___x_3728_ = l_Lean_Meta_Match_Alt_toMessageData___closed__4;
    v___x_3729_ = l_Lean_stringToMessageData(v___x_3728_);
    return v___x_3729_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7() -> *mut LeanObject {
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    v___x_3731_ = l_Lean_Meta_Match_Alt_toMessageData___closed__6;
    v___x_3732_ = l_Lean_stringToMessageData(v___x_3731_);
    return v___x_3732_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData(
    mut v_alt_3733_: *mut LeanObject,
    mut v_a_3734_: *mut LeanObject,
    mut v_a_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
    mut v_a_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rhs_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rhs_3739_ = lean_ctor_get(v_alt_3733_, 2);
                lean_inc_ref(v_rhs_3739_);
                v_fvarDecls_3740_ = lean_ctor_get(v_alt_3733_, 3);
                lean_inc(v_fvarDecls_3740_);
                v_patterns_3741_ = lean_ctor_get(v_alt_3733_, 4);
                lean_inc(v_patterns_3741_);
                v_cnstrs_3742_ = lean_ctor_get(v_alt_3733_, 5);
                lean_inc(v_cnstrs_3742_);
                lean_dec_ref(v_alt_3733_);
                v___x_3758_ = l_List_isEmpty___redArg(v_fvarDecls_3740_);
                if v___x_3758_ == 0 {
                    v___x_3759_ = lean_box(0);
                    lean_inc(v_fvarDecls_3740_);
                    v___x_3760_ =
                        l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(
                            v_fvarDecls_3740_,
                            v___x_3759_,
                        );
                    v___x_3761_ = l_Lean_MessageData_ofList(v___x_3760_);
                    v___x_3762_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Alt_toMessageData___closed__5_once
                        ),
                        _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5,
                    );
                    v___x_3763_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                    lean_ctor_set(v___x_3763_, 1, v___x_3762_);
                    v___y_3744_ = v___x_3763_;
                    state = 1;
                    continue;
                } else {
                    v___x_3764_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Alt_toMessageData___closed__7_once
                        ),
                        _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7,
                    );
                    v___y_3744_ = v___x_3764_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3745_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__1_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1,
                );
                v___x_3746_ = lean_box(0);
                v___x_3747_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(
                        v_patterns_3741_,
                        v___x_3746_,
                    );
                v___x_3748_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
                    v___x_3747_,
                    v___x_3746_,
                );
                v___x_3749_ = l_Lean_MessageData_ofList(v___x_3748_);
                v___x_3750_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3750_, 0, v___x_3745_);
                lean_ctor_set(v___x_3750_, 1, v___x_3749_);
                v___x_3751_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__3_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3,
                );
                v___x_3752_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3752_, 0, v___x_3750_);
                lean_ctor_set(v___x_3752_, 1, v___x_3751_);
                v___x_3753_ = l_Lean_MessageData_ofExpr(v_rhs_3739_);
                v___x_3754_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3754_, 0, v___x_3752_);
                lean_ctor_set(v___x_3754_, 1, v___x_3753_);
                v_msg_3755_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msg_3755_, 0, v___y_3744_);
                lean_ctor_set(v_msg_3755_, 1, v___x_3754_);
                v___f_3756_ = lean_alloc_closure(
                    l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_3756_, 0, v_cnstrs_3742_);
                lean_closure_set(v___f_3756_, 1, v_msg_3755_);
                v___x_3757_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_3740_, v___f_3756_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
                return v___x_3757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Alt_toMessageData___boxed(
    mut v_alt_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
    mut v_a_3768_: *mut LeanObject,
    mut v_a_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3771_: *mut LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Lean_Meta_Match_Alt_toMessageData(
        v_alt_3765_,
        v_a_3766_,
        v_a_3767_,
        v_a_3768_,
        v_a_3769_,
    );
    lean_dec(v_a_3769_);
    lean_dec_ref(v_a_3768_);
    lean_dec(v_a_3767_);
    lean_dec_ref(v_a_3766_);
    return v_res_3771_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(
    mut v_as_3772_: *mut LeanObject,
    mut v_as_x27_3773_: *mut LeanObject,
    mut v_b_3774_: *mut LeanObject,
    mut v_a_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    v___x_3781_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(
        v_as_x27_3773_,
        v_b_3774_,
    );
    return v___x_3781_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(
    mut v_as_3782_: *mut LeanObject,
    mut v_as_x27_3783_: *mut LeanObject,
    mut v_b_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(
        v_as_3782_,
        v_as_x27_3783_,
        v_b_3784_,
        v_a_3785_,
        v___y_3786_,
        v___y_3787_,
        v___y_3788_,
        v___y_3789_,
    );
    lean_dec(v___y_3789_);
    lean_dec_ref(v___y_3788_);
    lean_dec(v___y_3787_);
    lean_dec_ref(v___y_3786_);
    lean_dec(v_as_x27_3783_);
    lean_dec(v_as_3782_);
    return v_res_3791_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(
    mut v_s_3792_: *mut LeanObject,
    mut v_a_3793_: *mut LeanObject,
    mut v_a_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3793_) == 0 {
                    lean_dec(v_s_3792_);
                    v___x_3795_ = l_List_reverse___redArg(v_a_3794_);
                    return v___x_3795_;
                } else {
                    v_head_3796_ = lean_ctor_get(v_a_3793_, 0);
                    v_tail_3797_ = lean_ctor_get(v_a_3793_, 1);
                    v_isSharedCheck_3806_ = (!lean_is_exclusive(v_a_3793_)) as u8;
                    if v_isSharedCheck_3806_ == 0 {
                        v___x_3799_ = v_a_3793_;
                        v_isShared_3800_ = v_isSharedCheck_3806_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3797_);
                        lean_inc(v_head_3796_);
                        lean_dec(v_a_3793_);
                        v___x_3799_ = lean_box(0);
                        v_isShared_3800_ = v_isSharedCheck_3806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_s_3792_);
                v___x_3801_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_3792_, v_head_3796_);
                if v_isShared_3800_ == 0 {
                    lean_ctor_set(v___x_3799_, 1, v_a_3794_);
                    lean_ctor_set(v___x_3799_, 0, v___x_3801_);
                    v___x_3803_ = v___x_3799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3801_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_a_3794_);
                    v___x_3803_ = v_reuseFailAlloc_3805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3793_ = v_tail_3797_;
                v_a_3794_ = v___x_3803_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(
    mut v_s_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_a_3809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3815_: u8 = 0;
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3808_) == 0 {
                    lean_dec(v_s_3807_);
                    v___x_3810_ = l_List_reverse___redArg(v_a_3809_);
                    return v___x_3810_;
                } else {
                    v_head_3811_ = lean_ctor_get(v_a_3808_, 0);
                    v_tail_3812_ = lean_ctor_get(v_a_3808_, 1);
                    v_isSharedCheck_3821_ = (!lean_is_exclusive(v_a_3808_)) as u8;
                    if v_isSharedCheck_3821_ == 0 {
                        v___x_3814_ = v_a_3808_;
                        v_isShared_3815_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3812_);
                        lean_inc(v_head_3811_);
                        lean_dec(v_a_3808_);
                        v___x_3814_ = lean_box(0);
                        v_isShared_3815_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_s_3807_);
                v___x_3816_ = l_Lean_LocalDecl_applyFVarSubst(v_s_3807_, v_head_3811_);
                if v_isShared_3815_ == 0 {
                    lean_ctor_set(v___x_3814_, 1, v_a_3809_);
                    lean_ctor_set(v___x_3814_, 0, v___x_3816_);
                    v___x_3818_ = v___x_3814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3816_);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3809_);
                    v___x_3818_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3808_ = v_tail_3812_;
                v_a_3809_ = v___x_3818_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(
    mut v_s_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_fst_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3823_) == 0 {
                    lean_dec(v_s_3822_);
                    v___x_3825_ = l_List_reverse___redArg(v_a_3824_);
                    return v___x_3825_;
                } else {
                    v_head_3826_ = lean_ctor_get(v_a_3823_, 0);
                    v_tail_3827_ = lean_ctor_get(v_a_3823_, 1);
                    v_isSharedCheck_3846_ = (!lean_is_exclusive(v_a_3823_)) as u8;
                    if v_isSharedCheck_3846_ == 0 {
                        v___x_3829_ = v_a_3823_;
                        v_isShared_3830_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3827_);
                        lean_inc(v_head_3826_);
                        lean_dec(v_a_3823_);
                        v___x_3829_ = lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3846_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3831_ = lean_ctor_get(v_head_3826_, 0);
                v_snd_3832_ = lean_ctor_get(v_head_3826_, 1);
                v_isSharedCheck_3845_ = (!lean_is_exclusive(v_head_3826_)) as u8;
                if v_isSharedCheck_3845_ == 0 {
                    v___x_3834_ = v_head_3826_;
                    v_isShared_3835_ = v_isSharedCheck_3845_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3832_);
                    lean_inc(v_fst_3831_);
                    lean_dec(v_head_3826_);
                    v___x_3834_ = lean_box(0);
                    v_isShared_3835_ = v_isSharedCheck_3845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_s_3822_, 2);
                v___x_3836_ = l_Lean_Meta_FVarSubst_apply(v_s_3822_, v_fst_3831_);
                lean_dec(v_fst_3831_);
                v___x_3837_ = l_Lean_Meta_FVarSubst_apply(v_s_3822_, v_snd_3832_);
                lean_dec(v_snd_3832_);
                if v_isShared_3835_ == 0 {
                    lean_ctor_set(v___x_3834_, 1, v___x_3837_);
                    lean_ctor_set(v___x_3834_, 0, v___x_3836_);
                    v___x_3839_ = v___x_3834_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3836_);
                    lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3837_);
                    v___x_3839_ = v_reuseFailAlloc_3844_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3830_ == 0 {
                    lean_ctor_set(v___x_3829_, 1, v_a_3824_);
                    lean_ctor_set(v___x_3829_, 0, v___x_3839_);
                    v___x_3841_ = v___x_3829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3839_);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_a_3824_);
                    v___x_3841_ = v_reuseFailAlloc_3843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3823_ = v_tail_3827_;
                v_a_3824_ = v___x_3841_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Alt_applyFVarSubst(
    mut v_s_3847_: *mut LeanObject,
    mut v_alt_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_notAltIdxs_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3849_ = lean_ctor_get(v_alt_3848_, 0);
                v_idx_3850_ = lean_ctor_get(v_alt_3848_, 1);
                v_rhs_3851_ = lean_ctor_get(v_alt_3848_, 2);
                v_fvarDecls_3852_ = lean_ctor_get(v_alt_3848_, 3);
                v_patterns_3853_ = lean_ctor_get(v_alt_3848_, 4);
                v_cnstrs_3854_ = lean_ctor_get(v_alt_3848_, 5);
                v_notAltIdxs_3855_ = lean_ctor_get(v_alt_3848_, 6);
                v_isSharedCheck_3867_ = (!lean_is_exclusive(v_alt_3848_)) as u8;
                if v_isSharedCheck_3867_ == 0 {
                    v___x_3857_ = v_alt_3848_;
                    v_isShared_3858_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_notAltIdxs_3855_);
                    lean_inc(v_cnstrs_3854_);
                    lean_inc(v_patterns_3853_);
                    lean_inc(v_fvarDecls_3852_);
                    lean_inc(v_rhs_3851_);
                    lean_inc(v_idx_3850_);
                    lean_inc(v_ref_3849_);
                    lean_dec(v_alt_3848_);
                    v___x_3857_ = lean_box(0);
                    v_isShared_3858_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_s_3847_, 3);
                v___x_3859_ = l_Lean_Meta_FVarSubst_apply(v_s_3847_, v_rhs_3851_);
                lean_dec_ref(v_rhs_3851_);
                v___x_3860_ = lean_box(0);
                v___x_3861_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(
                    v_s_3847_,
                    v_fvarDecls_3852_,
                    v___x_3860_,
                );
                v___x_3862_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(
                    v_s_3847_,
                    v_patterns_3853_,
                    v___x_3860_,
                );
                v___x_3863_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(
                    v_s_3847_,
                    v_cnstrs_3854_,
                    v___x_3860_,
                );
                if v_isShared_3858_ == 0 {
                    lean_ctor_set(v___x_3857_, 5, v___x_3863_);
                    lean_ctor_set(v___x_3857_, 4, v___x_3862_);
                    lean_ctor_set(v___x_3857_, 3, v___x_3861_);
                    lean_ctor_set(v___x_3857_, 2, v___x_3859_);
                    v___x_3865_ = v___x_3857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_ref_3849_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_idx_3850_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 2, v___x_3859_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 3, v___x_3861_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 4, v___x_3862_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 5, v___x_3863_);
                    lean_ctor_set(v_reuseFailAlloc_3866_, 6, v_notAltIdxs_3855_);
                    v___x_3865_ = v_reuseFailAlloc_3866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(
    mut v_fvarId_3868_: *mut LeanObject,
    mut v_v_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3877_: u8 = 0;
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3870_) == 0 {
                    lean_dec_ref(v_v_3869_);
                    lean_dec(v_fvarId_3868_);
                    v___x_3872_ = l_List_reverse___redArg(v_a_3871_);
                    return v___x_3872_;
                } else {
                    v_head_3873_ = lean_ctor_get(v_a_3870_, 0);
                    v_tail_3874_ = lean_ctor_get(v_a_3870_, 1);
                    v_isSharedCheck_3883_ = (!lean_is_exclusive(v_a_3870_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3876_ = v_a_3870_;
                        v_isShared_3877_ = v_isSharedCheck_3883_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3874_);
                        lean_inc(v_head_3873_);
                        lean_dec(v_a_3870_);
                        v___x_3876_ = lean_box(0);
                        v_isShared_3877_ = v_isSharedCheck_3883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_v_3869_);
                lean_inc(v_fvarId_3868_);
                v___x_3878_ = l_Lean_Meta_Match_Pattern_replaceFVarId(
                    v_fvarId_3868_,
                    v_v_3869_,
                    v_head_3873_,
                );
                if v_isShared_3877_ == 0 {
                    lean_ctor_set(v___x_3876_, 1, v_a_3871_);
                    lean_ctor_set(v___x_3876_, 0, v___x_3878_);
                    v___x_3880_ = v___x_3876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3878_);
                    lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_a_3871_);
                    v___x_3880_ = v_reuseFailAlloc_3882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3870_ = v_tail_3874_;
                v_a_3871_ = v___x_3880_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
    mut v_fvarId_3884_: *mut LeanObject,
    mut v_v_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
    mut v_a_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3886_) == 0 {
                    lean_dec(v_fvarId_3884_);
                    v___x_3888_ = l_List_reverse___redArg(v_a_3887_);
                    return v___x_3888_;
                } else {
                    v_head_3889_ = lean_ctor_get(v_a_3886_, 0);
                    v_tail_3890_ = lean_ctor_get(v_a_3886_, 1);
                    v_isSharedCheck_3899_ = (!lean_is_exclusive(v_a_3886_)) as u8;
                    if v_isSharedCheck_3899_ == 0 {
                        v___x_3892_ = v_a_3886_;
                        v_isShared_3893_ = v_isSharedCheck_3899_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3890_);
                        lean_inc(v_head_3889_);
                        lean_dec(v_a_3886_);
                        v___x_3892_ = lean_box(0);
                        v_isShared_3893_ = v_isSharedCheck_3899_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_fvarId_3884_);
                v___x_3894_ =
                    l_Lean_LocalDecl_replaceFVarId(v_fvarId_3884_, v_v_3885_, v_head_3889_);
                if v_isShared_3893_ == 0 {
                    lean_ctor_set(v___x_3892_, 1, v_a_3887_);
                    lean_ctor_set(v___x_3892_, 0, v___x_3894_);
                    v___x_3896_ = v___x_3892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3894_);
                    lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_a_3887_);
                    v___x_3896_ = v_reuseFailAlloc_3898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3886_ = v_tail_3890_;
                v_a_3887_ = v___x_3896_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(
    mut v_fvarId_3900_: *mut LeanObject,
    mut v_v_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
        v_fvarId_3900_,
        v_v_3901_,
        v_a_3902_,
        v_a_3903_,
    );
    lean_dec_ref(v_v_3901_);
    return v_res_3904_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
    mut v_fvarId_3905_: *mut LeanObject,
    mut v_v_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v_fst_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3907_) == 0 {
                    lean_dec(v_fvarId_3905_);
                    v___x_3909_ = l_List_reverse___redArg(v_a_3908_);
                    return v___x_3909_;
                } else {
                    v_head_3910_ = lean_ctor_get(v_a_3907_, 0);
                    v_tail_3911_ = lean_ctor_get(v_a_3907_, 1);
                    v_isSharedCheck_3930_ = (!lean_is_exclusive(v_a_3907_)) as u8;
                    if v_isSharedCheck_3930_ == 0 {
                        v___x_3913_ = v_a_3907_;
                        v_isShared_3914_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3911_);
                        lean_inc(v_head_3910_);
                        lean_dec(v_a_3907_);
                        v___x_3913_ = lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3915_ = lean_ctor_get(v_head_3910_, 0);
                v_snd_3916_ = lean_ctor_get(v_head_3910_, 1);
                v_isSharedCheck_3929_ = (!lean_is_exclusive(v_head_3910_)) as u8;
                if v_isSharedCheck_3929_ == 0 {
                    v___x_3918_ = v_head_3910_;
                    v_isShared_3919_ = v_isSharedCheck_3929_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3916_);
                    lean_inc(v_fst_3915_);
                    lean_dec(v_head_3910_);
                    v___x_3918_ = lean_box(0);
                    v_isShared_3919_ = v_isSharedCheck_3929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_fvarId_3905_, 2);
                v___x_3920_ = l_Lean_Expr_replaceFVarId(v_fst_3915_, v_fvarId_3905_, v_v_3906_);
                lean_dec(v_fst_3915_);
                v___x_3921_ = l_Lean_Expr_replaceFVarId(v_snd_3916_, v_fvarId_3905_, v_v_3906_);
                lean_dec(v_snd_3916_);
                if v_isShared_3919_ == 0 {
                    lean_ctor_set(v___x_3918_, 1, v___x_3921_);
                    lean_ctor_set(v___x_3918_, 0, v___x_3920_);
                    v___x_3923_ = v___x_3918_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3920_);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3921_);
                    v___x_3923_ = v_reuseFailAlloc_3928_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3914_ == 0 {
                    lean_ctor_set(v___x_3913_, 1, v_a_3908_);
                    lean_ctor_set(v___x_3913_, 0, v___x_3923_);
                    v___x_3925_ = v___x_3913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3923_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_a_3908_);
                    v___x_3925_ = v_reuseFailAlloc_3927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3907_ = v_tail_3911_;
                v_a_3908_ = v___x_3925_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(
    mut v_fvarId_3931_: *mut LeanObject,
    mut v_v_3932_: *mut LeanObject,
    mut v_a_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3935_: *mut LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
        v_fvarId_3931_,
        v_v_3932_,
        v_a_3933_,
        v_a_3934_,
    );
    lean_dec_ref(v_v_3932_);
    return v_res_3935_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
    mut v_fvarId_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3937_) == 0 {
                    v___x_3939_ = l_List_reverse___redArg(v_a_3938_);
                    return v___x_3939_;
                } else {
                    v_head_3940_ = lean_ctor_get(v_a_3937_, 0);
                    v_tail_3941_ = lean_ctor_get(v_a_3937_, 1);
                    v_isSharedCheck_3952_ = (!lean_is_exclusive(v_a_3937_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3943_ = v_a_3937_;
                        v_isShared_3944_ = v_isSharedCheck_3952_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3941_);
                        lean_inc(v_head_3940_);
                        lean_dec(v_a_3937_);
                        v___x_3943_ = lean_box(0);
                        v_isShared_3944_ = v_isSharedCheck_3952_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3945_ = l_Lean_LocalDecl_fvarId(v_head_3940_);
                v___x_3946_ = l_Lean_instBEqFVarId_beq(v___x_3945_, v_fvarId_3936_);
                lean_dec(v___x_3945_);
                if v___x_3946_ == 0 {
                    if v_isShared_3944_ == 0 {
                        lean_ctor_set(v___x_3943_, 1, v_a_3938_);
                        v___x_3948_ = v___x_3943_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_head_3940_);
                        lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_a_3938_);
                        v___x_3948_ = v_reuseFailAlloc_3950_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3943_);
                    lean_dec(v_head_3940_);
                    v_a_3937_ = v_tail_3941_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_3937_ = v_tail_3941_;
                v_a_3938_ = v___x_3948_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(
    mut v_fvarId_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
        v_fvarId_3953_,
        v_a_3954_,
        v_a_3955_,
    );
    lean_dec(v_fvarId_3953_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_replaceFVarId(
    mut v_fvarId_3957_: *mut LeanObject,
    mut v_v_3958_: *mut LeanObject,
    mut v_alt_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecls_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patterns_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cnstrs_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_notAltIdxs_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3960_ = lean_ctor_get(v_alt_3959_, 0);
                v_idx_3961_ = lean_ctor_get(v_alt_3959_, 1);
                v_rhs_3962_ = lean_ctor_get(v_alt_3959_, 2);
                v_fvarDecls_3963_ = lean_ctor_get(v_alt_3959_, 3);
                v_patterns_3964_ = lean_ctor_get(v_alt_3959_, 4);
                v_cnstrs_3965_ = lean_ctor_get(v_alt_3959_, 5);
                v_notAltIdxs_3966_ = lean_ctor_get(v_alt_3959_, 6);
                v_isSharedCheck_3979_ = (!lean_is_exclusive(v_alt_3959_)) as u8;
                if v_isSharedCheck_3979_ == 0 {
                    v___x_3968_ = v_alt_3959_;
                    v_isShared_3969_ = v_isSharedCheck_3979_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_notAltIdxs_3966_);
                    lean_inc(v_cnstrs_3965_);
                    lean_inc(v_patterns_3964_);
                    lean_inc(v_fvarDecls_3963_);
                    lean_inc(v_rhs_3962_);
                    lean_inc(v_idx_3961_);
                    lean_inc(v_ref_3960_);
                    lean_dec(v_alt_3959_);
                    v___x_3968_ = lean_box(0);
                    v_isShared_3969_ = v_isSharedCheck_3979_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_fvarId_3957_, 3);
                v___x_3970_ = l_Lean_Expr_replaceFVarId(v_rhs_3962_, v_fvarId_3957_, v_v_3958_);
                lean_dec_ref(v_rhs_3962_);
                v___x_3971_ = lean_box(0);
                v_decls_3972_ =
                    l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(
                        v_fvarId_3957_,
                        v_fvarDecls_3963_,
                        v___x_3971_,
                    );
                v___x_3973_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_decls_3972_,
                    v___x_3971_,
                );
                lean_inc_ref(v_v_3958_);
                v___x_3974_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_patterns_3964_,
                    v___x_3971_,
                );
                v___x_3975_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(
                    v_fvarId_3957_,
                    v_v_3958_,
                    v_cnstrs_3965_,
                    v___x_3971_,
                );
                lean_dec_ref(v_v_3958_);
                if v_isShared_3969_ == 0 {
                    lean_ctor_set(v___x_3968_, 5, v___x_3975_);
                    lean_ctor_set(v___x_3968_, 4, v___x_3974_);
                    lean_ctor_set(v___x_3968_, 3, v___x_3973_);
                    lean_ctor_set(v___x_3968_, 2, v___x_3970_);
                    v___x_3977_ = v___x_3968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_ref_3960_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_idx_3961_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 2, v___x_3970_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 3, v___x_3973_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 4, v___x_3974_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 5, v___x_3975_);
                    lean_ctor_set(v_reuseFailAlloc_3978_, 6, v_notAltIdxs_3966_);
                    v___x_3977_ = v_reuseFailAlloc_3978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(
    mut v_fvarId_3980_: *mut LeanObject,
    mut v_x_3981_: *mut LeanObject,
) -> u8 {
    let mut v___x_3982_: u8 = 0;
    let mut v_head_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3981_) == 0 {
                    v___x_3982_ = 0;
                    return v___x_3982_;
                } else {
                    v_head_3983_ = lean_ctor_get(v_x_3981_, 0);
                    v_tail_3984_ = lean_ctor_get(v_x_3981_, 1);
                    v___x_3985_ = l_Lean_LocalDecl_fvarId(v_head_3983_);
                    v___x_3986_ = l_Lean_instBEqFVarId_beq(v___x_3985_, v_fvarId_3980_);
                    lean_dec(v___x_3985_);
                    if v___x_3986_ == 0 {
                        v_x_3981_ = v_tail_3984_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3986_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(
    mut v_fvarId_3988_: *mut LeanObject,
    mut v_x_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3990_: u8 = 0;
    let mut v_r_3991_: *mut LeanObject = core::ptr::null_mut();
    v_res_3990_ =
        l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_3988_, v_x_3989_);
    lean_dec(v_x_3989_);
    lean_dec(v_fvarId_3988_);
    v_r_3991_ = lean_box((v_res_3990_) as usize);
    return v_r_3991_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_isLocalDecl(
    mut v_fvarId_3992_: *mut LeanObject,
    mut v_alt_3993_: *mut LeanObject,
) -> u8 {
    let mut v_fvarDecls_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    v_fvarDecls_3994_ = lean_ctor_get(v_alt_3993_, 3);
    v___x_3995_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(
        v_fvarId_3992_,
        v_fvarDecls_3994_,
    );
    return v___x_3995_;
}
pub unsafe fn l_Lean_Meta_Match_Alt_isLocalDecl___boxed(
    mut v_fvarId_3996_: *mut LeanObject,
    mut v_alt_3997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3998_: u8 = 0;
    let mut v_r_3999_: *mut LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_3996_, v_alt_3997_);
    lean_dec_ref(v_alt_3997_);
    lean_dec(v_fvarId_3996_);
    v_r_3999_ = lean_box((v_res_3998_) as usize);
    return v_r_3999_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorIdx(mut v_x_4000_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4000_) {
        0 => {
            let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
            v___x_4001_ = lean_unsigned_to_nat(0);
            return v___x_4001_;
        }
        1 => {
            let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
            v___x_4002_ = lean_unsigned_to_nat(1);
            return v___x_4002_;
        }
        2 => {
            let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
            v___x_4003_ = lean_unsigned_to_nat(2);
            return v___x_4003_;
        }
        3 => {
            let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
            v___x_4004_ = lean_unsigned_to_nat(3);
            return v___x_4004_;
        }
        _ => {
            let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
            v___x_4005_ = lean_unsigned_to_nat(4);
            return v___x_4005_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorIdx___boxed(
    mut v_x_4006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4007_: *mut LeanObject = core::ptr::null_mut();
    v_res_4007_ = l_Lean_Meta_Match_Example_ctorIdx(v_x_4006_);
    lean_dec(v_x_4006_);
    return v_res_4007_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim___redArg(
    mut v_t_4008_: *mut LeanObject,
    mut v_k_4009_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4008_) {
        1 => {
            return v_k_4009_;
        }
        2 => {
            let mut v_a_4010_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_4011_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
            v_a_4010_ = lean_ctor_get(v_t_4008_, 0);
            lean_inc(v_a_4010_);
            v_a_4011_ = lean_ctor_get(v_t_4008_, 1);
            lean_inc(v_a_4011_);
            lean_dec_ref_known(v_t_4008_, 2);
            v___x_4012_ = lean_apply_2(v_k_4009_, v_a_4010_, v_a_4011_);
            return v___x_4012_;
        }
        3 => {
            let mut v_a_4013_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
            v_a_4013_ = lean_ctor_get(v_t_4008_, 0);
            lean_inc_ref(v_a_4013_);
            lean_dec_ref_known(v_t_4008_, 1);
            v___x_4014_ = lean_apply_1(v_k_4009_, v_a_4013_);
            return v___x_4014_;
        }
        _ => {
            let mut v_a_4015_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
            v_a_4015_ = lean_ctor_get(v_t_4008_, 0);
            lean_inc(v_a_4015_);
            lean_dec(v_t_4008_);
            v___x_4016_ = lean_apply_1(v_k_4009_, v_a_4015_);
            return v___x_4016_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim(
    mut v_motive__1_4017_: *mut LeanObject,
    mut v_ctorIdx_4018_: *mut LeanObject,
    mut v_t_4019_: *mut LeanObject,
    mut v_h_4020_: *mut LeanObject,
    mut v_k_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    v___x_4022_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4019_, v_k_4021_);
    return v___x_4022_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctorElim___boxed(
    mut v_motive__1_4023_: *mut LeanObject,
    mut v_ctorIdx_4024_: *mut LeanObject,
    mut v_t_4025_: *mut LeanObject,
    mut v_h_4026_: *mut LeanObject,
    mut v_k_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4028_: *mut LeanObject = core::ptr::null_mut();
    v_res_4028_ = l_Lean_Meta_Match_Example_ctorElim(
        v_motive__1_4023_,
        v_ctorIdx_4024_,
        v_t_4025_,
        v_h_4026_,
        v_k_4027_,
    );
    lean_dec(v_ctorIdx_4024_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_Meta_Match_Example_var_elim___redArg(
    mut v_t_4029_: *mut LeanObject,
    mut v_var_4030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    v___x_4031_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4029_, v_var_4030_);
    return v___x_4031_;
}
pub unsafe fn l_Lean_Meta_Match_Example_var_elim(
    mut v_motive__1_4032_: *mut LeanObject,
    mut v_t_4033_: *mut LeanObject,
    mut v_h_4034_: *mut LeanObject,
    mut v_var_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    v___x_4036_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4033_, v_var_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_Meta_Match_Example_underscore_elim___redArg(
    mut v_t_4037_: *mut LeanObject,
    mut v_underscore_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    v___x_4039_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4037_, v_underscore_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_Meta_Match_Example_underscore_elim(
    mut v_motive__1_4040_: *mut LeanObject,
    mut v_t_4041_: *mut LeanObject,
    mut v_h_4042_: *mut LeanObject,
    mut v_underscore_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___x_4044_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4041_, v_underscore_4043_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctor_elim___redArg(
    mut v_t_4045_: *mut LeanObject,
    mut v_ctor_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4045_, v_ctor_4046_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_Meta_Match_Example_ctor_elim(
    mut v_motive__1_4048_: *mut LeanObject,
    mut v_t_4049_: *mut LeanObject,
    mut v_h_4050_: *mut LeanObject,
    mut v_ctor_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    v___x_4052_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4049_, v_ctor_4051_);
    return v___x_4052_;
}
pub unsafe fn l_Lean_Meta_Match_Example_val_elim___redArg(
    mut v_t_4053_: *mut LeanObject,
    mut v_val_4054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4053_, v_val_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_Meta_Match_Example_val_elim(
    mut v_motive__1_4056_: *mut LeanObject,
    mut v_t_4057_: *mut LeanObject,
    mut v_h_4058_: *mut LeanObject,
    mut v_val_4059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4057_, v_val_4059_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_Meta_Match_Example_arrayLit_elim___redArg(
    mut v_t_4061_: *mut LeanObject,
    mut v_arrayLit_4062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4061_, v_arrayLit_4062_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_Meta_Match_Example_arrayLit_elim(
    mut v_motive__1_4064_: *mut LeanObject,
    mut v_t_4065_: *mut LeanObject,
    mut v_h_4066_: *mut LeanObject,
    mut v_arrayLit_4067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    v___x_4068_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_4065_, v_arrayLit_4067_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_Meta_Match_Example_replaceFVarId(
    mut v_fvarId_4069_: *mut LeanObject,
    mut v_ex_4070_: *mut LeanObject,
    mut v_x_4071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v_a_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4071_) {
                0 => {
                    v_a_4072_ = lean_ctor_get(v_x_4071_, 0);
                    v___x_4073_ = l_Lean_instBEqFVarId_beq(v_a_4072_, v_fvarId_4069_);
                    if v___x_4073_ == 0 {
                        return v_x_4071_;
                    } else {
                        lean_dec_ref_known(v_x_4071_, 1);
                        lean_inc(v_ex_4070_);
                        return v_ex_4070_;
                    }
                }
                2 => {
                    v_a_4074_ = lean_ctor_get(v_x_4071_, 0);
                    v_a_4075_ = lean_ctor_get(v_x_4071_, 1);
                    v_isSharedCheck_4084_ = (!lean_is_exclusive(v_x_4071_)) as u8;
                    if v_isSharedCheck_4084_ == 0 {
                        v___x_4077_ = v_x_4071_;
                        v_isShared_4078_ = v_isSharedCheck_4084_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4075_);
                        lean_inc(v_a_4074_);
                        lean_dec(v_x_4071_);
                        v___x_4077_ = lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4084_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_a_4085_ = lean_ctor_get(v_x_4071_, 0);
                    v_isSharedCheck_4094_ = (!lean_is_exclusive(v_x_4071_)) as u8;
                    if v_isSharedCheck_4094_ == 0 {
                        v___x_4087_ = v_x_4071_;
                        v_isShared_4088_ = v_isSharedCheck_4094_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4085_);
                        lean_dec(v_x_4071_);
                        v___x_4087_ = lean_box(0);
                        v_isShared_4088_ = v_isSharedCheck_4094_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    return v_x_4071_;
                }
            },
            1 => {
                v___x_4079_ = lean_box(0);
                v___x_4080_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
                        v_fvarId_4069_,
                        v_ex_4070_,
                        v_a_4075_,
                        v___x_4079_,
                    );
                if v_isShared_4078_ == 0 {
                    lean_ctor_set(v___x_4077_, 1, v___x_4080_);
                    v___x_4082_ = v___x_4077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4074_);
                    lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4080_);
                    v___x_4082_ = v_reuseFailAlloc_4083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4082_;
            }
            3 => {
                v___x_4089_ = lean_box(0);
                v___x_4090_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
                        v_fvarId_4069_,
                        v_ex_4070_,
                        v_a_4085_,
                        v___x_4089_,
                    );
                if v_isShared_4088_ == 0 {
                    lean_ctor_set(v___x_4087_, 0, v___x_4090_);
                    v___x_4092_ = v___x_4087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
                    v___x_4092_ = v_reuseFailAlloc_4093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
    mut v_fvarId_4095_: *mut LeanObject,
    mut v_ex_4096_: *mut LeanObject,
    mut v_a_4097_: *mut LeanObject,
    mut v_a_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4097_) == 0 {
                    v___x_4099_ = l_List_reverse___redArg(v_a_4098_);
                    return v___x_4099_;
                } else {
                    v_head_4100_ = lean_ctor_get(v_a_4097_, 0);
                    v_tail_4101_ = lean_ctor_get(v_a_4097_, 1);
                    v_isSharedCheck_4110_ = (!lean_is_exclusive(v_a_4097_)) as u8;
                    if v_isSharedCheck_4110_ == 0 {
                        v___x_4103_ = v_a_4097_;
                        v_isShared_4104_ = v_isSharedCheck_4110_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4101_);
                        lean_inc(v_head_4100_);
                        lean_dec(v_a_4097_);
                        v___x_4103_ = lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4110_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4105_ = l_Lean_Meta_Match_Example_replaceFVarId(
                    v_fvarId_4095_,
                    v_ex_4096_,
                    v_head_4100_,
                );
                if v_isShared_4104_ == 0 {
                    lean_ctor_set(v___x_4103_, 1, v_a_4098_);
                    lean_ctor_set(v___x_4103_, 0, v___x_4105_);
                    v___x_4107_ = v___x_4103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4105_);
                    lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_a_4098_);
                    v___x_4107_ = v_reuseFailAlloc_4109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4097_ = v_tail_4101_;
                v_a_4098_ = v___x_4107_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(
    mut v_fvarId_4111_: *mut LeanObject,
    mut v_ex_4112_: *mut LeanObject,
    mut v_a_4113_: *mut LeanObject,
    mut v_a_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4115_: *mut LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(
        v_fvarId_4111_,
        v_ex_4112_,
        v_a_4113_,
        v_a_4114_,
    );
    lean_dec(v_ex_4112_);
    lean_dec(v_fvarId_4111_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_Meta_Match_Example_replaceFVarId___boxed(
    mut v_fvarId_4116_: *mut LeanObject,
    mut v_ex_4117_: *mut LeanObject,
    mut v_x_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_4116_, v_ex_4117_, v_x_4118_);
    lean_dec(v_ex_4117_);
    lean_dec(v_fvarId_4116_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_Meta_Match_Example_applyFVarSubst(
    mut v_s_4120_: *mut LeanObject,
    mut v_x_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut v_a_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4121_) {
                0 => {
                    v_a_4122_ = lean_ctor_get(v_x_4121_, 0);
                    v_isSharedCheck_4132_ = (!lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4132_ == 0 {
                        v___x_4124_ = v_x_4121_;
                        v_isShared_4125_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4122_);
                        lean_dec(v_x_4121_);
                        v___x_4124_ = lean_box(0);
                        v_isShared_4125_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_a_4133_ = lean_ctor_get(v_x_4121_, 0);
                    v_a_4134_ = lean_ctor_get(v_x_4121_, 1);
                    v_isSharedCheck_4143_ = (!lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4143_ == 0 {
                        v___x_4136_ = v_x_4121_;
                        v_isShared_4137_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4134_);
                        lean_inc(v_a_4133_);
                        lean_dec(v_x_4121_);
                        v___x_4136_ = lean_box(0);
                        v_isShared_4137_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    }
                }
                4 => {
                    v_a_4144_ = lean_ctor_get(v_x_4121_, 0);
                    v_isSharedCheck_4153_ = (!lean_is_exclusive(v_x_4121_)) as u8;
                    if v_isSharedCheck_4153_ == 0 {
                        v___x_4146_ = v_x_4121_;
                        v_isShared_4147_ = v_isSharedCheck_4153_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4144_);
                        lean_dec(v_x_4121_);
                        v___x_4146_ = lean_box(0);
                        v_isShared_4147_ = v_isSharedCheck_4153_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    return v_x_4121_;
                }
            },
            1 => {
                v___x_4126_ = l_Lean_Meta_FVarSubst_get(v_s_4120_, v_a_4122_);
                if lean_obj_tag(v___x_4126_) == 1 {
                    v_fvarId_4127_ = lean_ctor_get(v___x_4126_, 0);
                    lean_inc(v_fvarId_4127_);
                    lean_dec_ref_known(v___x_4126_, 1);
                    if v_isShared_4125_ == 0 {
                        lean_ctor_set(v___x_4124_, 0, v_fvarId_4127_);
                        v___x_4129_ = v___x_4124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_fvarId_4127_);
                        v___x_4129_ = v_reuseFailAlloc_4130_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4126_);
                    lean_del_object(v___x_4124_);
                    v___x_4131_ = lean_box(1);
                    return v___x_4131_;
                }
            }
            2 => {
                return v___x_4129_;
            }
            3 => {
                v___x_4138_ = lean_box(0);
                v___x_4139_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
                        v_s_4120_,
                        v_a_4134_,
                        v___x_4138_,
                    );
                if v_isShared_4137_ == 0 {
                    lean_ctor_set(v___x_4136_, 1, v___x_4139_);
                    v___x_4141_ = v___x_4136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4133_);
                    lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4139_);
                    v___x_4141_ = v_reuseFailAlloc_4142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4141_;
            }
            5 => {
                v___x_4148_ = lean_box(0);
                v___x_4149_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
                        v_s_4120_,
                        v_a_4144_,
                        v___x_4148_,
                    );
                if v_isShared_4147_ == 0 {
                    lean_ctor_set(v___x_4146_, 0, v___x_4149_);
                    v___x_4151_ = v___x_4146_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
    mut v_s_4154_: *mut LeanObject,
    mut v_a_4155_: *mut LeanObject,
    mut v_a_4156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4155_) == 0 {
                    v___x_4157_ = l_List_reverse___redArg(v_a_4156_);
                    return v___x_4157_;
                } else {
                    v_head_4158_ = lean_ctor_get(v_a_4155_, 0);
                    v_tail_4159_ = lean_ctor_get(v_a_4155_, 1);
                    v_isSharedCheck_4168_ = (!lean_is_exclusive(v_a_4155_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4161_ = v_a_4155_;
                        v_isShared_4162_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4159_);
                        lean_inc(v_head_4158_);
                        lean_dec(v_a_4155_);
                        v___x_4161_ = lean_box(0);
                        v_isShared_4162_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4163_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_4154_, v_head_4158_);
                if v_isShared_4162_ == 0 {
                    lean_ctor_set(v___x_4161_, 1, v_a_4156_);
                    lean_ctor_set(v___x_4161_, 0, v___x_4163_);
                    v___x_4165_ = v___x_4161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4163_);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_a_4156_);
                    v___x_4165_ = v_reuseFailAlloc_4167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4155_ = v_tail_4159_;
                v_a_4156_ = v___x_4165_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(
    mut v_s_4169_: *mut LeanObject,
    mut v_a_4170_: *mut LeanObject,
    mut v_a_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4172_: *mut LeanObject = core::ptr::null_mut();
    v_res_4172_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(
        v_s_4169_, v_a_4170_, v_a_4171_,
    );
    lean_dec(v_s_4169_);
    return v_res_4172_;
}
pub unsafe fn l_Lean_Meta_Match_Example_applyFVarSubst___boxed(
    mut v_s_4173_: *mut LeanObject,
    mut v_x_4174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4175_: *mut LeanObject = core::ptr::null_mut();
    v_res_4175_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_4173_, v_x_4174_);
    lean_dec(v_s_4173_);
    return v_res_4175_;
}
pub unsafe fn l_Lean_Meta_Match_Example_varsToUnderscore(
    mut v_x_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v_a_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4176_) {
                0 => {
                    lean_dec_ref_known(v_x_4176_, 1);
                    v___x_4177_ = lean_box(1);
                    return v___x_4177_;
                }
                2 => {
                    v_a_4178_ = lean_ctor_get(v_x_4176_, 0);
                    v_a_4179_ = lean_ctor_get(v_x_4176_, 1);
                    v_isSharedCheck_4188_ = (!lean_is_exclusive(v_x_4176_)) as u8;
                    if v_isSharedCheck_4188_ == 0 {
                        v___x_4181_ = v_x_4176_;
                        v_isShared_4182_ = v_isSharedCheck_4188_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4179_);
                        lean_inc(v_a_4178_);
                        lean_dec(v_x_4176_);
                        v___x_4181_ = lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4188_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_a_4189_ = lean_ctor_get(v_x_4176_, 0);
                    v_isSharedCheck_4198_ = (!lean_is_exclusive(v_x_4176_)) as u8;
                    if v_isSharedCheck_4198_ == 0 {
                        v___x_4191_ = v_x_4176_;
                        v_isShared_4192_ = v_isSharedCheck_4198_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4189_);
                        lean_dec(v_x_4176_);
                        v___x_4191_ = lean_box(0);
                        v_isShared_4192_ = v_isSharedCheck_4198_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    return v_x_4176_;
                }
            },
            1 => {
                v___x_4183_ = lean_box(0);
                v___x_4184_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
                        v_a_4179_,
                        v___x_4183_,
                    );
                if v_isShared_4182_ == 0 {
                    lean_ctor_set(v___x_4181_, 1, v___x_4184_);
                    v___x_4186_ = v___x_4181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4178_);
                    lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4184_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4186_;
            }
            3 => {
                v___x_4193_ = lean_box(0);
                v___x_4194_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
                        v_a_4189_,
                        v___x_4193_,
                    );
                if v_isShared_4192_ == 0 {
                    lean_ctor_set(v___x_4191_, 0, v___x_4194_);
                    v___x_4196_ = v___x_4191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4197_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
                    v___x_4196_ = v_reuseFailAlloc_4197_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(
    mut v_a_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4199_) == 0 {
                    v___x_4201_ = l_List_reverse___redArg(v_a_4200_);
                    return v___x_4201_;
                } else {
                    v_head_4202_ = lean_ctor_get(v_a_4199_, 0);
                    v_tail_4203_ = lean_ctor_get(v_a_4199_, 1);
                    v_isSharedCheck_4212_ = (!lean_is_exclusive(v_a_4199_)) as u8;
                    if v_isSharedCheck_4212_ == 0 {
                        v___x_4205_ = v_a_4199_;
                        v_isShared_4206_ = v_isSharedCheck_4212_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4203_);
                        lean_inc(v_head_4202_);
                        lean_dec(v_a_4199_);
                        v___x_4205_ = lean_box(0);
                        v_isShared_4206_ = v_isSharedCheck_4212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4207_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_4202_);
                if v_isShared_4206_ == 0 {
                    lean_ctor_set(v___x_4205_, 1, v_a_4200_);
                    lean_ctor_set(v___x_4205_, 0, v___x_4207_);
                    v___x_4209_ = v___x_4205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4207_);
                    lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_a_4200_);
                    v___x_4209_ = v_reuseFailAlloc_4211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4199_ = v_tail_4203_;
                v_a_4200_ = v___x_4209_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Example_toMessageData___closed__2() -> *mut LeanObject {
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Lean_Meta_Match_Example_toMessageData___closed__1;
    v___x_4217_ = l_Lean_MessageData_ofFormat(v___x_4216_);
    return v___x_4217_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0;
    v___x_4219_ = l_Lean_stringToMessageData(v___x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(
    mut v_x_4220_: *mut LeanObject,
    mut v_x_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4226_: u8 = 0;
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4221_) == 0 {
                    return v_x_4220_;
                } else {
                    v_head_4222_ = lean_ctor_get(v_x_4221_, 0);
                    v_tail_4223_ = lean_ctor_get(v_x_4221_, 1);
                    v_isSharedCheck_4234_ = (!lean_is_exclusive(v_x_4221_)) as u8;
                    if v_isSharedCheck_4234_ == 0 {
                        v___x_4225_ = v_x_4221_;
                        v_isShared_4226_ = v_isSharedCheck_4234_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4223_);
                        lean_inc(v_head_4222_);
                        lean_dec(v_x_4221_);
                        v___x_4225_ = lean_box(0);
                        v_isShared_4226_ = v_isSharedCheck_4234_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4227_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once), _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
                if v_isShared_4226_ == 0 {
                    lean_ctor_set_tag(v___x_4225_, 7);
                    lean_ctor_set(v___x_4225_, 1, v___x_4227_);
                    lean_ctor_set(v___x_4225_, 0, v_x_4220_);
                    v___x_4229_ = v___x_4225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_x_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4233_, 1, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4230_ = l_Lean_Meta_Match_Example_toMessageData(v_head_4222_);
                v___x_4231_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4231_, 0, v___x_4229_);
                lean_ctor_set(v___x_4231_, 1, v___x_4230_);
                v_x_4220_ = v___x_4231_;
                v_x_4221_ = v_tail_4223_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_Example_toMessageData___closed__5() -> *mut LeanObject {
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Meta_Match_Example_toMessageData___closed__4;
    v___x_4239_ = l_Lean_MessageData_ofFormat(v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Lean_Meta_Match_Example_toMessageData(
    mut v_x_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_unused_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_4240_) {
                    0 => {
                        v_a_4241_ = lean_ctor_get(v_x_4240_, 0);
                        lean_inc(v_a_4241_);
                        lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4242_ = l_Lean_mkFVar(v_a_4241_);
                        v___x_4243_ = l_Lean_MessageData_ofExpr(v___x_4242_);
                        return v___x_4243_;
                    }
                    1 => {
                        v___x_4244_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__2_once
                            ),
                            _init_l_Lean_Meta_Match_Example_toMessageData___closed__2,
                        );
                        return v___x_4244_;
                    }
                    2 => {
                        v_a_4245_ = lean_ctor_get(v_x_4240_, 1);
                        if lean_obj_tag(v_a_4245_) == 0 {
                            v_a_4246_ = lean_ctor_get(v_x_4240_, 0);
                            lean_inc(v_a_4246_);
                            lean_dec_ref_known(v_x_4240_, 2);
                            v___x_4247_ = lean_box(0);
                            v___x_4248_ = l_Lean_mkConst(v_a_4246_, v___x_4247_);
                            v___x_4249_ = l_Lean_MessageData_ofExpr(v___x_4248_);
                            return v___x_4249_;
                        } else {
                            lean_inc(v_a_4245_);
                            v_a_4250_ = lean_ctor_get(v_x_4240_, 0);
                            v_isSharedCheck_4265_ = (!lean_is_exclusive(v_x_4240_)) as u8;
                            if v_isSharedCheck_4265_ == 0 {
                                v_unused_4266_ = lean_ctor_get(v_x_4240_, 1);
                                lean_dec(v_unused_4266_);
                                v___x_4252_ = v_x_4240_;
                                v_isShared_4253_ = v_isSharedCheck_4265_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4250_);
                                lean_dec(v_x_4240_);
                                v___x_4252_ = lean_box(0);
                                v_isShared_4253_ = v_isSharedCheck_4265_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    3 => {
                        v_a_4267_ = lean_ctor_get(v_x_4240_, 0);
                        lean_inc_ref(v_a_4267_);
                        lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4268_ = l_Lean_MessageData_ofExpr(v_a_4267_);
                        return v___x_4268_;
                    }
                    _ => {
                        v_a_4269_ = lean_ctor_get(v_x_4240_, 0);
                        lean_inc(v_a_4269_);
                        lean_dec_ref_known(v_x_4240_, 1);
                        v___x_4270_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Match_Example_toMessageData___closed__5_once
                            ),
                            _init_l_Lean_Meta_Match_Example_toMessageData___closed__5,
                        );
                        v___x_4271_ = lean_box(0);
                        v___x_4272_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_4269_, v___x_4271_);
                        v___x_4273_ = l_Lean_MessageData_ofList(v___x_4272_);
                        v___x_4274_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4274_, 0, v___x_4270_);
                        lean_ctor_set(v___x_4274_, 1, v___x_4273_);
                        return v___x_4274_;
                    }
                }
            }
            1 => {
                v___x_4254_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5,
                );
                v___x_4255_ = 0;
                v___x_4256_ = l_Lean_MessageData_ofConstName(v_a_4250_, v___x_4255_);
                if v_isShared_4253_ == 0 {
                    lean_ctor_set_tag(v___x_4252_, 7);
                    lean_ctor_set(v___x_4252_, 1, v___x_4256_);
                    lean_ctor_set(v___x_4252_, 0, v___x_4254_);
                    v___x_4258_ = v___x_4252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4254_);
                    lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4256_);
                    v___x_4258_ = v_reuseFailAlloc_4264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4259_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6,
                );
                v___x_4260_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(
                    v___x_4259_,
                    v_a_4245_,
                );
                v___x_4261_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4261_, 0, v___x_4258_);
                lean_ctor_set(v___x_4261_, 1, v___x_4260_);
                v___x_4262_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                );
                v___x_4263_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4263_, 0, v___x_4261_);
                lean_ctor_set(v___x_4263_, 1, v___x_4262_);
                return v___x_4263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(
    mut v_a_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4275_) == 0 {
                    v___x_4277_ = l_List_reverse___redArg(v_a_4276_);
                    return v___x_4277_;
                } else {
                    v_head_4278_ = lean_ctor_get(v_a_4275_, 0);
                    v_tail_4279_ = lean_ctor_get(v_a_4275_, 1);
                    v_isSharedCheck_4288_ = (!lean_is_exclusive(v_a_4275_)) as u8;
                    if v_isSharedCheck_4288_ == 0 {
                        v___x_4281_ = v_a_4275_;
                        v_isShared_4282_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4279_);
                        lean_inc(v_head_4278_);
                        lean_dec(v_a_4275_);
                        v___x_4281_ = lean_box(0);
                        v_isShared_4282_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4283_ = l_Lean_Meta_Match_Example_toMessageData(v_head_4278_);
                if v_isShared_4282_ == 0 {
                    lean_ctor_set(v___x_4281_, 1, v_a_4276_);
                    lean_ctor_set(v___x_4281_, 0, v___x_4283_);
                    v___x_4285_ = v___x_4281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4283_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_a_4276_);
                    v___x_4285_ = v_reuseFailAlloc_4287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4275_ = v_tail_4279_;
                v_a_4276_ = v___x_4285_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(
    mut v_a_4289_: *mut LeanObject,
    mut v_a_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4289_) == 0 {
                    v___x_4291_ = l_List_reverse___redArg(v_a_4290_);
                    return v___x_4291_;
                } else {
                    v_head_4292_ = lean_ctor_get(v_a_4289_, 0);
                    v_tail_4293_ = lean_ctor_get(v_a_4289_, 1);
                    v_isSharedCheck_4303_ = (!lean_is_exclusive(v_a_4289_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4295_ = v_a_4289_;
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4293_);
                        lean_inc(v_head_4292_);
                        lean_dec(v_a_4289_);
                        v___x_4295_ = lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_4292_);
                v___x_4298_ = l_Lean_Meta_Match_Example_toMessageData(v___x_4297_);
                if v_isShared_4296_ == 0 {
                    lean_ctor_set(v___x_4295_, 1, v_a_4290_);
                    lean_ctor_set(v___x_4295_, 0, v___x_4298_);
                    v___x_4300_ = v___x_4295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4298_);
                    lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_a_4290_);
                    v___x_4300_ = v_reuseFailAlloc_4302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4289_ = v_tail_4293_;
                v_a_4290_ = v___x_4300_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_examplesToMessageData(
    mut v_cex_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    v___x_4305_ = lean_box(0);
    v___x_4306_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(
        v_cex_4304_,
        v___x_4305_,
    );
    v___x_4307_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once),
        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11,
    );
    v___x_4308_ = l_Lean_MessageData_joinSep(v___x_4306_, v___x_4307_);
    return v___x_4308_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
    mut v_mvarId_4314_: *mut LeanObject,
    mut v_x_4315_: *mut LeanObject,
    mut v___y_4316_: *mut LeanObject,
    mut v___y_4317_: *mut LeanObject,
    mut v___y_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4321_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4314_,
                    v_x_4315_,
                    v___y_4316_,
                    v___y_4317_,
                    v___y_4318_,
                    v___y_4319_,
                );
                if lean_obj_tag(v___x_4321_) == 0 {
                    v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4329_ = (!lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4324_ = v___x_4321_;
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4322_);
                        lean_dec(v___x_4321_);
                        v___x_4324_ = lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4330_ = lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4337_ = (!lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4332_ = v___x_4321_;
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4330_);
                        lean_dec(v___x_4321_);
                        v___x_4332_ = lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4325_ == 0 {
                    v___x_4327_ = v___x_4324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
                    v___x_4327_ = v_reuseFailAlloc_4328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4327_;
            }
            3 => {
                if v_isShared_4333_ == 0 {
                    v___x_4335_ = v___x_4332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(
    mut v_mvarId_4338_: *mut LeanObject,
    mut v_x_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4345_: *mut LeanObject = core::ptr::null_mut();
    v_res_4345_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4338_,
        v_x_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
        v___y_4343_,
    );
    lean_dec(v___y_4343_);
    lean_dec_ref(v___y_4342_);
    lean_dec(v___y_4341_);
    lean_dec_ref(v___y_4340_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(
    mut v_00_u03b1_4346_: *mut LeanObject,
    mut v_mvarId_4347_: *mut LeanObject,
    mut v_x_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    v___x_4354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4347_,
        v_x_4348_,
        v___y_4349_,
        v___y_4350_,
        v___y_4351_,
        v___y_4352_,
    );
    return v___x_4354_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(
    mut v_00_u03b1_4355_: *mut LeanObject,
    mut v_mvarId_4356_: *mut LeanObject,
    mut v_x_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4363_: *mut LeanObject = core::ptr::null_mut();
    v_res_4363_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(
        v_00_u03b1_4355_,
        v_mvarId_4356_,
        v_x_4357_,
        v___y_4358_,
        v___y_4359_,
        v___y_4360_,
        v___y_4361_,
    );
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    lean_dec(v___y_4359_);
    lean_dec_ref(v___y_4358_);
    return v_res_4363_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___redArg(
    mut v_p_4364_: *mut LeanObject,
    mut v_x_4365_: *mut LeanObject,
    mut v_a_4366_: *mut LeanObject,
    mut v_a_4367_: *mut LeanObject,
    mut v_a_4368_: *mut LeanObject,
    mut v_a_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mvarId_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    v_mvarId_4371_ = lean_ctor_get(v_p_4364_, 0);
    lean_inc(v_mvarId_4371_);
    lean_dec_ref(v_p_4364_);
    v___x_4372_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(
        v_mvarId_4371_,
        v_x_4365_,
        v_a_4366_,
        v_a_4367_,
        v_a_4368_,
        v_a_4369_,
    );
    return v___x_4372_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___redArg___boxed(
    mut v_p_4373_: *mut LeanObject,
    mut v_x_4374_: *mut LeanObject,
    mut v_a_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
    mut v_a_4377_: *mut LeanObject,
    mut v_a_4378_: *mut LeanObject,
    mut v_a_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4380_: *mut LeanObject = core::ptr::null_mut();
    v_res_4380_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4373_, v_x_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_,
    );
    lean_dec(v_a_4378_);
    lean_dec_ref(v_a_4377_);
    lean_dec(v_a_4376_);
    lean_dec_ref(v_a_4375_);
    return v_res_4380_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf(
    mut v_00_u03b1_4381_: *mut LeanObject,
    mut v_p_4382_: *mut LeanObject,
    mut v_x_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4382_, v_x_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_,
    );
    return v___x_4389_;
}
pub unsafe fn l_Lean_Meta_Match_withGoalOf___boxed(
    mut v_00_u03b1_4390_: *mut LeanObject,
    mut v_p_4391_: *mut LeanObject,
    mut v_x_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4398_: *mut LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Lean_Meta_Match_withGoalOf(
        v_00_u03b1_4390_,
        v_p_4391_,
        v_x_4392_,
        v_a_4393_,
        v_a_4394_,
        v_a_4395_,
        v_a_4396_,
    );
    lean_dec(v_a_4396_);
    lean_dec_ref(v_a_4395_);
    lean_dec(v_a_4394_);
    lean_dec_ref(v_a_4393_);
    return v_res_4398_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
    mut v_x_4399_: *mut LeanObject,
    mut v_x_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4399_) == 0 {
                    v___x_4406_ = l_List_reverse___redArg(v_x_4400_);
                    v___x_4407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4407_, 0, v___x_4406_);
                    return v___x_4407_;
                } else {
                    v_head_4408_ = lean_ctor_get(v_x_4399_, 0);
                    v_tail_4409_ = lean_ctor_get(v_x_4399_, 1);
                    v_isSharedCheck_4427_ = (!lean_is_exclusive(v_x_4399_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4411_ = v_x_4399_;
                        v_isShared_4412_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4409_);
                        lean_inc(v_head_4408_);
                        lean_dec(v_x_4399_);
                        v___x_4411_ = lean_box(0);
                        v_isShared_4412_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4413_ = l_Lean_Meta_Match_Alt_toMessageData(
                    v_head_4408_,
                    v___y_4401_,
                    v___y_4402_,
                    v___y_4403_,
                    v___y_4404_,
                );
                if lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
                    lean_inc(v_a_4414_);
                    lean_dec_ref_known(v___x_4413_, 1);
                    if v_isShared_4412_ == 0 {
                        lean_ctor_set(v___x_4411_, 1, v_x_4400_);
                        lean_ctor_set(v___x_4411_, 0, v_a_4414_);
                        v___x_4416_ = v___x_4411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4414_);
                        lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_x_4400_);
                        v___x_4416_ = v_reuseFailAlloc_4418_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4411_);
                    lean_dec(v_tail_4409_);
                    lean_dec(v_x_4400_);
                    v_a_4419_ = lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4426_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4426_ == 0 {
                        v___x_4421_ = v___x_4413_;
                        v_isShared_4422_ = v_isSharedCheck_4426_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4419_);
                        lean_dec(v___x_4413_);
                        v___x_4421_ = lean_box(0);
                        v_isShared_4422_ = v_isSharedCheck_4426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4399_ = v_tail_4409_;
                v_x_4400_ = v___x_4416_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4422_ == 0 {
                    v___x_4424_ = v___x_4421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(
    mut v_x_4428_: *mut LeanObject,
    mut v_x_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4435_: *mut LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
        v_x_4428_,
        v_x_4429_,
        v___y_4430_,
        v___y_4431_,
        v___y_4432_,
        v___y_4433_,
    );
    lean_dec(v___y_4433_);
    lean_dec_ref(v___y_4432_);
    lean_dec(v___y_4431_);
    lean_dec_ref(v___y_4430_);
    return v_res_4435_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
    mut v_x_4436_: *mut LeanObject,
    mut v_x_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4436_) == 0 {
                    v___x_4443_ = l_List_reverse___redArg(v_x_4437_);
                    v___x_4444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4444_, 0, v___x_4443_);
                    return v___x_4444_;
                } else {
                    v_head_4445_ = lean_ctor_get(v_x_4436_, 0);
                    v_tail_4446_ = lean_ctor_get(v_x_4436_, 1);
                    v_isSharedCheck_4471_ = (!lean_is_exclusive(v_x_4436_)) as u8;
                    if v_isSharedCheck_4471_ == 0 {
                        v___x_4448_ = v_x_4436_;
                        v_isShared_4449_ = v_isSharedCheck_4471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4446_);
                        lean_inc(v_head_4445_);
                        lean_dec(v_x_4436_);
                        v___x_4448_ = lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_4441_);
                lean_inc_ref(v___y_4440_);
                lean_inc(v___y_4439_);
                lean_inc_ref(v___y_4438_);
                lean_inc(v_head_4445_);
                v___x_4450_ = lean_infer_type(
                    v_head_4445_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                    v___y_4441_,
                );
                if lean_obj_tag(v___x_4450_) == 0 {
                    v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
                    lean_inc(v_a_4451_);
                    lean_dec_ref_known(v___x_4450_, 1);
                    v___x_4452_ = l_Lean_MessageData_ofExpr(v_head_4445_);
                    v___x_4453_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
                    v___x_4454_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4454_, 0, v___x_4452_);
                    lean_ctor_set(v___x_4454_, 1, v___x_4453_);
                    v___x_4455_ = l_Lean_MessageData_ofExpr(v_a_4451_);
                    v___x_4456_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4456_, 0, v___x_4454_);
                    lean_ctor_set(v___x_4456_, 1, v___x_4455_);
                    v___x_4457_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once
                        ),
                        _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3,
                    );
                    v___x_4458_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4458_, 0, v___x_4456_);
                    lean_ctor_set(v___x_4458_, 1, v___x_4457_);
                    if v_isShared_4449_ == 0 {
                        lean_ctor_set(v___x_4448_, 1, v_x_4437_);
                        lean_ctor_set(v___x_4448_, 0, v___x_4458_);
                        v___x_4460_ = v___x_4448_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4458_);
                        lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_x_4437_);
                        v___x_4460_ = v_reuseFailAlloc_4462_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4448_);
                    lean_dec(v_tail_4446_);
                    lean_dec(v_head_4445_);
                    lean_dec(v_x_4437_);
                    v_a_4463_ = lean_ctor_get(v___x_4450_, 0);
                    v_isSharedCheck_4470_ = (!lean_is_exclusive(v___x_4450_)) as u8;
                    if v_isSharedCheck_4470_ == 0 {
                        v___x_4465_ = v___x_4450_;
                        v_isShared_4466_ = v_isSharedCheck_4470_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4463_);
                        lean_dec(v___x_4450_);
                        v___x_4465_ = lean_box(0);
                        v_isShared_4466_ = v_isSharedCheck_4470_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4436_ = v_tail_4446_;
                v_x_4437_ = v___x_4460_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4466_ == 0 {
                    v___x_4468_ = v___x_4465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
                    v___x_4468_ = v_reuseFailAlloc_4469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(
    mut v_x_4472_: *mut LeanObject,
    mut v_x_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4479_: *mut LeanObject = core::ptr::null_mut();
    v_res_4479_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
        v_x_4472_,
        v_x_4473_,
        v___y_4474_,
        v___y_4475_,
        v___y_4476_,
        v___y_4477_,
    );
    lean_dec(v___y_4477_);
    lean_dec_ref(v___y_4476_);
    lean_dec(v___y_4475_);
    lean_dec_ref(v___y_4474_);
    return v_res_4479_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0;
    v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
    return v___x_4482_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3() -> *mut LeanObject
{
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2;
    v___x_4485_ = l_Lean_stringToMessageData(v___x_4484_);
    return v___x_4485_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4() -> *mut LeanObject
{
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    v___x_4486_ = lean_box(1);
    v___x_4487_ = l_Lean_MessageData_ofFormat(v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6() -> *mut LeanObject
{
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    v___x_4489_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5;
    v___x_4490_ = l_Lean_stringToMessageData(v___x_4489_);
    return v___x_4490_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___lam__0(
    mut v_alts_4491_: *mut LeanObject,
    mut v___x_4492_: *mut LeanObject,
    mut v_vars_4493_: *mut LeanObject,
    mut v_examples_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_a_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4530_: u8 = 0;
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut v_a_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_4492_);
                v___x_4500_ =
                    l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(
                        v_alts_4491_,
                        v___x_4492_,
                        v___y_4495_,
                        v___y_4496_,
                        v___y_4497_,
                        v___y_4498_,
                    );
                if lean_obj_tag(v___x_4500_) == 0 {
                    v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
                    lean_inc(v_a_4501_);
                    lean_dec_ref_known(v___x_4500_, 1);
                    lean_inc(v___x_4492_);
                    v___x_4502_ =
                        l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(
                            v_vars_4493_,
                            v___x_4492_,
                            v___y_4495_,
                            v___y_4496_,
                            v___y_4497_,
                            v___y_4498_,
                        );
                    if lean_obj_tag(v___x_4502_) == 0 {
                        v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
                        v_isSharedCheck_4526_ = (!lean_is_exclusive(v___x_4502_)) as u8;
                        if v_isSharedCheck_4526_ == 0 {
                            v___x_4505_ = v___x_4502_;
                            v_isShared_4506_ = v_isSharedCheck_4526_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4503_);
                            lean_dec(v___x_4502_);
                            v___x_4505_ = lean_box(0);
                            v_isShared_4506_ = v_isSharedCheck_4526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4501_);
                        lean_dec(v_examples_4494_);
                        lean_dec(v___x_4492_);
                        v_a_4527_ = lean_ctor_get(v___x_4502_, 0);
                        v_isSharedCheck_4534_ = (!lean_is_exclusive(v___x_4502_)) as u8;
                        if v_isSharedCheck_4534_ == 0 {
                            v___x_4529_ = v___x_4502_;
                            v_isShared_4530_ = v_isSharedCheck_4534_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4527_);
                            lean_dec(v___x_4502_);
                            v___x_4529_ = lean_box(0);
                            v_isShared_4530_ = v_isSharedCheck_4534_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_examples_4494_);
                    lean_dec(v_vars_4493_);
                    lean_dec(v___x_4492_);
                    v_a_4535_ = lean_ctor_get(v___x_4500_, 0);
                    v_isSharedCheck_4542_ = (!lean_is_exclusive(v___x_4500_)) as u8;
                    if v_isSharedCheck_4542_ == 0 {
                        v___x_4537_ = v___x_4500_;
                        v_isShared_4538_ = v_isSharedCheck_4542_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4535_);
                        lean_dec(v___x_4500_);
                        v___x_4537_ = lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4542_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4507_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1,
                );
                v___x_4508_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(
                    v_a_4503_,
                    v___x_4492_,
                );
                v___x_4509_ = l_Lean_MessageData_ofList(v___x_4508_);
                v___x_4510_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4510_, 0, v___x_4507_);
                lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                v___x_4511_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3,
                );
                v___x_4512_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4512_, 0, v___x_4510_);
                lean_ctor_set(v___x_4512_, 1, v___x_4511_);
                v___x_4513_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4,
                );
                v___x_4514_ = l_Lean_MessageData_joinSep(v_a_4501_, v___x_4513_);
                v___x_4515_ = l_Lean_indentD(v___x_4514_);
                v___x_4516_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4516_, 0, v___x_4512_);
                lean_ctor_set(v___x_4516_, 1, v___x_4515_);
                v___x_4517_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6,
                );
                v___x_4518_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4518_, 0, v___x_4516_);
                lean_ctor_set(v___x_4518_, 1, v___x_4517_);
                v___x_4519_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_4494_);
                v___x_4520_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4520_, 0, v___x_4518_);
                lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                v___x_4521_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_Alt_toMessageData___closed__5_once),
                    _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5,
                );
                v___x_4522_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4522_, 0, v___x_4520_);
                lean_ctor_set(v___x_4522_, 1, v___x_4521_);
                if v_isShared_4506_ == 0 {
                    lean_ctor_set(v___x_4505_, 0, v___x_4522_);
                    v___x_4524_ = v___x_4505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
                    v___x_4524_ = v_reuseFailAlloc_4525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4524_;
            }
            3 => {
                if v_isShared_4530_ == 0 {
                    v___x_4532_ = v___x_4529_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
                    v___x_4532_ = v_reuseFailAlloc_4533_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4532_;
            }
            5 => {
                if v_isShared_4538_ == 0 {
                    v___x_4540_ = v___x_4537_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
                    v___x_4540_ = v_reuseFailAlloc_4541_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(
    mut v_alts_4543_: *mut LeanObject,
    mut v___x_4544_: *mut LeanObject,
    mut v_vars_4545_: *mut LeanObject,
    mut v_examples_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4552_: *mut LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(
        v_alts_4543_,
        v___x_4544_,
        v_vars_4545_,
        v_examples_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
        v___y_4550_,
    );
    lean_dec(v___y_4550_);
    lean_dec_ref(v___y_4549_);
    lean_dec(v___y_4548_);
    lean_dec_ref(v___y_4547_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData(
    mut v_p_4553_: *mut LeanObject,
    mut v_a_4554_: *mut LeanObject,
    mut v_a_4555_: *mut LeanObject,
    mut v_a_4556_: *mut LeanObject,
    mut v_a_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_examples_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    v_vars_4559_ = lean_ctor_get(v_p_4553_, 1);
    v_alts_4560_ = lean_ctor_get(v_p_4553_, 2);
    v_examples_4561_ = lean_ctor_get(v_p_4553_, 3);
    v___x_4562_ = lean_box(0);
    lean_inc(v_examples_4561_);
    lean_inc(v_vars_4559_);
    lean_inc(v_alts_4560_);
    v___f_4563_ = lean_alloc_closure(
        l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_4563_, 0, v_alts_4560_);
    lean_closure_set(v___f_4563_, 1, v___x_4562_);
    lean_closure_set(v___f_4563_, 2, v_vars_4559_);
    lean_closure_set(v___f_4563_, 3, v_examples_4561_);
    v___x_4564_ = l_Lean_Meta_Match_withGoalOf___redArg(
        v_p_4553_,
        v___f_4563_,
        v_a_4554_,
        v_a_4555_,
        v_a_4556_,
        v_a_4557_,
    );
    return v___x_4564_;
}
pub unsafe fn l_Lean_Meta_Match_Problem_toMessageData___boxed(
    mut v_p_4565_: *mut LeanObject,
    mut v_a_4566_: *mut LeanObject,
    mut v_a_4567_: *mut LeanObject,
    mut v_a_4568_: *mut LeanObject,
    mut v_a_4569_: *mut LeanObject,
    mut v_a_4570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4571_: *mut LeanObject = core::ptr::null_mut();
    v_res_4571_ = l_Lean_Meta_Match_Problem_toMessageData(
        v_p_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_,
    );
    lean_dec(v_a_4569_);
    lean_dec_ref(v_a_4568_);
    lean_dec(v_a_4567_);
    lean_dec_ref(v_a_4566_);
    return v_res_4571_;
}
pub unsafe fn l_Lean_Meta_Match_counterExampleToMessageData(
    mut v_cex_4572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    v___x_4573_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_4572_);
    return v___x_4573_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(
    mut v_a_4574_: *mut LeanObject,
    mut v_a_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4574_) == 0 {
                    v___x_4576_ = l_List_reverse___redArg(v_a_4575_);
                    return v___x_4576_;
                } else {
                    v_head_4577_ = lean_ctor_get(v_a_4574_, 0);
                    v_tail_4578_ = lean_ctor_get(v_a_4574_, 1);
                    v_isSharedCheck_4587_ = (!lean_is_exclusive(v_a_4574_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v___x_4580_ = v_a_4574_;
                        v_isShared_4581_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4578_);
                        lean_inc(v_head_4577_);
                        lean_dec(v_a_4574_);
                        v___x_4580_ = lean_box(0);
                        v_isShared_4581_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4582_ = l_Lean_Meta_Match_examplesToMessageData(v_head_4577_);
                if v_isShared_4581_ == 0 {
                    lean_ctor_set(v___x_4580_, 1, v_a_4575_);
                    lean_ctor_set(v___x_4580_, 0, v___x_4582_);
                    v___x_4584_ = v___x_4580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4582_);
                    lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_a_4575_);
                    v___x_4584_ = v_reuseFailAlloc_4586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4574_ = v_tail_4578_;
                v_a_4575_ = v___x_4584_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_counterExamplesToMessageData(
    mut v_cexs_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    v___x_4589_ = lean_array_to_list(v_cexs_4588_);
    v___x_4590_ = lean_box(0);
    v___x_4591_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(
        v___x_4589_,
        v___x_4590_,
    );
    v___x_4592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once),
        _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4,
    );
    v___x_4593_ = l_Lean_MessageData_joinSep(v___x_4591_, v___x_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
    mut v_msg_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4600_ = lean_ctor_get(v___y_4597_, 5);
                v___x_4601_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(
                        v_msg_4594_,
                        v___y_4595_,
                        v___y_4596_,
                        v___y_4597_,
                        v___y_4598_,
                    );
                v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
                v_isSharedCheck_4610_ = (!lean_is_exclusive(v___x_4601_)) as u8;
                if v_isSharedCheck_4610_ == 0 {
                    v___x_4604_ = v___x_4601_;
                    v_isShared_4605_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4602_);
                    lean_dec(v___x_4601_);
                    v___x_4604_ = lean_box(0);
                    v_isShared_4605_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4600_);
                v___x_4606_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4606_, 0, v_ref_4600_);
                lean_ctor_set(v___x_4606_, 1, v_a_4602_);
                if v_isShared_4605_ == 0 {
                    lean_ctor_set_tag(v___x_4604_, 1);
                    lean_ctor_set(v___x_4604_, 0, v___x_4606_);
                    v___x_4608_ = v___x_4604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(
    mut v_msg_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
        v_msg_4611_,
        v___y_4612_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
    );
    lean_dec(v___y_4615_);
    lean_dec_ref(v___y_4614_);
    lean_dec(v___y_4613_);
    lean_dec_ref(v___y_4612_);
    return v_res_4617_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__1() -> *mut LeanObject {
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_Meta_Match_toPattern___closed__0;
    v___x_4620_ = l_Lean_stringToMessageData(v___x_4619_);
    return v___x_4620_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__3() -> *mut LeanObject {
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    v___x_4622_ = l_Lean_Meta_Match_toPattern___closed__2;
    v___x_4623_ = l_Lean_stringToMessageData(v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn _init_l_Lean_Meta_Match_toPattern___closed__4() -> *mut LeanObject {
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4625_: *mut LeanObject = core::ptr::null_mut();
    v___x_4624_ = lean_box(0);
    v_dummy_4625_ = l_Lean_Expr_sort___override(v___x_4624_);
    return v_dummy_4625_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(
    mut v_sz_4626_: usize,
    mut v_i_4627_: usize,
    mut v_bs_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: usize = 0;
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4634_ = lean_usize_dec_lt(v_i_4627_, v_sz_4626_);
                if v___x_4634_ == 0 {
                    v___x_4635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4635_, 0, v_bs_4628_);
                    return v___x_4635_;
                } else {
                    v_v_4636_ = lean_array_uget_borrowed(v_bs_4628_, v_i_4627_);
                    lean_inc(v_v_4636_);
                    v___x_4637_ = l_Lean_Meta_Match_toPattern(
                        v_v_4636_,
                        v___y_4629_,
                        v___y_4630_,
                        v___y_4631_,
                        v___y_4632_,
                    );
                    if lean_obj_tag(v___x_4637_) == 0 {
                        v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
                        lean_inc(v_a_4638_);
                        lean_dec_ref_known(v___x_4637_, 1);
                        v___x_4639_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4640_ = lean_array_uset(v_bs_4628_, v_i_4627_, v___x_4639_);
                        v___x_4641_ = 1usize;
                        v___x_4642_ = lean_usize_add(v_i_4627_, v___x_4641_);
                        v___x_4643_ = lean_array_uset(v_bs_x27_4640_, v_i_4627_, v_a_4638_);
                        v_i_4627_ = v___x_4642_;
                        v_bs_4628_ = v___x_4643_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4628_);
                        v_a_4645_ = lean_ctor_get(v___x_4637_, 0);
                        v_isSharedCheck_4652_ = (!lean_is_exclusive(v___x_4637_)) as u8;
                        if v_isSharedCheck_4652_ == 0 {
                            v___x_4647_ = v___x_4637_;
                            v_isShared_4648_ = v_isSharedCheck_4652_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4645_);
                            lean_dec(v___x_4637_);
                            v___x_4647_ = lean_box(0);
                            v_isShared_4648_ = v_isSharedCheck_4652_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4648_ == 0 {
                    v___x_4650_ = v___x_4647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
                    v___x_4650_ = v_reuseFailAlloc_4651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_toPattern(
    mut v_e_4653_: *mut LeanObject,
    mut v_a_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v_a_4657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___y_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4708_: u8 = 0;
    let mut v___x_4709_: u8 = 0;
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4741_: usize = 0;
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v_name_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_a_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v_a_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4797_: u8 = 0;
    let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_val_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut v_a_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4828_: u8 = 0;
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4832_: u8 = 0;
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_val_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4668_ = l_Lean_inaccessible_x3f(v_e_4653_);
                if lean_obj_tag(v___x_4668_) == 0 {
                    v___x_4669_ = l_Lean_Expr_arrayLit_x3f(v_e_4653_);
                    if lean_obj_tag(v___x_4669_) == 0 {
                        v___x_4670_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_4653_);
                        if lean_obj_tag(v___x_4670_) == 1 {
                            lean_dec_ref(v_e_4653_);
                            v_val_4671_ = lean_ctor_get(v___x_4670_, 0);
                            lean_inc(v_val_4671_);
                            lean_dec_ref_known(v___x_4670_, 1);
                            v___x_4672_ = lean_unsigned_to_nat(2);
                            v___x_4673_ = l_Lean_Expr_getAppNumArgs(v_val_4671_);
                            v___x_4674_ = lean_nat_sub(v___x_4673_, v___x_4672_);
                            v___x_4675_ = lean_unsigned_to_nat(1);
                            v___x_4676_ = lean_nat_sub(v___x_4674_, v___x_4675_);
                            lean_dec(v___x_4674_);
                            v___x_4677_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4676_);
                            v___x_4678_ = l_Lean_Meta_Match_toPattern(
                                v___x_4677_,
                                v_a_4654_,
                                v_a_4655_,
                                v_a_4656_,
                                v_a_4657_,
                            );
                            if lean_obj_tag(v___x_4678_) == 0 {
                                v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
                                v_isSharedCheck_4703_ = (!lean_is_exclusive(v___x_4678_)) as u8;
                                if v_isSharedCheck_4703_ == 0 {
                                    v___x_4681_ = v___x_4678_;
                                    v_isShared_4682_ = v_isSharedCheck_4703_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_4679_);
                                    lean_dec(v___x_4678_);
                                    v___x_4681_ = lean_box(0);
                                    v_isShared_4682_ = v_isSharedCheck_4703_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4673_);
                                lean_dec(v_val_4671_);
                                return v___x_4678_;
                            }
                        } else {
                            lean_dec(v___x_4670_);
                            lean_inc_ref(v_e_4653_);
                            v___x_4704_ = l_Lean_Meta_isMatchValue(
                                v_e_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_,
                            );
                            if lean_obj_tag(v___x_4704_) == 0 {
                                v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
                                v_isSharedCheck_4797_ = (!lean_is_exclusive(v___x_4704_)) as u8;
                                if v_isSharedCheck_4797_ == 0 {
                                    v___x_4707_ = v___x_4704_;
                                    v_isShared_4708_ = v_isSharedCheck_4797_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_4705_);
                                    lean_dec(v___x_4704_);
                                    v___x_4707_ = lean_box(0);
                                    v_isShared_4708_ = v_isSharedCheck_4797_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_e_4653_);
                                v_a_4798_ = lean_ctor_get(v___x_4704_, 0);
                                v_isSharedCheck_4805_ = (!lean_is_exclusive(v___x_4704_)) as u8;
                                if v_isSharedCheck_4805_ == 0 {
                                    v___x_4800_ = v___x_4704_;
                                    v_isShared_4801_ = v_isSharedCheck_4805_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_4798_);
                                    lean_dec(v___x_4704_);
                                    v___x_4800_ = lean_box(0);
                                    v_isShared_4801_ = v_isSharedCheck_4805_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_4653_);
                        v_val_4806_ = lean_ctor_get(v___x_4669_, 0);
                        lean_inc(v_val_4806_);
                        lean_dec_ref_known(v___x_4669_, 1);
                        v_fst_4807_ = lean_ctor_get(v_val_4806_, 0);
                        v_snd_4808_ = lean_ctor_get(v_val_4806_, 1);
                        v_isSharedCheck_4833_ = (!lean_is_exclusive(v_val_4806_)) as u8;
                        if v_isSharedCheck_4833_ == 0 {
                            v___x_4810_ = v_val_4806_;
                            v_isShared_4811_ = v_isSharedCheck_4833_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_snd_4808_);
                            lean_inc(v_fst_4807_);
                            lean_dec(v_val_4806_);
                            v___x_4810_ = lean_box(0);
                            v_isShared_4811_ = v_isSharedCheck_4833_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_4653_);
                    v_val_4834_ = lean_ctor_get(v___x_4668_, 0);
                    v_isSharedCheck_4842_ = (!lean_is_exclusive(v___x_4668_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4836_ = v___x_4668_;
                        v_isShared_4837_ = v_isSharedCheck_4842_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_val_4834_);
                        lean_dec(v___x_4668_);
                        v___x_4836_ = lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4842_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4664_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1_once),
                    _init_l_Lean_Meta_Match_toPattern___closed__1,
                );
                v___x_4665_ = l_Lean_indentExpr(v_e_4653_);
                v___x_4666_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4666_, 0, v___x_4664_);
                lean_ctor_set(v___x_4666_, 1, v___x_4665_);
                v___x_4667_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
                    v___x_4666_,
                    v___y_4660_,
                    v___y_4661_,
                    v___y_4662_,
                    v___y_4663_,
                );
                return v___x_4667_;
            }
            2 => {
                v___x_4690_ = lean_nat_sub(v___x_4673_, v___x_4675_);
                v___x_4691_ = lean_nat_sub(v___x_4690_, v___x_4675_);
                lean_dec(v___x_4690_);
                v___x_4692_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4691_);
                if lean_obj_tag(v___x_4692_) == 1 {
                    v_fvarId_4693_ = lean_ctor_get(v___x_4692_, 0);
                    lean_inc(v_fvarId_4693_);
                    lean_dec_ref_known(v___x_4692_, 1);
                    v___x_4694_ = lean_unsigned_to_nat(3);
                    v___x_4695_ = lean_nat_sub(v___x_4673_, v___x_4694_);
                    lean_dec(v___x_4673_);
                    v___x_4696_ = lean_nat_sub(v___x_4695_, v___x_4675_);
                    lean_dec(v___x_4695_);
                    v___x_4697_ = l_Lean_Expr_getRevArg_x21(v_val_4671_, v___x_4696_);
                    lean_dec(v_val_4671_);
                    if lean_obj_tag(v___x_4697_) == 1 {
                        v_fvarId_4698_ = lean_ctor_get(v___x_4697_, 0);
                        lean_inc(v_fvarId_4698_);
                        lean_dec_ref_known(v___x_4697_, 1);
                        v___x_4699_ = lean_alloc_ctor(5, 3, (0) as u32);
                        lean_ctor_set(v___x_4699_, 0, v_fvarId_4693_);
                        lean_ctor_set(v___x_4699_, 1, v_a_4679_);
                        lean_ctor_set(v___x_4699_, 2, v_fvarId_4698_);
                        if v_isShared_4682_ == 0 {
                            lean_ctor_set(v___x_4681_, 0, v___x_4699_);
                            v___x_4701_ = v___x_4681_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4699_);
                            v___x_4701_ = v_reuseFailAlloc_4702_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4697_);
                        lean_dec(v_fvarId_4693_);
                        lean_del_object(v___x_4681_);
                        lean_dec(v_a_4679_);
                        v___y_4684_ = v_a_4654_;
                        v___y_4685_ = v_a_4655_;
                        v___y_4686_ = v_a_4656_;
                        v___y_4687_ = v_a_4657_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4692_);
                    lean_del_object(v___x_4681_);
                    lean_dec(v_a_4679_);
                    lean_dec(v___x_4673_);
                    lean_dec(v_val_4671_);
                    v___y_4684_ = v_a_4654_;
                    v___y_4685_ = v_a_4655_;
                    v___y_4686_ = v_a_4656_;
                    v___y_4687_ = v_a_4657_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4688_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__3_once),
                    _init_l_Lean_Meta_Match_toPattern___closed__3,
                );
                v___x_4689_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
                    v___x_4688_,
                    v___y_4684_,
                    v___y_4685_,
                    v___y_4686_,
                    v___y_4687_,
                );
                return v___x_4689_;
            }
            4 => {
                return v___x_4701_;
            }
            5 => {
                v___x_4709_ = (lean_unbox(v_a_4705_) as u8);
                lean_dec(v_a_4705_);
                if v___x_4709_ == 0 {
                    v___x_4710_ = l_Lean_Expr_isFVar(v_e_4653_);
                    if v___x_4710_ == 0 {
                        lean_del_object(v___x_4707_);
                        lean_inc(v_a_4657_);
                        lean_inc_ref(v_a_4656_);
                        lean_inc(v_a_4655_);
                        lean_inc_ref(v_a_4654_);
                        lean_inc_ref(v_e_4653_);
                        v___x_4711_ =
                            lean_whnf(v_e_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
                        if lean_obj_tag(v___x_4711_) == 0 {
                            v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
                            lean_inc(v_a_4712_);
                            lean_dec_ref_known(v___x_4711_, 1);
                            v___x_4713_ = lean_expr_eqv(v_a_4712_, v_e_4653_);
                            if v___x_4713_ == 0 {
                                lean_dec_ref(v_e_4653_);
                                v_e_4653_ = v_a_4712_;
                                state = 0;
                                continue;
                            } else {
                                if v___x_4710_ == 0 {
                                    lean_dec(v_a_4712_);
                                    v___x_4715_ = l_Lean_Expr_getAppFn(v_e_4653_);
                                    if lean_obj_tag(v___x_4715_) == 4 {
                                        v_declName_4716_ = lean_ctor_get(v___x_4715_, 0);
                                        lean_inc(v_declName_4716_);
                                        v_us_4717_ = lean_ctor_get(v___x_4715_, 1);
                                        lean_inc(v_us_4717_);
                                        lean_dec_ref_known(v___x_4715_, 2);
                                        v___x_4718_ = lean_st_ref_get(v_a_4657_);
                                        v_env_4719_ = lean_ctor_get(v___x_4718_, 0);
                                        lean_inc_ref(v_env_4719_);
                                        lean_dec(v___x_4718_);
                                        v___x_4720_ = l_Lean_Environment_find_x3f(
                                            v_env_4719_,
                                            v_declName_4716_,
                                            v___x_4710_,
                                        );
                                        if lean_obj_tag(v___x_4720_) == 0 {
                                            lean_dec(v_us_4717_);
                                            v___y_4660_ = v_a_4654_;
                                            v___y_4661_ = v_a_4655_;
                                            v___y_4662_ = v_a_4656_;
                                            v___y_4663_ = v_a_4657_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_val_4721_ = lean_ctor_get(v___x_4720_, 0);
                                            lean_inc(v_val_4721_);
                                            lean_dec_ref_known(v___x_4720_, 1);
                                            if lean_obj_tag(v_val_4721_) == 6 {
                                                v_val_4722_ = lean_ctor_get(v_val_4721_, 0);
                                                lean_inc_ref(v_val_4722_);
                                                lean_dec_ref_known(v_val_4721_, 1);
                                                v_toConstantVal_4723_ =
                                                    lean_ctor_get(v_val_4722_, 0);
                                                lean_inc_ref(v_toConstantVal_4723_);
                                                v_numParams_4724_ = lean_ctor_get(v_val_4722_, 3);
                                                lean_inc(v_numParams_4724_);
                                                v_numFields_4725_ = lean_ctor_get(v_val_4722_, 4);
                                                lean_inc(v_numFields_4725_);
                                                lean_dec_ref(v_val_4722_);
                                                v_nargs_4726_ =
                                                    l_Lean_Expr_getAppNumArgs(v_e_4653_);
                                                v_dummy_4727_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__4_once), _init_l_Lean_Meta_Match_toPattern___closed__4);
                                                lean_inc(v_nargs_4726_);
                                                v___x_4728_ =
                                                    lean_mk_array(v_nargs_4726_, v_dummy_4727_);
                                                v___x_4729_ = lean_unsigned_to_nat(1);
                                                v___x_4730_ =
                                                    lean_nat_sub(v_nargs_4726_, v___x_4729_);
                                                lean_dec(v_nargs_4726_);
                                                lean_inc_ref(v_e_4653_);
                                                v___x_4731_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4653_, v___x_4728_, v___x_4730_);
                                                v___x_4764_ = lean_array_get_size(v___x_4731_);
                                                v___x_4765_ = lean_nat_add(
                                                    v_numParams_4724_,
                                                    v_numFields_4725_,
                                                );
                                                lean_dec(v_numFields_4725_);
                                                v___x_4766_ =
                                                    lean_nat_dec_eq(v___x_4764_, v___x_4765_);
                                                lean_dec(v___x_4765_);
                                                if v___x_4766_ == 0 {
                                                    v___x_4767_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Match_toPattern___closed__1_once), _init_l_Lean_Meta_Match_toPattern___closed__1);
                                                    v___x_4768_ = l_Lean_indentExpr(v_e_4653_);
                                                    v___x_4769_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                    lean_ctor_set(v___x_4769_, 0, v___x_4767_);
                                                    lean_ctor_set(v___x_4769_, 1, v___x_4768_);
                                                    v___x_4770_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_4769_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
                                                    if lean_obj_tag(v___x_4770_) == 0 {
                                                        lean_dec_ref_known(v___x_4770_, 1);
                                                        v___y_4733_ = v_a_4654_;
                                                        v___y_4734_ = v_a_4655_;
                                                        v___y_4735_ = v_a_4656_;
                                                        v___y_4736_ = v_a_4657_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        lean_dec_ref(v___x_4731_);
                                                        lean_dec(v_numParams_4724_);
                                                        lean_dec_ref(v_toConstantVal_4723_);
                                                        lean_dec(v_us_4717_);
                                                        v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
                                                        v_isSharedCheck_4778_ =
                                                            (!lean_is_exclusive(v___x_4770_)) as u8;
                                                        if v_isSharedCheck_4778_ == 0 {
                                                            v___x_4773_ = v___x_4770_;
                                                            v_isShared_4774_ =
                                                                v_isSharedCheck_4778_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4771_);
                                                            lean_dec(v___x_4770_);
                                                            v___x_4773_ = lean_box(0);
                                                            v_isShared_4774_ =
                                                                v_isSharedCheck_4778_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_e_4653_);
                                                    v___y_4733_ = v_a_4654_;
                                                    v___y_4734_ = v_a_4655_;
                                                    v___y_4735_ = v_a_4656_;
                                                    v___y_4736_ = v_a_4657_;
                                                    state = 6;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_val_4721_);
                                                lean_dec(v_us_4717_);
                                                v___y_4660_ = v_a_4654_;
                                                v___y_4661_ = v_a_4655_;
                                                v___y_4662_ = v_a_4656_;
                                                v___y_4663_ = v_a_4657_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_4715_);
                                        v___y_4660_ = v_a_4654_;
                                        v___y_4661_ = v_a_4655_;
                                        v___y_4662_ = v_a_4656_;
                                        v___y_4663_ = v_a_4657_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_e_4653_);
                                    v_e_4653_ = v_a_4712_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_e_4653_);
                            v_a_4780_ = lean_ctor_get(v___x_4711_, 0);
                            v_isSharedCheck_4787_ = (!lean_is_exclusive(v___x_4711_)) as u8;
                            if v_isSharedCheck_4787_ == 0 {
                                v___x_4782_ = v___x_4711_;
                                v_isShared_4783_ = v_isSharedCheck_4787_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_4780_);
                                lean_dec(v___x_4711_);
                                v___x_4782_ = lean_box(0);
                                v_isShared_4783_ = v_isSharedCheck_4787_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_4788_ = l_Lean_Expr_fvarId_x21(v_e_4653_);
                        lean_dec_ref(v_e_4653_);
                        v___x_4789_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                        if v_isShared_4708_ == 0 {
                            lean_ctor_set(v___x_4707_, 0, v___x_4789_);
                            v___x_4791_ = v___x_4707_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
                            v___x_4791_ = v_reuseFailAlloc_4792_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v___x_4793_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_4793_, 0, v_e_4653_);
                    if v_isShared_4708_ == 0 {
                        lean_ctor_set(v___x_4707_, 0, v___x_4793_);
                        v___x_4795_ = v___x_4707_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4793_);
                        v___x_4795_ = v_reuseFailAlloc_4796_;
                        state = 16;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4737_ = lean_unsigned_to_nat(0);
                lean_inc(v_numParams_4724_);
                v___x_4738_ = l_Array_extract___redArg(v___x_4731_, v___x_4737_, v_numParams_4724_);
                v___x_4739_ = lean_array_get_size(v___x_4731_);
                v___x_4740_ = l_Array_extract___redArg(v___x_4731_, v_numParams_4724_, v___x_4739_);
                lean_dec_ref(v___x_4731_);
                v_sz_4741_ = lean_array_size(v___x_4740_);
                v___x_4742_ = 0usize;
                v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_4741_, v___x_4742_, v___x_4740_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
                if lean_obj_tag(v___x_4743_) == 0 {
                    v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
                    v_isSharedCheck_4755_ = (!lean_is_exclusive(v___x_4743_)) as u8;
                    if v_isSharedCheck_4755_ == 0 {
                        v___x_4746_ = v___x_4743_;
                        v_isShared_4747_ = v_isSharedCheck_4755_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4744_);
                        lean_dec(v___x_4743_);
                        v___x_4746_ = lean_box(0);
                        v_isShared_4747_ = v_isSharedCheck_4755_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4738_);
                    lean_dec_ref(v_toConstantVal_4723_);
                    lean_dec(v_us_4717_);
                    v_a_4756_ = lean_ctor_get(v___x_4743_, 0);
                    v_isSharedCheck_4763_ = (!lean_is_exclusive(v___x_4743_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4758_ = v___x_4743_;
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4756_);
                        lean_dec(v___x_4743_);
                        v___x_4758_ = lean_box(0);
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v_name_4748_ = lean_ctor_get(v_toConstantVal_4723_, 0);
                lean_inc(v_name_4748_);
                lean_dec_ref(v_toConstantVal_4723_);
                v___x_4749_ = lean_array_to_list(v___x_4738_);
                v___x_4750_ = lean_array_to_list(v_a_4744_);
                v___x_4751_ = lean_alloc_ctor(2, 4, (0) as u32);
                lean_ctor_set(v___x_4751_, 0, v_name_4748_);
                lean_ctor_set(v___x_4751_, 1, v_us_4717_);
                lean_ctor_set(v___x_4751_, 2, v___x_4749_);
                lean_ctor_set(v___x_4751_, 3, v___x_4750_);
                if v_isShared_4747_ == 0 {
                    lean_ctor_set(v___x_4746_, 0, v___x_4751_);
                    v___x_4753_ = v___x_4746_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4753_;
            }
            9 => {
                if v_isShared_4759_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4761_;
            }
            11 => {
                if v_isShared_4774_ == 0 {
                    v___x_4776_ = v___x_4773_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4776_;
            }
            13 => {
                if v_isShared_4783_ == 0 {
                    v___x_4785_ = v___x_4782_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4785_;
            }
            15 => {
                return v___x_4791_;
            }
            16 => {
                return v___x_4795_;
            }
            17 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4803_;
            }
            19 => {
                v___x_4812_ = lean_box(0);
                v___x_4813_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
                    v_snd_4808_,
                    v___x_4812_,
                    v_a_4654_,
                    v_a_4655_,
                    v_a_4656_,
                    v_a_4657_,
                );
                if lean_obj_tag(v___x_4813_) == 0 {
                    v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
                    v_isSharedCheck_4824_ = (!lean_is_exclusive(v___x_4813_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v___x_4816_ = v___x_4813_;
                        v_isShared_4817_ = v_isSharedCheck_4824_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_4814_);
                        lean_dec(v___x_4813_);
                        v___x_4816_ = lean_box(0);
                        v_isShared_4817_ = v_isSharedCheck_4824_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4810_);
                    lean_dec(v_fst_4807_);
                    v_a_4825_ = lean_ctor_get(v___x_4813_, 0);
                    v_isSharedCheck_4832_ = (!lean_is_exclusive(v___x_4813_)) as u8;
                    if v_isSharedCheck_4832_ == 0 {
                        v___x_4827_ = v___x_4813_;
                        v_isShared_4828_ = v_isSharedCheck_4832_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4825_);
                        lean_dec(v___x_4813_);
                        v___x_4827_ = lean_box(0);
                        v_isShared_4828_ = v_isSharedCheck_4832_;
                        state = 23;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_4811_ == 0 {
                    lean_ctor_set_tag(v___x_4810_, 4);
                    lean_ctor_set(v___x_4810_, 1, v_a_4814_);
                    v___x_4819_ = v___x_4810_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4823_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_fst_4807_);
                    lean_ctor_set(v_reuseFailAlloc_4823_, 1, v_a_4814_);
                    v___x_4819_ = v_reuseFailAlloc_4823_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4817_ == 0 {
                    lean_ctor_set(v___x_4816_, 0, v___x_4819_);
                    v___x_4821_ = v___x_4816_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4821_;
            }
            23 => {
                if v_isShared_4828_ == 0 {
                    v___x_4830_ = v___x_4827_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
                    v___x_4830_ = v_reuseFailAlloc_4831_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4830_;
            }
            25 => {
                if v_isShared_4837_ == 0 {
                    lean_ctor_set_tag(v___x_4836_, 0);
                    v___x_4839_ = v___x_4836_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_val_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4841_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4840_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4840_, 0, v___x_4839_);
                return v___x_4840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
    mut v_x_4843_: *mut LeanObject,
    mut v_x_4844_: *mut LeanObject,
    mut v___y_4845_: *mut LeanObject,
    mut v___y_4846_: *mut LeanObject,
    mut v___y_4847_: *mut LeanObject,
    mut v___y_4848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4843_) == 0 {
                    v___x_4850_ = l_List_reverse___redArg(v_x_4844_);
                    v___x_4851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4851_, 0, v___x_4850_);
                    return v___x_4851_;
                } else {
                    v_head_4852_ = lean_ctor_get(v_x_4843_, 0);
                    v_tail_4853_ = lean_ctor_get(v_x_4843_, 1);
                    v_isSharedCheck_4871_ = (!lean_is_exclusive(v_x_4843_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4855_ = v_x_4843_;
                        v_isShared_4856_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4853_);
                        lean_inc(v_head_4852_);
                        lean_dec(v_x_4843_);
                        v___x_4855_ = lean_box(0);
                        v_isShared_4856_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4857_ = l_Lean_Meta_Match_toPattern(
                    v_head_4852_,
                    v___y_4845_,
                    v___y_4846_,
                    v___y_4847_,
                    v___y_4848_,
                );
                if lean_obj_tag(v___x_4857_) == 0 {
                    v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
                    lean_inc(v_a_4858_);
                    lean_dec_ref_known(v___x_4857_, 1);
                    if v_isShared_4856_ == 0 {
                        lean_ctor_set(v___x_4855_, 1, v_x_4844_);
                        lean_ctor_set(v___x_4855_, 0, v_a_4858_);
                        v___x_4860_ = v___x_4855_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4858_);
                        lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_x_4844_);
                        v___x_4860_ = v_reuseFailAlloc_4862_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4855_);
                    lean_dec(v_tail_4853_);
                    lean_dec(v_x_4844_);
                    v_a_4863_ = lean_ctor_get(v___x_4857_, 0);
                    v_isSharedCheck_4870_ = (!lean_is_exclusive(v___x_4857_)) as u8;
                    if v_isSharedCheck_4870_ == 0 {
                        v___x_4865_ = v___x_4857_;
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4863_);
                        lean_dec(v___x_4857_);
                        v___x_4865_ = lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4870_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4843_ = v_tail_4853_;
                v_x_4844_ = v___x_4860_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4866_ == 0 {
                    v___x_4868_ = v___x_4865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(
    mut v_x_4872_: *mut LeanObject,
    mut v_x_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4879_: *mut LeanObject = core::ptr::null_mut();
    v_res_4879_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(
        v_x_4872_,
        v_x_4873_,
        v___y_4874_,
        v___y_4875_,
        v___y_4876_,
        v___y_4877_,
    );
    lean_dec(v___y_4877_);
    lean_dec_ref(v___y_4876_);
    lean_dec(v___y_4875_);
    lean_dec_ref(v___y_4874_);
    return v_res_4879_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(
    mut v_sz_4880_: *mut LeanObject,
    mut v_i_4881_: *mut LeanObject,
    mut v_bs_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4888_: usize = 0;
    let mut v_i_boxed_4889_: usize = 0;
    let mut v_res_4890_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4888_ = lean_unbox_usize(v_sz_4880_);
    lean_dec(v_sz_4880_);
    v_i_boxed_4889_ = lean_unbox_usize(v_i_4881_);
    lean_dec(v_i_4881_);
    v_res_4890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_4888_, v_i_boxed_4889_, v_bs_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
    lean_dec(v___y_4886_);
    lean_dec_ref(v___y_4885_);
    lean_dec(v___y_4884_);
    lean_dec_ref(v___y_4883_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_Meta_Match_toPattern___boxed(
    mut v_e_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
    mut v_a_4894_: *mut LeanObject,
    mut v_a_4895_: *mut LeanObject,
    mut v_a_4896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4897_: *mut LeanObject = core::ptr::null_mut();
    v_res_4897_ =
        l_Lean_Meta_Match_toPattern(v_e_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
    lean_dec(v_a_4895_);
    lean_dec_ref(v_a_4894_);
    lean_dec(v_a_4893_);
    lean_dec_ref(v_a_4892_);
    return v_res_4897_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(
    mut v_00_u03b1_4898_: *mut LeanObject,
    mut v_msg_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(
        v_msg_4899_,
        v___y_4900_,
        v___y_4901_,
        v___y_4902_,
        v___y_4903_,
    );
    return v___x_4905_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(
    mut v_00_u03b1_4906_: *mut LeanObject,
    mut v_msg_4907_: *mut LeanObject,
    mut v___y_4908_: *mut LeanObject,
    mut v___y_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4913_: *mut LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(
        v_00_u03b1_4906_,
        v_msg_4907_,
        v___y_4908_,
        v___y_4909_,
        v___y_4910_,
        v___y_4911_,
    );
    lean_dec(v___y_4911_);
    lean_dec_ref(v___y_4910_);
    lean_dec(v___y_4909_);
    lean_dec_ref(v___y_4908_);
    return v_res_4913_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    v___x_4920_ = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
    v___x_4921_ = lean_string_utf8_byte_size(v___x_4920_);
    return v___x_4921_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(
    mut v_s_4922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    v___x_4923_ = l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0;
    v___x_4924_ = lean_string_utf8_byte_size(v_s_4922_);
    v___x_4925_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0);
    v___x_4926_ = lean_nat_dec_le(v___x_4925_, v___x_4924_);
    if v___x_4926_ == 0 {
        let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4922_);
        v___x_4927_ = lean_box(0);
        return v___x_4927_;
    } else {
        let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4929_: u8 = 0;
        v___x_4928_ = lean_unsigned_to_nat(0);
        v___x_4929_ = lean_string_memcmp(
            v_s_4922_,
            v___x_4923_,
            v___x_4928_,
            v___x_4928_,
            v___x_4925_,
        );
        if v___x_4929_ == 0 {
            let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4922_);
            v___x_4930_ = lean_box(0);
            return v___x_4930_;
        } else {
            let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4922_);
            v___x_4931_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4931_, 0, v_s_4922_);
            lean_ctor_set(v___x_4931_, 1, v___x_4928_);
            lean_ctor_set(v___x_4931_, 2, v___x_4924_);
            v___x_4932_ = l_String_Slice_pos_x21(v___x_4931_, v___x_4925_);
            lean_dec_ref_known(v___x_4931_, 3);
            v___x_4933_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4933_, 0, v_s_4922_);
            lean_ctor_set(v___x_4933_, 1, v___x_4932_);
            lean_ctor_set(v___x_4933_, 2, v___x_4924_);
            v___x_4934_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4934_, 0, v___x_4933_);
            return v___x_4934_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(
    mut v_s_4935_: *mut LeanObject,
    mut v_pat_4936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    v___x_4937_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_4935_);
    return v___x_4937_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(
    mut v_s_4938_: *mut LeanObject,
    mut v_pat_4939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4940_: *mut LeanObject = core::ptr::null_mut();
    v_res_4940_ =
        l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(
            v_s_4938_,
            v_pat_4939_,
        );
    lean_dec_ref(v_pat_4939_);
    return v_res_4940_;
}
pub unsafe fn l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(mut v_s_4941_: *mut LeanObject) -> u8 {
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    v___x_4942_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_4941_);
    if lean_obj_tag(v___x_4942_) == 0 {
        let mut v___x_4943_: u8 = 0;
        v___x_4943_ = 0;
        return v___x_4943_;
    } else {
        let mut v_val_4944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: u8 = 0;
        v_val_4944_ = lean_ctor_get(v___x_4942_, 0);
        lean_inc(v_val_4944_);
        lean_dec_ref_known(v___x_4942_, 1);
        v___x_4945_ = l_String_Slice_isNat(v_val_4944_);
        lean_dec(v_val_4944_);
        return v___x_4945_;
    }
}
pub unsafe fn l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(
    mut v_s_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4947_: u8 = 0;
    let mut v_r_4948_: *mut LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_4946_);
    v_r_4948_ = lean_box((v_res_4947_) as usize);
    return v_r_4948_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Match_instInhabitedPattern_default =
        _init_l_Lean_Meta_Match_instInhabitedPattern_default();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default);
    l_Lean_Meta_Match_instInhabitedPattern = _init_l_Lean_Meta_Match_instInhabitedPattern();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern);
    l_Lean_Meta_Match_instInhabitedAlt_default = _init_l_Lean_Meta_Match_instInhabitedAlt_default();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt_default);
    l_Lean_Meta_Match_instInhabitedAlt = _init_l_Lean_Meta_Match_instInhabitedAlt();
    lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_Basic(builtin);
}

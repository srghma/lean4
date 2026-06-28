// Lean compiler output
// Module: Lean.Meta.Sorry
// Imports: Lean.Data.Lsp.Utf16 Lean.Meta.ForEachExpr Lean.Meta.InferType Lean.Util.Recognizers
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Lsp::Utf16::{
    initialize_Lean_Data_Lsp_Utf16, l_Lean_FileMap_utf8PosToLspPos,
    runtime_initialize_Lean_Data_Lsp_Utf16,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_Declaration_foldExprM___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_header};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getBoundedAppFn, l_Lean_Expr_getRevArg_x21,
    l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity, l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkForall,
};
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::Meta::ForEachExpr::{
    initialize_Lean_Meta_ForEachExpr, l_Lean_Meta_forEachExpr_x27___redArg,
    runtime_initialize_Lean_Meta_ForEachExpr,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_getLevel, runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, l_Lean_Expr_name_x3f,
    runtime_initialize_Lean_Util_Recognizers,
};
use crate::r#gen::Lean::Util::Sorry::l_Lean_Expr_isSorry;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_le, lean_nat_sub, lean_string_dec_eq};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSorry___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 111, 114, 114, 121, 65, 120, 0],
};
static mut l_Lean_Meta_mkSorry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkSorry___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__0_value) as *mut LeanObject,
        5207765522374246084 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkSorry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkSorry___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_mkSorry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_mkSorry___closed__3_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_mkSorry___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_mkSorry___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkSorry___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__3_value) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkSorry___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_mkSorry___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkSorry___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSorry___closed__6_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_mkSorry___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_mkSorry___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkSorry___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__6_value) as *mut LeanObject,
        9255189395584251158 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkSorry___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_mkSorry___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkSorry___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SorryLabelView_encode___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 115, 111, 114, 114, 121, 0],
    };
static mut l_Lean_Meta_SorryLabelView_encode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SorryLabelView_encode___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkLabeledSorry___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__1_value) as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__3_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 97, 103, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__3_value) as *mut LeanObject,
        10552689246107305202 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [85, 110, 105, 116, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value) as *mut LeanObject,
        9833841078580172006 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkLabeledSorry___closed__8_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__9_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__9_value) as *mut LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__8_value) as *mut LeanObject,
        920240211420121313 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkLabeledSorry___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__9_value) as *mut LeanObject,
        12861851057597587943 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__10_value) as *mut LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkLabeledSorry___closed__16_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [117, 110, 105, 116, 0],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__16_value) as *mut LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value) as *mut LeanObject,
        9833841078580172006 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkLabeledSorry___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__16_value) as *mut LeanObject,
        565778312915565143 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkLabeledSorry___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__17_value) as *mut LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkLabeledSorry___closed__18: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
    mut v_constName_512_: *mut LeanObject,
    mut v_skipRealize_513_: u8,
    mut v___y_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_st_ref_get(v___y_514_);
    v_env_517_ = lean_ctor_get(v___x_516_, 0);
    lean_inc_ref(v_env_517_);
    lean_dec(v___x_516_);
    v___x_518_ = l_Lean_Environment_contains(v_env_517_, v_constName_512_, v_skipRealize_513_);
    v___x_519_ = lean_box((v___x_518_) as usize);
    v___x_520_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_520_, 0, v___x_519_);
    return v___x_520_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(
    mut v_constName_521_: *mut LeanObject,
    mut v_skipRealize_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
    mut v___y_524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_525_ = (lean_unbox(v_skipRealize_522_) as u8);
    v_res_526_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
        v_constName_521_,
        v_skipRealize_boxed_525_,
        v___y_523_,
    );
    lean_dec(v___y_523_);
    return v_res_526_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(
    mut v_constName_527_: *mut LeanObject,
    mut v_skipRealize_528_: u8,
    mut v___y_529_: *mut LeanObject,
    mut v___y_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    v___x_534_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
        v_constName_527_,
        v_skipRealize_528_,
        v___y_532_,
    );
    return v___x_534_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(
    mut v_constName_535_: *mut LeanObject,
    mut v_skipRealize_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
    mut v___y_538_: *mut LeanObject,
    mut v___y_539_: *mut LeanObject,
    mut v___y_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipRealize_boxed_542_: u8 = 0;
    let mut v_res_543_: *mut LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_542_ = (lean_unbox(v_skipRealize_536_) as u8);
    v_res_543_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(
        v_constName_535_,
        v_skipRealize_boxed_542_,
        v___y_537_,
        v___y_538_,
        v___y_539_,
        v___y_540_,
    );
    lean_dec(v___y_540_);
    lean_dec_ref(v___y_539_);
    lean_dec(v___y_538_);
    lean_dec_ref(v___y_537_);
    return v_res_543_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = lean_box(0);
    v___x_545_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_546_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_546_, 0, v___x_545_);
    lean_ctor_set(v___x_546_, 1, v___x_544_);
    return v___x_546_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg()
-> *mut LeanObject {
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v___x_548_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0);
    v___x_549_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_549_, 0, v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(
    mut v___y_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_551_: *mut LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
    return v_res_551_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(
    mut v_00_u03b1_552_: *mut LeanObject,
    mut v___y_553_: *mut LeanObject,
    mut v___y_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
    return v___x_558_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(
    mut v_00_u03b1_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
    mut v___y_562_: *mut LeanObject,
    mut v___y_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(
        v_00_u03b1_559_,
        v___y_560_,
        v___y_561_,
        v___y_562_,
        v___y_563_,
    );
    lean_dec(v___y_563_);
    lean_dec_ref(v___y_562_);
    lean_dec(v___y_561_);
    lean_dec_ref(v___y_560_);
    return v_res_565_;
}
pub unsafe fn _init_l_Lean_Meta_mkSorry___closed__5() -> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = lean_box(0);
    v___x_575_ = l_Lean_Meta_mkSorry___closed__4;
    v___x_576_ = l_Lean_mkConst(v___x_575_, v___x_574_);
    return v___x_576_;
}
pub unsafe fn _init_l_Lean_Meta_mkSorry___closed__8() -> *mut LeanObject {
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_581_ = lean_box(0);
    v___x_582_ = l_Lean_Meta_mkSorry___closed__7;
    v___x_583_ = l_Lean_mkConst(v___x_582_, v___x_581_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Meta_mkSorry(
    mut v_type_584_: *mut LeanObject,
    mut v_synthetic_585_: u8,
    mut v_a_586_: *mut LeanObject,
    mut v_a_587_: *mut LeanObject,
    mut v_a_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_616_: u8 = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: u8 = 0;
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_596_ = l_Lean_Meta_mkSorry___closed__1;
                v___x_617_ = 1;
                v___x_618_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
                    v___x_596_, v___x_617_, v_a_589_,
                );
                v_a_619_ = lean_ctor_get(v___x_618_, 0);
                lean_inc(v_a_619_);
                lean_dec_ref(v___x_618_);
                v___x_620_ = (lean_unbox(v_a_619_) as u8);
                lean_dec(v_a_619_);
                if v___x_620_ == 0 {
                    lean_dec_ref(v_type_584_);
                    v___x_621_ =
                        l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
                    v_a_622_ = lean_ctor_get(v___x_621_, 0);
                    v_isSharedCheck_629_ = (!lean_is_exclusive(v___x_621_)) as u8;
                    if v_isSharedCheck_629_ == 0 {
                        v___x_624_ = v___x_621_;
                        v_isShared_625_ = v_isSharedCheck_629_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_622_);
                        lean_dec(v___x_621_);
                        v___x_624_ = lean_box(0);
                        v_isShared_625_ = v_isSharedCheck_629_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_598_ = v_a_586_;
                    v___y_599_ = v_a_587_;
                    v___y_600_ = v_a_588_;
                    v___y_601_ = v_a_589_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v___y_593_);
                v___x_594_ = l_Lean_mkAppB(v___y_592_, v_type_584_, v___y_593_);
                v___x_595_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_595_, 0, v___x_594_);
                return v___x_595_;
            }
            2 => {
                lean_inc_ref(v_type_584_);
                v___x_602_ = l_Lean_Meta_getLevel(
                    v_type_584_,
                    v___y_598_,
                    v___y_599_,
                    v___y_600_,
                    v___y_601_,
                );
                if lean_obj_tag(v___x_602_) == 0 {
                    v_a_603_ = lean_ctor_get(v___x_602_, 0);
                    lean_inc(v_a_603_);
                    lean_dec_ref_known(v___x_602_, 1);
                    v___x_604_ = lean_box(0);
                    v___x_605_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_605_, 0, v_a_603_);
                    lean_ctor_set(v___x_605_, 1, v___x_604_);
                    v___x_606_ = l_Lean_mkConst(v___x_596_, v___x_605_);
                    if v_synthetic_585_ == 0 {
                        v___x_607_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__5_once),
                            _init_l_Lean_Meta_mkSorry___closed__5,
                        );
                        v___y_592_ = v___x_606_;
                        v___y_593_ = v___x_607_;
                        state = 1;
                        continue;
                    } else {
                        v___x_608_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__8),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__8_once),
                            _init_l_Lean_Meta_mkSorry___closed__8,
                        );
                        v___y_592_ = v___x_606_;
                        v___y_593_ = v___x_608_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_584_);
                    v_a_609_ = lean_ctor_get(v___x_602_, 0);
                    v_isSharedCheck_616_ = (!lean_is_exclusive(v___x_602_)) as u8;
                    if v_isSharedCheck_616_ == 0 {
                        v___x_611_ = v___x_602_;
                        v_isShared_612_ = v_isSharedCheck_616_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_609_);
                        lean_dec(v___x_602_);
                        v___x_611_ = lean_box(0);
                        v_isShared_612_ = v_isSharedCheck_616_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_612_ == 0 {
                    v___x_614_ = v___x_611_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
                    v___x_614_ = v_reuseFailAlloc_615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_614_;
            }
            5 => {
                if v_isShared_625_ == 0 {
                    v___x_627_ = v___x_624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
                    v___x_627_ = v_reuseFailAlloc_628_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSorry___boxed(
    mut v_type_630_: *mut LeanObject,
    mut v_synthetic_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
    mut v_a_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_637_: u8 = 0;
    let mut v_res_638_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_637_ = (lean_unbox(v_synthetic_631_) as u8);
    v_res_638_ = l_Lean_Meta_mkSorry(
        v_type_630_,
        v_synthetic_boxed_637_,
        v_a_632_,
        v_a_633_,
        v_a_634_,
        v_a_635_,
    );
    lean_dec(v_a_635_);
    lean_dec_ref(v_a_634_);
    lean_dec(v_a_633_);
    lean_dec_ref(v_a_632_);
    return v_res_638_;
}
pub unsafe fn l_Lean_Meta_SorryLabelView_encode(
    mut v_view_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
    mut v_a_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_view_640_) == 1 {
                    v_val_649_ = lean_ctor_get(v_view_640_, 0);
                    lean_inc(v_val_649_);
                    lean_dec_ref_known(v_view_640_, 1);
                    v_range_650_ = lean_ctor_get(v_val_649_, 1);
                    lean_inc_ref(v_range_650_);
                    v_pos_651_ = lean_ctor_get(v_range_650_, 0);
                    lean_inc_ref(v_pos_651_);
                    v_endPos_652_ = lean_ctor_get(v_range_650_, 2);
                    lean_inc_ref(v_endPos_652_);
                    v_module_653_ = lean_ctor_get(v_val_649_, 0);
                    lean_inc(v_module_653_);
                    lean_dec(v_val_649_);
                    v_charUtf16_654_ = lean_ctor_get(v_range_650_, 1);
                    lean_inc(v_charUtf16_654_);
                    v_endCharUtf16_655_ = lean_ctor_get(v_range_650_, 3);
                    lean_inc(v_endCharUtf16_655_);
                    lean_dec_ref(v_range_650_);
                    v_line_656_ = lean_ctor_get(v_pos_651_, 0);
                    lean_inc(v_line_656_);
                    v_column_657_ = lean_ctor_get(v_pos_651_, 1);
                    lean_inc(v_column_657_);
                    lean_dec_ref(v_pos_651_);
                    v_line_658_ = lean_ctor_get(v_endPos_652_, 0);
                    lean_inc(v_line_658_);
                    v_column_659_ = lean_ctor_get(v_endPos_652_, 1);
                    lean_inc(v_column_659_);
                    lean_dec_ref(v_endPos_652_);
                    v___x_660_ = l_Lean_Name_num___override(v_module_653_, v_line_656_);
                    v___x_661_ = l_Lean_Name_num___override(v___x_660_, v_column_657_);
                    v___x_662_ = l_Lean_Name_num___override(v___x_661_, v_line_658_);
                    v___x_663_ = l_Lean_Name_num___override(v___x_662_, v_column_659_);
                    v___x_664_ = l_Lean_Name_num___override(v___x_663_, v_charUtf16_654_);
                    v___x_665_ = l_Lean_Name_num___override(v___x_664_, v_endCharUtf16_655_);
                    v___y_645_ = v___x_665_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_view_640_);
                    v___x_666_ = lean_box(0);
                    v___y_645_ = v___x_666_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_646_ = l_Lean_Meta_SorryLabelView_encode___closed__0;
                v___x_647_ = l_Lean_Name_str___override(v___y_645_, v___x_646_);
                v___x_648_ = l_Lean_Core_mkFreshUserName(v___x_647_, v_a_641_, v_a_642_);
                return v___x_648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SorryLabelView_encode___boxed(
    mut v_view_667_: *mut LeanObject,
    mut v_a_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_671_: *mut LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Lean_Meta_SorryLabelView_encode(v_view_667_, v_a_668_, v_a_669_);
    lean_dec(v_a_669_);
    lean_dec_ref(v_a_668_);
    return v_res_671_;
}
pub unsafe fn l_Lean_Meta_SorryLabelView_decode_x3f(
    mut v_name_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_673_: u8 = 0;
    v___x_673_ = l_Lean_Name_hasMacroScopes(v_name_672_);
    if v___x_673_ == 0 {
        let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_name_672_);
        v___x_674_ = lean_box(0);
        return v___x_674_;
    } else {
        let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
        v___x_675_ = lean_erase_macro_scopes(v_name_672_);
        if lean_obj_tag(v___x_675_) == 1 {
            let mut v_pre_676_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_677_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_679_: u8 = 0;
            v_pre_676_ = lean_ctor_get(v___x_675_, 0);
            lean_inc(v_pre_676_);
            v_str_677_ = lean_ctor_get(v___x_675_, 1);
            lean_inc_ref(v_str_677_);
            lean_dec_ref_known(v___x_675_, 2);
            v___x_678_ = l_Lean_Meta_SorryLabelView_encode___closed__0;
            v___x_679_ = lean_string_dec_eq(v_str_677_, v___x_678_);
            lean_dec_ref(v_str_677_);
            if v___x_679_ == 0 {
                let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_pre_676_);
                v___x_680_ = lean_box(0);
                return v___x_680_;
            } else {
                if lean_obj_tag(v_pre_676_) == 2 {
                    let mut v_pre_681_: *mut LeanObject = core::ptr::null_mut();
                    v_pre_681_ = lean_ctor_get(v_pre_676_, 0);
                    lean_inc(v_pre_681_);
                    if lean_obj_tag(v_pre_681_) == 2 {
                        let mut v_pre_682_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_682_ = lean_ctor_get(v_pre_681_, 0);
                        lean_inc(v_pre_682_);
                        if lean_obj_tag(v_pre_682_) == 2 {
                            let mut v_pre_683_: *mut LeanObject = core::ptr::null_mut();
                            v_pre_683_ = lean_ctor_get(v_pre_682_, 0);
                            lean_inc(v_pre_683_);
                            if lean_obj_tag(v_pre_683_) == 2 {
                                let mut v_pre_684_: *mut LeanObject = core::ptr::null_mut();
                                v_pre_684_ = lean_ctor_get(v_pre_683_, 0);
                                lean_inc(v_pre_684_);
                                if lean_obj_tag(v_pre_684_) == 2 {
                                    let mut v_pre_685_: *mut LeanObject = core::ptr::null_mut();
                                    v_pre_685_ = lean_ctor_get(v_pre_684_, 0);
                                    lean_inc(v_pre_685_);
                                    if lean_obj_tag(v_pre_685_) == 2 {
                                        let mut v_i_686_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_i_687_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_i_688_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_i_689_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_i_690_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_pre_691_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v_i_692_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
                                        v_i_686_ = lean_ctor_get(v_pre_676_, 1);
                                        lean_inc(v_i_686_);
                                        lean_dec_ref_known(v_pre_676_, 2);
                                        v_i_687_ = lean_ctor_get(v_pre_681_, 1);
                                        lean_inc(v_i_687_);
                                        lean_dec_ref_known(v_pre_681_, 2);
                                        v_i_688_ = lean_ctor_get(v_pre_682_, 1);
                                        lean_inc(v_i_688_);
                                        lean_dec_ref_known(v_pre_682_, 2);
                                        v_i_689_ = lean_ctor_get(v_pre_683_, 1);
                                        lean_inc(v_i_689_);
                                        lean_dec_ref_known(v_pre_683_, 2);
                                        v_i_690_ = lean_ctor_get(v_pre_684_, 1);
                                        lean_inc(v_i_690_);
                                        lean_dec_ref_known(v_pre_684_, 2);
                                        v_pre_691_ = lean_ctor_get(v_pre_685_, 0);
                                        lean_inc(v_pre_691_);
                                        v_i_692_ = lean_ctor_get(v_pre_685_, 1);
                                        lean_inc(v_i_692_);
                                        lean_dec_ref_known(v_pre_685_, 2);
                                        v___x_693_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_693_, 0, v_i_692_);
                                        lean_ctor_set(v___x_693_, 1, v_i_690_);
                                        v___x_694_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_694_, 0, v_i_689_);
                                        lean_ctor_set(v___x_694_, 1, v_i_688_);
                                        v___x_695_ = lean_alloc_ctor(0, 4, (0) as u32);
                                        lean_ctor_set(v___x_695_, 0, v___x_693_);
                                        lean_ctor_set(v___x_695_, 1, v_i_687_);
                                        lean_ctor_set(v___x_695_, 2, v___x_694_);
                                        lean_ctor_set(v___x_695_, 3, v_i_686_);
                                        v___x_696_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_696_, 0, v_pre_691_);
                                        lean_ctor_set(v___x_696_, 1, v___x_695_);
                                        v___x_697_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_697_, 0, v___x_696_);
                                        v___x_698_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_698_, 0, v___x_697_);
                                        return v___x_698_;
                                    } else {
                                        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
                                        lean_dec(v_pre_685_);
                                        lean_dec_ref_known(v_pre_684_, 2);
                                        lean_dec_ref_known(v_pre_683_, 2);
                                        lean_dec_ref_known(v_pre_682_, 2);
                                        lean_dec_ref_known(v_pre_681_, 2);
                                        lean_dec_ref_known(v_pre_676_, 2);
                                        v___x_699_ = lean_box(0);
                                        return v___x_699_;
                                    }
                                } else {
                                    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v_pre_684_);
                                    lean_dec_ref_known(v_pre_683_, 2);
                                    lean_dec_ref_known(v_pre_682_, 2);
                                    lean_dec_ref_known(v_pre_681_, 2);
                                    lean_dec_ref_known(v_pre_676_, 2);
                                    v___x_700_ = lean_box(0);
                                    return v___x_700_;
                                }
                            } else {
                                let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec(v_pre_683_);
                                lean_dec_ref_known(v_pre_682_, 2);
                                lean_dec_ref_known(v_pre_681_, 2);
                                lean_dec_ref_known(v_pre_676_, 2);
                                v___x_701_ = lean_box(0);
                                return v___x_701_;
                            }
                        } else {
                            let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v_pre_681_, 2);
                            lean_dec(v_pre_682_);
                            lean_dec_ref_known(v_pre_676_, 2);
                            v___x_702_ = lean_box(0);
                            return v___x_702_;
                        }
                    } else {
                        let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v_pre_676_, 2);
                        lean_dec(v_pre_681_);
                        v___x_703_ = lean_box(0);
                        return v___x_703_;
                    }
                } else {
                    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_pre_676_);
                    v___x_704_ = lean_box(0);
                    return v___x_704_;
                }
            }
        } else {
            let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_675_);
            v___x_705_ = lean_box(0);
            return v___x_705_;
        }
    }
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(
    mut v___y_706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = lean_st_ref_get(v___y_706_);
    v_env_709_ = lean_ctor_get(v___x_708_, 0);
    lean_inc_ref(v_env_709_);
    lean_dec(v___x_708_);
    v___x_710_ = l_Lean_Environment_header(v_env_709_);
    lean_dec_ref(v_env_709_);
    v_mainModule_711_ = lean_ctor_get(v___x_710_, 0);
    lean_inc(v_mainModule_711_);
    lean_dec_ref(v___x_710_);
    v___x_712_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_712_, 0, v_mainModule_711_);
    return v___x_712_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(
    mut v___y_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_715_: *mut LeanObject = core::ptr::null_mut();
    v_res_715_ =
        l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_713_);
    lean_dec(v___y_713_);
    return v_res_715_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(
    mut v___y_716_: *mut LeanObject,
    mut v___y_717_: *mut LeanObject,
    mut v___y_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ =
        l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_719_);
    return v___x_721_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
    mut v___y_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_727_: *mut LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(
        v___y_722_, v___y_723_, v___y_724_, v___y_725_,
    );
    lean_dec(v___y_725_);
    lean_dec_ref(v___y_724_);
    lean_dec(v___y_723_);
    lean_dec_ref(v___y_722_);
    return v_res_727_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__7() -> *mut LeanObject {
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    v___x_739_ = lean_box(0);
    v___x_740_ = l_Lean_Meta_mkLabeledSorry___closed__6;
    v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
    return v___x_741_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__11() -> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_box(0);
    v___x_748_ = l_Lean_Level_succ___override(v___x_747_);
    return v___x_748_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__12() -> *mut LeanObject {
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_749_ = lean_box(0);
    v___x_750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__11,
    );
    v___x_751_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_751_, 0, v___x_750_);
    lean_ctor_set(v___x_751_, 1, v___x_749_);
    return v___x_751_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__13() -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__12_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__12,
    );
    v___x_753_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__11,
    );
    v___x_754_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_754_, 0, v___x_753_);
    lean_ctor_set(v___x_754_, 1, v___x_752_);
    return v___x_754_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__14() -> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__13_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__13,
    );
    v___x_756_ = l_Lean_Meta_mkLabeledSorry___closed__10;
    v___x_757_ = l_Lean_mkConst(v___x_756_, v___x_755_);
    return v___x_757_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__15() -> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_box(0);
    v___x_759_ = l_Lean_Meta_mkLabeledSorry___closed__2;
    v___x_760_ = l_Lean_mkConst(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__18() -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_box(0);
    v___x_766_ = l_Lean_Meta_mkLabeledSorry___closed__17;
    v___x_767_ = l_Lean_mkConst(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn l_Lean_Meta_mkLabeledSorry(
    mut v_type_768_: *mut LeanObject,
    mut v_synthetic_769_: u8,
    mut v_unique_770_: u8,
    mut v_a_771_: *mut LeanObject,
    mut v_a_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tag_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_791_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_816_: u8 = 0;
    let mut v___y_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_828_: u8 = 0;
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v___y_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_character_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_character_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut v_reuseFailAlloc_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_unused_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_776_ = l_Lean_Meta_mkLabeledSorry___closed__2;
                v___x_879_ = 1;
                v___x_880_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
                    v___x_776_, v___x_879_, v_a_774_,
                );
                v_a_881_ = lean_ctor_get(v___x_880_, 0);
                lean_inc(v_a_881_);
                lean_dec_ref(v___x_880_);
                v___x_882_ = (lean_unbox(v_a_881_) as u8);
                lean_dec(v_a_881_);
                if v___x_882_ == 0 {
                    lean_dec_ref(v_type_768_);
                    v___x_883_ =
                        l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
                    v_a_884_ = lean_ctor_get(v___x_883_, 0);
                    v_isSharedCheck_891_ = (!lean_is_exclusive(v___x_883_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_886_ = v___x_883_;
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_884_);
                        lean_dec(v___x_883_);
                        v___x_886_ = lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___y_834_ = v_a_771_;
                    v___y_835_ = v_a_772_;
                    v___y_836_ = v_a_773_;
                    v___y_837_ = v_a_774_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                if v_unique_770_ == 0 {
                    v___x_783_ = l_Lean_Meta_mkLabeledSorry___closed__4;
                    v___x_784_ = 0;
                    v___x_785_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__7_once),
                        _init_l_Lean_Meta_mkLabeledSorry___closed__7,
                    );
                    v___x_786_ = l_Lean_mkForall(v___x_783_, v___x_784_, v___x_785_, v_type_768_);
                    v___x_787_ = l_Lean_Meta_mkSorry(
                        v___x_786_,
                        v_synthetic_769_,
                        v___y_779_,
                        v___y_780_,
                        v___y_781_,
                        v___y_782_,
                    );
                    if lean_obj_tag(v___x_787_) == 0 {
                        v_a_788_ = lean_ctor_get(v___x_787_, 0);
                        v_isSharedCheck_801_ = (!lean_is_exclusive(v___x_787_)) as u8;
                        if v_isSharedCheck_801_ == 0 {
                            v___x_790_ = v___x_787_;
                            v_isShared_791_ = v_isSharedCheck_801_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_788_);
                            lean_dec(v___x_787_);
                            v___x_790_ = lean_box(0);
                            v_isShared_791_ = v_isSharedCheck_801_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_tag_778_);
                        return v___x_787_;
                    }
                } else {
                    v___x_802_ = l_Lean_Meta_mkLabeledSorry___closed__4;
                    v___x_803_ = 0;
                    v___x_804_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15_once),
                        _init_l_Lean_Meta_mkLabeledSorry___closed__15,
                    );
                    v___x_805_ = l_Lean_mkForall(v___x_802_, v___x_803_, v___x_804_, v_type_768_);
                    v___x_806_ = l_Lean_Meta_mkSorry(
                        v___x_805_,
                        v_synthetic_769_,
                        v___y_779_,
                        v___y_780_,
                        v___y_781_,
                        v___y_782_,
                    );
                    if lean_obj_tag(v___x_806_) == 0 {
                        v_a_807_ = lean_ctor_get(v___x_806_, 0);
                        v_isSharedCheck_816_ = (!lean_is_exclusive(v___x_806_)) as u8;
                        if v_isSharedCheck_816_ == 0 {
                            v___x_809_ = v___x_806_;
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_807_);
                            lean_dec(v___x_806_);
                            v___x_809_ = lean_box(0);
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_tag_778_);
                        return v___x_806_;
                    }
                }
            }
            2 => {
                v___x_792_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__14_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__14,
                );
                v___x_793_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__15,
                );
                v___x_794_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__18_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__18,
                );
                v___x_795_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_778_);
                v___x_796_ =
                    l_Lean_mkApp4(v___x_792_, v___x_785_, v___x_793_, v___x_794_, v___x_795_);
                v___x_797_ = l_Lean_Expr_app___override(v_a_788_, v___x_796_);
                if v_isShared_791_ == 0 {
                    lean_ctor_set(v___x_790_, 0, v___x_797_);
                    v___x_799_ = v___x_790_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                    v___x_799_ = v_reuseFailAlloc_800_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_799_;
            }
            4 => {
                v___x_811_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_778_);
                v___x_812_ = l_Lean_Expr_app___override(v_a_807_, v___x_811_);
                if v_isShared_810_ == 0 {
                    lean_ctor_set(v___x_809_, 0, v___x_812_);
                    v___x_814_ = v___x_809_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
                    v___x_814_ = v_reuseFailAlloc_815_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_814_;
            }
            6 => {
                v___x_822_ = lean_box(0);
                v___x_823_ = l_Lean_Meta_SorryLabelView_encode(v___x_822_, v___y_820_, v___y_821_);
                if lean_obj_tag(v___x_823_) == 0 {
                    v_a_824_ = lean_ctor_get(v___x_823_, 0);
                    lean_inc(v_a_824_);
                    lean_dec_ref_known(v___x_823_, 1);
                    v_tag_778_ = v_a_824_;
                    v___y_779_ = v___y_818_;
                    v___y_780_ = v___y_819_;
                    v___y_781_ = v___y_820_;
                    v___y_782_ = v___y_821_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_type_768_);
                    v_a_825_ = lean_ctor_get(v___x_823_, 0);
                    v_isSharedCheck_832_ = (!lean_is_exclusive(v___x_823_)) as u8;
                    if v_isSharedCheck_832_ == 0 {
                        v___x_827_ = v___x_823_;
                        v_isShared_828_ = v_isSharedCheck_832_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_825_);
                        lean_dec(v___x_823_);
                        v___x_827_ = lean_box(0);
                        v_isShared_828_ = v_isSharedCheck_832_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_828_ == 0 {
                    v___x_830_ = v___x_827_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
                    v___x_830_ = v_reuseFailAlloc_831_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_830_;
            }
            9 => {
                v_fileMap_838_ = lean_ctor_get(v___y_836_, 1);
                v_ref_839_ = lean_ctor_get(v___y_836_, 5);
                v___x_840_ = 0;
                v___x_841_ = l_Lean_Syntax_getPos_x3f(v_ref_839_, v___x_840_);
                if lean_obj_tag(v___x_841_) == 1 {
                    v_val_842_ = lean_ctor_get(v___x_841_, 0);
                    lean_inc(v_val_842_);
                    lean_dec_ref_known(v___x_841_, 1);
                    v___x_843_ = l_Lean_Syntax_getTailPos_x3f(v_ref_839_, v___x_840_);
                    if lean_obj_tag(v___x_843_) == 1 {
                        v_val_844_ = lean_ctor_get(v___x_843_, 0);
                        v_isSharedCheck_878_ = (!lean_is_exclusive(v___x_843_)) as u8;
                        if v_isSharedCheck_878_ == 0 {
                            v___x_846_ = v___x_843_;
                            v_isShared_847_ = v_isSharedCheck_878_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_val_844_);
                            lean_dec(v___x_843_);
                            v___x_846_ = lean_box(0);
                            v_isShared_847_ = v_isSharedCheck_878_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_843_);
                        lean_dec(v_val_842_);
                        v___y_818_ = v___y_834_;
                        v___y_819_ = v___y_835_;
                        v___y_820_ = v___y_836_;
                        v___y_821_ = v___y_837_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_841_);
                    v___y_818_ = v___y_834_;
                    v___y_819_ = v___y_835_;
                    v___y_820_ = v___y_836_;
                    v___y_821_ = v___y_837_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_848_ =
                    l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(
                        v___y_837_,
                    );
                v_a_849_ = lean_ctor_get(v___x_848_, 0);
                lean_inc(v_a_849_);
                lean_dec_ref(v___x_848_);
                lean_inc_ref_n(v_fileMap_838_, 4);
                v___x_850_ = l_Lean_FileMap_toPosition(v_fileMap_838_, v_val_842_);
                v___x_851_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_838_, v_val_842_);
                lean_dec(v_val_842_);
                v_character_852_ = lean_ctor_get(v___x_851_, 1);
                lean_inc(v_character_852_);
                lean_dec_ref(v___x_851_);
                v___x_853_ = l_Lean_FileMap_toPosition(v_fileMap_838_, v_val_844_);
                v___x_854_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_838_, v_val_844_);
                lean_dec(v_val_844_);
                v_character_855_ = lean_ctor_get(v___x_854_, 1);
                v_isSharedCheck_876_ = (!lean_is_exclusive(v___x_854_)) as u8;
                if v_isSharedCheck_876_ == 0 {
                    v_unused_877_ = lean_ctor_get(v___x_854_, 0);
                    lean_dec(v_unused_877_);
                    v___x_857_ = v___x_854_;
                    v_isShared_858_ = v_isSharedCheck_876_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_character_855_);
                    lean_dec(v___x_854_);
                    v___x_857_ = lean_box(0);
                    v_isShared_858_ = v_isSharedCheck_876_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_859_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_859_, 0, v___x_850_);
                lean_ctor_set(v___x_859_, 1, v_character_852_);
                lean_ctor_set(v___x_859_, 2, v___x_853_);
                lean_ctor_set(v___x_859_, 3, v_character_855_);
                if v_isShared_858_ == 0 {
                    lean_ctor_set(v___x_857_, 1, v___x_859_);
                    lean_ctor_set(v___x_857_, 0, v_a_849_);
                    v___x_861_ = v___x_857_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_849_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_859_);
                    v___x_861_ = v_reuseFailAlloc_875_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_847_ == 0 {
                    lean_ctor_set(v___x_846_, 0, v___x_861_);
                    v___x_863_ = v___x_846_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_861_);
                    v___x_863_ = v_reuseFailAlloc_874_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_864_ = l_Lean_Meta_SorryLabelView_encode(v___x_863_, v___y_836_, v___y_837_);
                if lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = lean_ctor_get(v___x_864_, 0);
                    lean_inc(v_a_865_);
                    lean_dec_ref_known(v___x_864_, 1);
                    v_tag_778_ = v_a_865_;
                    v___y_779_ = v___y_834_;
                    v___y_780_ = v___y_835_;
                    v___y_781_ = v___y_836_;
                    v___y_782_ = v___y_837_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_type_768_);
                    v_a_866_ = lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_873_ = (!lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_873_ == 0 {
                        v___x_868_ = v___x_864_;
                        v_isShared_869_ = v_isSharedCheck_873_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_866_);
                        lean_dec(v___x_864_);
                        v___x_868_ = lean_box(0);
                        v_isShared_869_ = v_isSharedCheck_873_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_869_ == 0 {
                    v___x_871_ = v___x_868_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
                    v___x_871_ = v_reuseFailAlloc_872_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_871_;
            }
            16 => {
                if v_isShared_887_ == 0 {
                    v___x_889_ = v___x_886_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkLabeledSorry___boxed(
    mut v_type_892_: *mut LeanObject,
    mut v_synthetic_893_: *mut LeanObject,
    mut v_unique_894_: *mut LeanObject,
    mut v_a_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_900_: u8 = 0;
    let mut v_unique_boxed_901_: u8 = 0;
    let mut v_res_902_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_900_ = (lean_unbox(v_synthetic_893_) as u8);
    v_unique_boxed_901_ = (lean_unbox(v_unique_894_) as u8);
    v_res_902_ = l_Lean_Meta_mkLabeledSorry(
        v_type_892_,
        v_synthetic_boxed_900_,
        v_unique_boxed_901_,
        v_a_895_,
        v_a_896_,
        v_a_897_,
        v_a_898_,
    );
    lean_dec(v_a_898_);
    lean_dec_ref(v_a_897_);
    lean_dec(v_a_896_);
    lean_dec_ref(v_a_895_);
    return v_res_902_;
}
pub unsafe fn l_Lean_Meta_isLabeledSorry_x3f(mut v_e_903_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    v___x_904_ = l_Lean_Meta_mkSorry___closed__1;
    v___x_905_ = l_Lean_Expr_isAppOf(v_e_903_, v___x_904_);
    if v___x_905_ == 0 {
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        v___x_906_ = lean_box(0);
        return v___x_906_;
    } else {
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: u8 = 0;
        v___x_907_ = l_Lean_Expr_getAppNumArgs(v_e_903_);
        v___x_908_ = lean_unsigned_to_nat(3);
        v___x_909_ = lean_nat_dec_le(v___x_908_, v___x_907_);
        if v___x_909_ == 0 {
            let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_907_);
            v___x_910_ = lean_box(0);
            return v___x_910_;
        } else {
            let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
            v___x_911_ = lean_unsigned_to_nat(2);
            v___x_912_ = lean_nat_sub(v___x_907_, v___x_911_);
            lean_dec(v___x_907_);
            v___x_913_ = lean_unsigned_to_nat(1);
            v___x_914_ = lean_nat_sub(v___x_912_, v___x_913_);
            lean_dec(v___x_912_);
            v___x_915_ = l_Lean_Expr_getRevArg_x21(v_e_903_, v___x_914_);
            lean_inc_ref(v___x_915_);
            v___x_916_ = l_Lean_Expr_name_x3f(v___x_915_);
            if lean_obj_tag(v___x_916_) == 1 {
                let mut v_val_917_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_915_);
                v_val_917_ = lean_ctor_get(v___x_916_, 0);
                lean_inc(v_val_917_);
                lean_dec_ref_known(v___x_916_, 1);
                v___x_918_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_917_);
                return v___x_918_;
            } else {
                let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_921_: u8 = 0;
                lean_dec(v___x_916_);
                v___x_919_ = l_Lean_Meta_mkLabeledSorry___closed__10;
                v___x_920_ = lean_unsigned_to_nat(4);
                v___x_921_ = l_Lean_Expr_isAppOfArity(v___x_915_, v___x_919_, v___x_920_);
                if v___x_921_ == 0 {
                    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___x_915_);
                    v___x_922_ = lean_box(0);
                    return v___x_922_;
                } else {
                    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_927_: u8 = 0;
                    v___x_923_ = l_Lean_Expr_appFn_x21(v___x_915_);
                    v___x_924_ = l_Lean_Expr_appArg_x21(v___x_923_);
                    lean_dec_ref(v___x_923_);
                    v___x_925_ = l_Lean_Meta_mkLabeledSorry___closed__17;
                    v___x_926_ = lean_unsigned_to_nat(0);
                    v___x_927_ = l_Lean_Expr_isAppOfArity(v___x_924_, v___x_925_, v___x_926_);
                    lean_dec_ref(v___x_924_);
                    if v___x_927_ == 0 {
                        let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref(v___x_915_);
                        v___x_928_ = lean_box(0);
                        return v___x_928_;
                    } else {
                        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
                        v___x_929_ = l_Lean_Expr_appArg_x21(v___x_915_);
                        lean_dec_ref(v___x_915_);
                        v___x_930_ = l_Lean_Expr_name_x3f(v___x_929_);
                        if lean_obj_tag(v___x_930_) == 0 {
                            let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
                            v___x_931_ = lean_box(0);
                            return v___x_931_;
                        } else {
                            let mut v_val_932_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
                            v_val_932_ = lean_ctor_get(v___x_930_, 0);
                            lean_inc(v_val_932_);
                            lean_dec_ref_known(v___x_930_, 1);
                            v___x_933_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_932_);
                            return v___x_933_;
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_isLabeledSorry_x3f___boxed(
    mut v_e_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_934_);
    lean_dec_ref(v_e_934_);
    return v_res_935_;
}
pub unsafe fn l_Lean_Expr_getSorry_x3f(mut v_e_936_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_unused_957_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_943_ = l_Lean_Expr_isSorry(v_e_936_);
                if v___x_943_ == 0 {
                    v___x_944_ = lean_box(0);
                    return v___x_944_;
                } else {
                    v___x_945_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_936_);
                    if lean_obj_tag(v___x_945_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_956_ = (!lean_is_exclusive(v___x_945_)) as u8;
                        if v_isSharedCheck_956_ == 0 {
                            v_unused_957_ = lean_ctor_get(v___x_945_, 0);
                            lean_dec(v_unused_957_);
                            v___x_947_ = v___x_945_;
                            v_isShared_948_ = v_isSharedCheck_956_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_945_);
                            v___x_947_ = lean_box(0);
                            v_isShared_948_ = v_isSharedCheck_956_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_938_ = l_Lean_Expr_getAppNumArgs(v_e_936_);
                v___x_939_ = lean_unsigned_to_nat(2);
                v___x_940_ = lean_nat_sub(v___x_938_, v___x_939_);
                lean_dec(v___x_938_);
                v___x_941_ = l_Lean_Expr_getBoundedAppFn(v___x_940_, v_e_936_);
                v___x_942_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_942_, 0, v___x_941_);
                return v___x_942_;
            }
            2 => {
                if v___x_943_ == 0 {
                    lean_del_object(v___x_947_);
                    state = 1;
                    continue;
                } else {
                    v___x_949_ = l_Lean_Expr_getAppNumArgs(v_e_936_);
                    v___x_950_ = lean_unsigned_to_nat(3);
                    v___x_951_ = lean_nat_sub(v___x_949_, v___x_950_);
                    lean_dec(v___x_949_);
                    v___x_952_ = l_Lean_Expr_getBoundedAppFn(v___x_951_, v_e_936_);
                    if v_isShared_948_ == 0 {
                        lean_ctor_set(v___x_947_, 0, v___x_952_);
                        v___x_954_ = v___x_947_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
                        v___x_954_ = v_reuseFailAlloc_955_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_getSorry_x3f___boxed(mut v_e_958_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_959_: *mut LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lean_Expr_getSorry_x3f(v_e_958_);
    lean_dec_ref(v_e_958_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__0(
    mut v_toPure_960_: *mut LeanObject,
    mut v_____r_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_962_ = 0;
    v___x_963_ = lean_box((v___x_962_) as usize);
    v___x_964_ = lean_apply_2(v_toPure_960_, lean_box(0), v___x_963_);
    return v___x_964_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__1(
    mut v_fn_965_: *mut LeanObject,
    mut v_toBind_966_: *mut LeanObject,
    mut v___f_967_: *mut LeanObject,
    mut v_toPure_968_: *mut LeanObject,
    mut v_e_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_Expr_getSorry_x3f(v_e_969_);
    if lean_obj_tag(v___x_970_) == 1 {
        let mut v_val_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_968_);
        v_val_971_ = lean_ctor_get(v___x_970_, 0);
        lean_inc(v_val_971_);
        lean_dec_ref_known(v___x_970_, 1);
        v___x_972_ = lean_apply_1(v_fn_965_, v_val_971_);
        v___x_973_ = lean_apply_4(
            v_toBind_966_,
            lean_box(0),
            lean_box(0),
            v___x_972_,
            v___f_967_,
        );
        return v___x_973_;
    } else {
        let mut v___x_974_: u8 = 0;
        let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_970_);
        lean_dec(v___f_967_);
        lean_dec(v_toBind_966_);
        lean_dec(v_fn_965_);
        v___x_974_ = 1;
        v___x_975_ = lean_box((v___x_974_) as usize);
        v___x_976_ = lean_apply_2(v_toPure_968_, lean_box(0), v___x_975_);
        return v___x_976_;
    }
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(
    mut v_fn_977_: *mut LeanObject,
    mut v_toBind_978_: *mut LeanObject,
    mut v___f_979_: *mut LeanObject,
    mut v_toPure_980_: *mut LeanObject,
    mut v_e_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_Meta_forEachSorryM___redArg___lam__1(
        v_fn_977_,
        v_toBind_978_,
        v___f_979_,
        v_toPure_980_,
        v_e_981_,
    );
    lean_dec_ref(v_e_981_);
    return v_res_982_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg(
    mut v_inst_983_: *mut LeanObject,
    mut v_inst_984_: *mut LeanObject,
    mut v_inst_985_: *mut LeanObject,
    mut v_input_986_: *mut LeanObject,
    mut v_fn_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_988_ = lean_ctor_get(v_inst_983_, 0);
    v_toBind_989_ = lean_ctor_get(v_inst_983_, 1);
    v_toPure_990_ = lean_ctor_get(v_toApplicative_988_, 1);
    lean_inc_n(v_toPure_990_, 2);
    v___f_991_ = lean_alloc_closure(
        l_Lean_Meta_forEachSorryM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_991_, 0, v_toPure_990_);
    lean_inc(v_toBind_989_);
    v___f_992_ = lean_alloc_closure(
        l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_992_, 0, v_fn_987_);
    lean_closure_set(v___f_992_, 1, v_toBind_989_);
    lean_closure_set(v___f_992_, 2, v___f_991_);
    lean_closure_set(v___f_992_, 3, v_toPure_990_);
    v___x_993_ = l_Lean_Meta_forEachExpr_x27___redArg(
        v_inst_983_,
        v_inst_984_,
        v_inst_985_,
        v_input_986_,
        v___f_992_,
    );
    return v___x_993_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM(
    mut v_m_994_: *mut LeanObject,
    mut v_inst_995_: *mut LeanObject,
    mut v_inst_996_: *mut LeanObject,
    mut v_inst_997_: *mut LeanObject,
    mut v_input_998_: *mut LeanObject,
    mut v_fn_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = l_Lean_Meta_forEachSorryM___redArg(
        v_inst_995_,
        v_inst_996_,
        v_inst_997_,
        v_input_998_,
        v_fn_999_,
    );
    return v___x_1000_;
}
pub unsafe fn l_Lean_Declaration_forEachSorryM___redArg___lam__0(
    mut v_inst_1001_: *mut LeanObject,
    mut v_inst_1002_: *mut LeanObject,
    mut v_inst_1003_: *mut LeanObject,
    mut v_fn_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Lean_Meta_forEachSorryM___redArg(
        v_inst_1001_,
        v_inst_1002_,
        v_inst_1003_,
        v_a_1006_,
        v_fn_1004_,
    );
    return v___x_1007_;
}
pub unsafe fn l_Lean_Declaration_forEachSorryM___redArg(
    mut v_inst_1008_: *mut LeanObject,
    mut v_inst_1009_: *mut LeanObject,
    mut v_inst_1010_: *mut LeanObject,
    mut v_decl_1011_: *mut LeanObject,
    mut v_fn_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1008_);
    v___f_1013_ = lean_alloc_closure(
        l_Lean_Declaration_forEachSorryM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_1013_, 0, v_inst_1008_);
    lean_closure_set(v___f_1013_, 1, v_inst_1009_);
    lean_closure_set(v___f_1013_, 2, v_inst_1010_);
    lean_closure_set(v___f_1013_, 3, v_fn_1012_);
    v___x_1014_ = lean_box(0);
    v___x_1015_ =
        l_Lean_Declaration_foldExprM___redArg(v_inst_1008_, v_decl_1011_, v___f_1013_, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_Declaration_forEachSorryM(
    mut v_m_1016_: *mut LeanObject,
    mut v_inst_1017_: *mut LeanObject,
    mut v_inst_1018_: *mut LeanObject,
    mut v_inst_1019_: *mut LeanObject,
    mut v_decl_1020_: *mut LeanObject,
    mut v_fn_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1022_ = l_Lean_Declaration_forEachSorryM___redArg(
        v_inst_1017_,
        v_inst_1018_,
        v_inst_1019_,
        v_decl_1020_,
        v_fn_1021_,
    );
    return v___x_1022_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Utf16(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sorry(builtin);
}

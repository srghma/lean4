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
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSorry___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkSorry___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5207765522374246084 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSorry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkSorry___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkSorry___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkSorry___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkSorry___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkSorry___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSorry___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__3_value)
                as *mut crate::leanh::LeanObject,
            15761733860085307253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSorry___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkSorry___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSorry___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSorry___closed__6_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkSorry___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkSorry___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkSorry___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__6_value)
                as *mut crate::leanh::LeanObject,
            9255189395584251158 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSorry___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSorry___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkSorry___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSorry___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_SorryLabelView_encode___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [95, 115, 111, 114, 114, 121, 0],
    };
static mut l_Lean_Meta_SorryLabelView_encode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SorryLabelView_encode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkLabeledSorry___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13306843946249674491 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10552689246107305202 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value)
                as *mut crate::leanh::LeanObject,
            9833841078580172006 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkLabeledSorry___closed__8_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkLabeledSorry___closed__9_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__8_value)
                as *mut crate::leanh::LeanObject,
            920240211420121313 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkLabeledSorry___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__10_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__9_value)
                as *mut crate::leanh::LeanObject,
            12861851057597587943 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkLabeledSorry___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkLabeledSorry___closed__16_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkLabeledSorry___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__5_value)
                as *mut crate::leanh::LeanObject,
            9833841078580172006 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkLabeledSorry___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__17_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__16_value)
                as *mut crate::leanh::LeanObject,
            565778312915565143 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkLabeledSorry___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkLabeledSorry___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkLabeledSorry___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
    mut v_constName_512_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_513_: u8,
    mut v___y_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_st_ref_get(v___y_514_);
    v_env_517_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
    crate::leanh::lean_inc_ref(v_env_517_);
    crate::leanh::lean_dec(v___x_516_);
    v___x_518_ = l_Lean_Environment_contains(v_env_517_, v_constName_512_, v_skipRealize_513_);
    v___x_519_ = crate::leanh::lean_box((v___x_518_) as usize);
    v___x_520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_519_);
    return v___x_520_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(
    mut v_constName_521_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_522_: *mut crate::leanh::LeanObject,
    mut v___y_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_525_ = (crate::leanh::lean_unbox(v_skipRealize_522_) as u8);
    v_res_526_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
        v_constName_521_,
        v_skipRealize_boxed_525_,
        v___y_523_,
    );
    crate::leanh::lean_dec(v___y_523_);
    return v_res_526_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(
    mut v_constName_527_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_528_: u8,
    mut v___y_529_: *mut crate::leanh::LeanObject,
    mut v___y_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(
        v_constName_527_,
        v_skipRealize_528_,
        v___y_532_,
    );
    return v___x_534_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(
    mut v_constName_535_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_536_: *mut crate::leanh::LeanObject,
    mut v___y_537_: *mut crate::leanh::LeanObject,
    mut v___y_538_: *mut crate::leanh::LeanObject,
    mut v___y_539_: *mut crate::leanh::LeanObject,
    mut v___y_540_: *mut crate::leanh::LeanObject,
    mut v___y_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_542_: u8 = 0;
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_542_ = (crate::leanh::lean_unbox(v_skipRealize_536_) as u8);
    v_res_543_ = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(
        v_constName_535_,
        v_skipRealize_boxed_542_,
        v___y_537_,
        v___y_538_,
        v___y_539_,
        v___y_540_,
    );
    crate::leanh::lean_dec(v___y_540_);
    crate::leanh::lean_dec_ref(v___y_539_);
    crate::leanh::lean_dec(v___y_538_);
    crate::leanh::lean_dec_ref(v___y_537_);
    return v_res_543_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = crate::leanh::lean_box(0);
    v___x_545_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_546_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_546_, 0, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_546_, 1, v___x_544_);
    return v___x_546_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_548_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0);
    v___x_549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_548_);
    return v___x_549_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(
    mut v___y_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
    return v_res_551_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(
    mut v_00_u03b1_552_: *mut crate::leanh::LeanObject,
    mut v___y_553_: *mut crate::leanh::LeanObject,
    mut v___y_554_: *mut crate::leanh::LeanObject,
    mut v___y_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
    return v___x_558_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(
    mut v_00_u03b1_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(
        v_00_u03b1_559_,
        v___y_560_,
        v___y_561_,
        v___y_562_,
        v___y_563_,
    );
    crate::leanh::lean_dec(v___y_563_);
    crate::leanh::lean_dec_ref(v___y_562_);
    crate::leanh::lean_dec(v___y_561_);
    crate::leanh::lean_dec_ref(v___y_560_);
    return v_res_565_;
}
pub unsafe fn _init_l_Lean_Meta_mkSorry___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = crate::leanh::lean_box(0);
    v___x_575_ = l_Lean_Meta_mkSorry___closed__4;
    v___x_576_ = l_Lean_mkConst(v___x_575_, v___x_574_);
    return v___x_576_;
}
pub unsafe fn _init_l_Lean_Meta_mkSorry___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = crate::leanh::lean_box(0);
    v___x_582_ = l_Lean_Meta_mkSorry___closed__7;
    v___x_583_ = l_Lean_mkConst(v___x_582_, v___x_581_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Meta_mkSorry(
    mut v_type_584_: *mut crate::leanh::LeanObject,
    mut v_synthetic_585_: u8,
    mut v_a_586_: *mut crate::leanh::LeanObject,
    mut v_a_587_: *mut crate::leanh::LeanObject,
    mut v_a_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_616_: u8 = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: u8 = 0;
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_619_ = crate::leanh::lean_ctor_get(v___x_618_, 0);
                crate::leanh::lean_inc(v_a_619_);
                crate::leanh::lean_dec_ref(v___x_618_);
                v___x_620_ = (crate::leanh::lean_unbox(v_a_619_) as u8);
                crate::leanh::lean_dec(v_a_619_);
                if v___x_620_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_584_);
                    v___x_621_ =
                        l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
                    v_a_622_ = crate::leanh::lean_ctor_get(v___x_621_, 0);
                    v_isSharedCheck_629_ = (!crate::leanh::lean_is_exclusive(v___x_621_)) as u8;
                    if v_isSharedCheck_629_ == 0 {
                        v___x_624_ = v___x_621_;
                        v_isShared_625_ = v_isSharedCheck_629_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_622_);
                        crate::leanh::lean_dec(v___x_621_);
                        v___x_624_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc_ref(v___y_593_);
                v___x_594_ = l_Lean_mkAppB(v___y_592_, v_type_584_, v___y_593_);
                v___x_595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_595_, 0, v___x_594_);
                return v___x_595_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_type_584_);
                v___x_602_ = l_Lean_Meta_getLevel(
                    v_type_584_,
                    v___y_598_,
                    v___y_599_,
                    v___y_600_,
                    v___y_601_,
                );
                if crate::leanh::lean_obj_tag(v___x_602_) == 0 {
                    v_a_603_ = crate::leanh::lean_ctor_get(v___x_602_, 0);
                    crate::leanh::lean_inc(v_a_603_);
                    crate::leanh::lean_dec_ref_known(v___x_602_, 1);
                    v___x_604_ = crate::leanh::lean_box(0);
                    v___x_605_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_605_, 0, v_a_603_);
                    crate::leanh::lean_ctor_set(v___x_605_, 1, v___x_604_);
                    v___x_606_ = l_Lean_mkConst(v___x_596_, v___x_605_);
                    if v_synthetic_585_ == 0 {
                        v___x_607_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSorry___closed__5_once),
                            _init_l_Lean_Meta_mkSorry___closed__5,
                        );
                        v___y_592_ = v___x_606_;
                        v___y_593_ = v___x_607_;
                        state = 1;
                        continue;
                    } else {
                        v___x_608_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec_ref(v_type_584_);
                    v_a_609_ = crate::leanh::lean_ctor_get(v___x_602_, 0);
                    v_isSharedCheck_616_ = (!crate::leanh::lean_is_exclusive(v___x_602_)) as u8;
                    if v_isSharedCheck_616_ == 0 {
                        v___x_611_ = v___x_602_;
                        v_isShared_612_ = v_isSharedCheck_616_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_609_);
                        crate::leanh::lean_dec(v___x_602_);
                        v___x_611_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
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
                    v_reuseFailAlloc_628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
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
    mut v_type_630_: *mut crate::leanh::LeanObject,
    mut v_synthetic_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_boxed_637_: u8 = 0;
    let mut v_res_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_637_ = (crate::leanh::lean_unbox(v_synthetic_631_) as u8);
    v_res_638_ = l_Lean_Meta_mkSorry(
        v_type_630_,
        v_synthetic_boxed_637_,
        v_a_632_,
        v_a_633_,
        v_a_634_,
        v_a_635_,
    );
    crate::leanh::lean_dec(v_a_635_);
    crate::leanh::lean_dec_ref(v_a_634_);
    crate::leanh::lean_dec(v_a_633_);
    crate::leanh::lean_dec_ref(v_a_632_);
    return v_res_638_;
}
pub unsafe fn l_Lean_Meta_SorryLabelView_encode(
    mut v_view_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
    mut v_a_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_view_640_) == 1 {
                    v_val_649_ = crate::leanh::lean_ctor_get(v_view_640_, 0);
                    crate::leanh::lean_inc(v_val_649_);
                    crate::leanh::lean_dec_ref_known(v_view_640_, 1);
                    v_range_650_ = crate::leanh::lean_ctor_get(v_val_649_, 1);
                    crate::leanh::lean_inc_ref(v_range_650_);
                    v_pos_651_ = crate::leanh::lean_ctor_get(v_range_650_, 0);
                    crate::leanh::lean_inc_ref(v_pos_651_);
                    v_endPos_652_ = crate::leanh::lean_ctor_get(v_range_650_, 2);
                    crate::leanh::lean_inc_ref(v_endPos_652_);
                    v_module_653_ = crate::leanh::lean_ctor_get(v_val_649_, 0);
                    crate::leanh::lean_inc(v_module_653_);
                    crate::leanh::lean_dec(v_val_649_);
                    v_charUtf16_654_ = crate::leanh::lean_ctor_get(v_range_650_, 1);
                    crate::leanh::lean_inc(v_charUtf16_654_);
                    v_endCharUtf16_655_ = crate::leanh::lean_ctor_get(v_range_650_, 3);
                    crate::leanh::lean_inc(v_endCharUtf16_655_);
                    crate::leanh::lean_dec_ref(v_range_650_);
                    v_line_656_ = crate::leanh::lean_ctor_get(v_pos_651_, 0);
                    crate::leanh::lean_inc(v_line_656_);
                    v_column_657_ = crate::leanh::lean_ctor_get(v_pos_651_, 1);
                    crate::leanh::lean_inc(v_column_657_);
                    crate::leanh::lean_dec_ref(v_pos_651_);
                    v_line_658_ = crate::leanh::lean_ctor_get(v_endPos_652_, 0);
                    crate::leanh::lean_inc(v_line_658_);
                    v_column_659_ = crate::leanh::lean_ctor_get(v_endPos_652_, 1);
                    crate::leanh::lean_inc(v_column_659_);
                    crate::leanh::lean_dec_ref(v_endPos_652_);
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
                    crate::leanh::lean_dec(v_view_640_);
                    v___x_666_ = crate::leanh::lean_box(0);
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
    mut v_view_667_: *mut crate::leanh::LeanObject,
    mut v_a_668_: *mut crate::leanh::LeanObject,
    mut v_a_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Lean_Meta_SorryLabelView_encode(v_view_667_, v_a_668_, v_a_669_);
    crate::leanh::lean_dec(v_a_669_);
    crate::leanh::lean_dec_ref(v_a_668_);
    return v_res_671_;
}
pub unsafe fn l_Lean_Meta_SorryLabelView_decode_x3f(
    mut v_name_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: u8 = 0;
    v___x_673_ = l_Lean_Name_hasMacroScopes(v_name_672_);
    if v___x_673_ == 0 {
        let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_name_672_);
        v___x_674_ = crate::leanh::lean_box(0);
        return v___x_674_;
    } else {
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_675_ = lean_erase_macro_scopes(v_name_672_);
        if crate::leanh::lean_obj_tag(v___x_675_) == 1 {
            let mut v_pre_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_679_: u8 = 0;
            v_pre_676_ = crate::leanh::lean_ctor_get(v___x_675_, 0);
            crate::leanh::lean_inc(v_pre_676_);
            v_str_677_ = crate::leanh::lean_ctor_get(v___x_675_, 1);
            crate::leanh::lean_inc_ref(v_str_677_);
            crate::leanh::lean_dec_ref_known(v___x_675_, 2);
            v___x_678_ = l_Lean_Meta_SorryLabelView_encode___closed__0;
            v___x_679_ = lean_string_dec_eq(v_str_677_, v___x_678_);
            crate::leanh::lean_dec_ref(v_str_677_);
            if v___x_679_ == 0 {
                let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_pre_676_);
                v___x_680_ = crate::leanh::lean_box(0);
                return v___x_680_;
            } else {
                if crate::leanh::lean_obj_tag(v_pre_676_) == 2 {
                    let mut v_pre_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_pre_681_ = crate::leanh::lean_ctor_get(v_pre_676_, 0);
                    crate::leanh::lean_inc(v_pre_681_);
                    if crate::leanh::lean_obj_tag(v_pre_681_) == 2 {
                        let mut v_pre_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_682_ = crate::leanh::lean_ctor_get(v_pre_681_, 0);
                        crate::leanh::lean_inc(v_pre_682_);
                        if crate::leanh::lean_obj_tag(v_pre_682_) == 2 {
                            let mut v_pre_683_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_pre_683_ = crate::leanh::lean_ctor_get(v_pre_682_, 0);
                            crate::leanh::lean_inc(v_pre_683_);
                            if crate::leanh::lean_obj_tag(v_pre_683_) == 2 {
                                let mut v_pre_684_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_pre_684_ = crate::leanh::lean_ctor_get(v_pre_683_, 0);
                                crate::leanh::lean_inc(v_pre_684_);
                                if crate::leanh::lean_obj_tag(v_pre_684_) == 2 {
                                    let mut v_pre_685_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_pre_685_ = crate::leanh::lean_ctor_get(v_pre_684_, 0);
                                    crate::leanh::lean_inc(v_pre_685_);
                                    if crate::leanh::lean_obj_tag(v_pre_685_) == 2 {
                                        let mut v_i_686_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_i_687_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_i_688_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_i_689_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_i_690_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_pre_691_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_i_692_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_693_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_694_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_695_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_696_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_697_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_698_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_i_686_ = crate::leanh::lean_ctor_get(v_pre_676_, 1);
                                        crate::leanh::lean_inc(v_i_686_);
                                        crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                                        v_i_687_ = crate::leanh::lean_ctor_get(v_pre_681_, 1);
                                        crate::leanh::lean_inc(v_i_687_);
                                        crate::leanh::lean_dec_ref_known(v_pre_681_, 2);
                                        v_i_688_ = crate::leanh::lean_ctor_get(v_pre_682_, 1);
                                        crate::leanh::lean_inc(v_i_688_);
                                        crate::leanh::lean_dec_ref_known(v_pre_682_, 2);
                                        v_i_689_ = crate::leanh::lean_ctor_get(v_pre_683_, 1);
                                        crate::leanh::lean_inc(v_i_689_);
                                        crate::leanh::lean_dec_ref_known(v_pre_683_, 2);
                                        v_i_690_ = crate::leanh::lean_ctor_get(v_pre_684_, 1);
                                        crate::leanh::lean_inc(v_i_690_);
                                        crate::leanh::lean_dec_ref_known(v_pre_684_, 2);
                                        v_pre_691_ = crate::leanh::lean_ctor_get(v_pre_685_, 0);
                                        crate::leanh::lean_inc(v_pre_691_);
                                        v_i_692_ = crate::leanh::lean_ctor_get(v_pre_685_, 1);
                                        crate::leanh::lean_inc(v_i_692_);
                                        crate::leanh::lean_dec_ref_known(v_pre_685_, 2);
                                        v___x_693_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_693_, 0, v_i_692_);
                                        crate::leanh::lean_ctor_set(v___x_693_, 1, v_i_690_);
                                        v___x_694_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_694_, 0, v_i_689_);
                                        crate::leanh::lean_ctor_set(v___x_694_, 1, v_i_688_);
                                        v___x_695_ =
                                            crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_695_, 0, v___x_693_);
                                        crate::leanh::lean_ctor_set(v___x_695_, 1, v_i_687_);
                                        crate::leanh::lean_ctor_set(v___x_695_, 2, v___x_694_);
                                        crate::leanh::lean_ctor_set(v___x_695_, 3, v_i_686_);
                                        v___x_696_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_696_, 0, v_pre_691_);
                                        crate::leanh::lean_ctor_set(v___x_696_, 1, v___x_695_);
                                        v___x_697_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_697_, 0, v___x_696_);
                                        v___x_698_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_697_);
                                        return v___x_698_;
                                    } else {
                                        let mut v___x_699_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        crate::leanh::lean_dec(v_pre_685_);
                                        crate::leanh::lean_dec_ref_known(v_pre_684_, 2);
                                        crate::leanh::lean_dec_ref_known(v_pre_683_, 2);
                                        crate::leanh::lean_dec_ref_known(v_pre_682_, 2);
                                        crate::leanh::lean_dec_ref_known(v_pre_681_, 2);
                                        crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                                        v___x_699_ = crate::leanh::lean_box(0);
                                        return v___x_699_;
                                    }
                                } else {
                                    let mut v___x_700_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v_pre_684_);
                                    crate::leanh::lean_dec_ref_known(v_pre_683_, 2);
                                    crate::leanh::lean_dec_ref_known(v_pre_682_, 2);
                                    crate::leanh::lean_dec_ref_known(v_pre_681_, 2);
                                    crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                                    v___x_700_ = crate::leanh::lean_box(0);
                                    return v___x_700_;
                                }
                            } else {
                                let mut v___x_701_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v_pre_683_);
                                crate::leanh::lean_dec_ref_known(v_pre_682_, 2);
                                crate::leanh::lean_dec_ref_known(v_pre_681_, 2);
                                crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                                v___x_701_ = crate::leanh::lean_box(0);
                                return v___x_701_;
                            }
                        } else {
                            let mut v___x_702_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v_pre_681_, 2);
                            crate::leanh::lean_dec(v_pre_682_);
                            crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                            v___x_702_ = crate::leanh::lean_box(0);
                            return v___x_702_;
                        }
                    } else {
                        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v_pre_676_, 2);
                        crate::leanh::lean_dec(v_pre_681_);
                        v___x_703_ = crate::leanh::lean_box(0);
                        return v___x_703_;
                    }
                } else {
                    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_pre_676_);
                    v___x_704_ = crate::leanh::lean_box(0);
                    return v___x_704_;
                }
            }
        } else {
            let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_675_);
            v___x_705_ = crate::leanh::lean_box(0);
            return v___x_705_;
        }
    }
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(
    mut v___y_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = lean_st_ref_get(v___y_706_);
    v_env_709_ = crate::leanh::lean_ctor_get(v___x_708_, 0);
    crate::leanh::lean_inc_ref(v_env_709_);
    crate::leanh::lean_dec(v___x_708_);
    v___x_710_ = l_Lean_Environment_header(v_env_709_);
    crate::leanh::lean_dec_ref(v_env_709_);
    v_mainModule_711_ = crate::leanh::lean_ctor_get(v___x_710_, 0);
    crate::leanh::lean_inc(v_mainModule_711_);
    crate::leanh::lean_dec_ref(v___x_710_);
    v___x_712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_712_, 0, v_mainModule_711_);
    return v___x_712_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ =
        l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_713_);
    crate::leanh::lean_dec(v___y_713_);
    return v_res_715_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(
    mut v___y_716_: *mut crate::leanh::LeanObject,
    mut v___y_717_: *mut crate::leanh::LeanObject,
    mut v___y_718_: *mut crate::leanh::LeanObject,
    mut v___y_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ =
        l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(v___y_719_);
    return v___x_721_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(
    mut v___y_722_: *mut crate::leanh::LeanObject,
    mut v___y_723_: *mut crate::leanh::LeanObject,
    mut v___y_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
    mut v___y_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(
        v___y_722_, v___y_723_, v___y_724_, v___y_725_,
    );
    crate::leanh::lean_dec(v___y_725_);
    crate::leanh::lean_dec_ref(v___y_724_);
    crate::leanh::lean_dec(v___y_723_);
    crate::leanh::lean_dec_ref(v___y_722_);
    return v_res_727_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = crate::leanh::lean_box(0);
    v___x_740_ = l_Lean_Meta_mkLabeledSorry___closed__6;
    v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
    return v___x_741_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_747_ = crate::leanh::lean_box(0);
    v___x_748_ = l_Lean_Level_succ___override(v___x_747_);
    return v___x_748_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = crate::leanh::lean_box(0);
    v___x_750_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__11,
    );
    v___x_751_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_751_, 0, v___x_750_);
    crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_749_);
    return v___x_751_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__12_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__12,
    );
    v___x_753_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__11_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__11,
    );
    v___x_754_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_754_, 0, v___x_753_);
    crate::leanh::lean_ctor_set(v___x_754_, 1, v___x_752_);
    return v___x_754_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__13_once),
        _init_l_Lean_Meta_mkLabeledSorry___closed__13,
    );
    v___x_756_ = l_Lean_Meta_mkLabeledSorry___closed__10;
    v___x_757_ = l_Lean_mkConst(v___x_756_, v___x_755_);
    return v___x_757_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = crate::leanh::lean_box(0);
    v___x_759_ = l_Lean_Meta_mkLabeledSorry___closed__2;
    v___x_760_ = l_Lean_mkConst(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_Meta_mkLabeledSorry___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = crate::leanh::lean_box(0);
    v___x_766_ = l_Lean_Meta_mkLabeledSorry___closed__17;
    v___x_767_ = l_Lean_mkConst(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn l_Lean_Meta_mkLabeledSorry(
    mut v_type_768_: *mut crate::leanh::LeanObject,
    mut v_synthetic_769_: u8,
    mut v_unique_770_: u8,
    mut v_a_771_: *mut crate::leanh::LeanObject,
    mut v_a_772_: *mut crate::leanh::LeanObject,
    mut v_a_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tag_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_791_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_816_: u8 = 0;
    let mut v___y_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_828_: u8 = 0;
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v___y_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut v_reuseFailAlloc_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_unused_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_878_: u8 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_881_ = crate::leanh::lean_ctor_get(v___x_880_, 0);
                crate::leanh::lean_inc(v_a_881_);
                crate::leanh::lean_dec_ref(v___x_880_);
                v___x_882_ = (crate::leanh::lean_unbox(v_a_881_) as u8);
                crate::leanh::lean_dec(v_a_881_);
                if v___x_882_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_768_);
                    v___x_883_ =
                        l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
                    v_a_884_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                    v_isSharedCheck_891_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_886_ = v___x_883_;
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_884_);
                        crate::leanh::lean_dec(v___x_883_);
                        v___x_886_ = crate::leanh::lean_box(0);
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
                    v___x_785_ = crate::leanh::lean_obj_once(
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
                    if crate::leanh::lean_obj_tag(v___x_787_) == 0 {
                        v_a_788_ = crate::leanh::lean_ctor_get(v___x_787_, 0);
                        v_isSharedCheck_801_ = (!crate::leanh::lean_is_exclusive(v___x_787_)) as u8;
                        if v_isSharedCheck_801_ == 0 {
                            v___x_790_ = v___x_787_;
                            v_isShared_791_ = v_isSharedCheck_801_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_788_);
                            crate::leanh::lean_dec(v___x_787_);
                            v___x_790_ = crate::leanh::lean_box(0);
                            v_isShared_791_ = v_isSharedCheck_801_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tag_778_);
                        return v___x_787_;
                    }
                } else {
                    v___x_802_ = l_Lean_Meta_mkLabeledSorry___closed__4;
                    v___x_803_ = 0;
                    v___x_804_ = crate::leanh::lean_obj_once(
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
                    if crate::leanh::lean_obj_tag(v___x_806_) == 0 {
                        v_a_807_ = crate::leanh::lean_ctor_get(v___x_806_, 0);
                        v_isSharedCheck_816_ = (!crate::leanh::lean_is_exclusive(v___x_806_)) as u8;
                        if v_isSharedCheck_816_ == 0 {
                            v___x_809_ = v___x_806_;
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_807_);
                            crate::leanh::lean_dec(v___x_806_);
                            v___x_809_ = crate::leanh::lean_box(0);
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tag_778_);
                        return v___x_806_;
                    }
                }
            }
            2 => {
                v___x_792_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__14_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__14,
                );
                v___x_793_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__15_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__15,
                );
                v___x_794_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkLabeledSorry___closed__18_once),
                    _init_l_Lean_Meta_mkLabeledSorry___closed__18,
                );
                v___x_795_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_tag_778_);
                v___x_796_ =
                    l_Lean_mkApp4(v___x_792_, v___x_785_, v___x_793_, v___x_794_, v___x_795_);
                v___x_797_ = l_Lean_Expr_app___override(v_a_788_, v___x_796_);
                if v_isShared_791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_790_, 0, v___x_797_);
                    v___x_799_ = v___x_790_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
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
                    crate::leanh::lean_ctor_set(v___x_809_, 0, v___x_812_);
                    v___x_814_ = v___x_809_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
                    v___x_814_ = v_reuseFailAlloc_815_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_814_;
            }
            6 => {
                v___x_822_ = crate::leanh::lean_box(0);
                v___x_823_ = l_Lean_Meta_SorryLabelView_encode(v___x_822_, v___y_820_, v___y_821_);
                if crate::leanh::lean_obj_tag(v___x_823_) == 0 {
                    v_a_824_ = crate::leanh::lean_ctor_get(v___x_823_, 0);
                    crate::leanh::lean_inc(v_a_824_);
                    crate::leanh::lean_dec_ref_known(v___x_823_, 1);
                    v_tag_778_ = v_a_824_;
                    v___y_779_ = v___y_818_;
                    v___y_780_ = v___y_819_;
                    v___y_781_ = v___y_820_;
                    v___y_782_ = v___y_821_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_type_768_);
                    v_a_825_ = crate::leanh::lean_ctor_get(v___x_823_, 0);
                    v_isSharedCheck_832_ = (!crate::leanh::lean_is_exclusive(v___x_823_)) as u8;
                    if v_isSharedCheck_832_ == 0 {
                        v___x_827_ = v___x_823_;
                        v_isShared_828_ = v_isSharedCheck_832_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_825_);
                        crate::leanh::lean_dec(v___x_823_);
                        v___x_827_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
                    v___x_830_ = v_reuseFailAlloc_831_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_830_;
            }
            9 => {
                v_fileMap_838_ = crate::leanh::lean_ctor_get(v___y_836_, 1);
                v_ref_839_ = crate::leanh::lean_ctor_get(v___y_836_, 5);
                v___x_840_ = 0;
                v___x_841_ = l_Lean_Syntax_getPos_x3f(v_ref_839_, v___x_840_);
                if crate::leanh::lean_obj_tag(v___x_841_) == 1 {
                    v_val_842_ = crate::leanh::lean_ctor_get(v___x_841_, 0);
                    crate::leanh::lean_inc(v_val_842_);
                    crate::leanh::lean_dec_ref_known(v___x_841_, 1);
                    v___x_843_ = l_Lean_Syntax_getTailPos_x3f(v_ref_839_, v___x_840_);
                    if crate::leanh::lean_obj_tag(v___x_843_) == 1 {
                        v_val_844_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                        v_isSharedCheck_878_ = (!crate::leanh::lean_is_exclusive(v___x_843_)) as u8;
                        if v_isSharedCheck_878_ == 0 {
                            v___x_846_ = v___x_843_;
                            v_isShared_847_ = v_isSharedCheck_878_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_844_);
                            crate::leanh::lean_dec(v___x_843_);
                            v___x_846_ = crate::leanh::lean_box(0);
                            v_isShared_847_ = v_isSharedCheck_878_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_843_);
                        crate::leanh::lean_dec(v_val_842_);
                        v___y_818_ = v___y_834_;
                        v___y_819_ = v___y_835_;
                        v___y_820_ = v___y_836_;
                        v___y_821_ = v___y_837_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_841_);
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
                v_a_849_ = crate::leanh::lean_ctor_get(v___x_848_, 0);
                crate::leanh::lean_inc(v_a_849_);
                crate::leanh::lean_dec_ref(v___x_848_);
                crate::leanh::lean_inc_ref_n(v_fileMap_838_, 4);
                v___x_850_ = l_Lean_FileMap_toPosition(v_fileMap_838_, v_val_842_);
                v___x_851_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_838_, v_val_842_);
                crate::leanh::lean_dec(v_val_842_);
                v_character_852_ = crate::leanh::lean_ctor_get(v___x_851_, 1);
                crate::leanh::lean_inc(v_character_852_);
                crate::leanh::lean_dec_ref(v___x_851_);
                v___x_853_ = l_Lean_FileMap_toPosition(v_fileMap_838_, v_val_844_);
                v___x_854_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_838_, v_val_844_);
                crate::leanh::lean_dec(v_val_844_);
                v_character_855_ = crate::leanh::lean_ctor_get(v___x_854_, 1);
                v_isSharedCheck_876_ = (!crate::leanh::lean_is_exclusive(v___x_854_)) as u8;
                if v_isSharedCheck_876_ == 0 {
                    v_unused_877_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                    crate::leanh::lean_dec(v_unused_877_);
                    v___x_857_ = v___x_854_;
                    v_isShared_858_ = v_isSharedCheck_876_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_character_855_);
                    crate::leanh::lean_dec(v___x_854_);
                    v___x_857_ = crate::leanh::lean_box(0);
                    v_isShared_858_ = v_isSharedCheck_876_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_859_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_850_);
                crate::leanh::lean_ctor_set(v___x_859_, 1, v_character_852_);
                crate::leanh::lean_ctor_set(v___x_859_, 2, v___x_853_);
                crate::leanh::lean_ctor_set(v___x_859_, 3, v_character_855_);
                if v_isShared_858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_857_, 1, v___x_859_);
                    crate::leanh::lean_ctor_set(v___x_857_, 0, v_a_849_);
                    v___x_861_ = v___x_857_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_859_);
                    v___x_861_ = v_reuseFailAlloc_875_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_861_);
                    v___x_863_ = v___x_846_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_874_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_861_);
                    v___x_863_ = v_reuseFailAlloc_874_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_864_ = l_Lean_Meta_SorryLabelView_encode(v___x_863_, v___y_836_, v___y_837_);
                if crate::leanh::lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    crate::leanh::lean_inc(v_a_865_);
                    crate::leanh::lean_dec_ref_known(v___x_864_, 1);
                    v_tag_778_ = v_a_865_;
                    v___y_779_ = v___y_834_;
                    v___y_780_ = v___y_835_;
                    v___y_781_ = v___y_836_;
                    v___y_782_ = v___y_837_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_type_768_);
                    v_a_866_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_873_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_873_ == 0 {
                        v___x_868_ = v___x_864_;
                        v_isShared_869_ = v_isSharedCheck_873_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_866_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_868_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
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
                    v_reuseFailAlloc_890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
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
    mut v_type_892_: *mut crate::leanh::LeanObject,
    mut v_synthetic_893_: *mut crate::leanh::LeanObject,
    mut v_unique_894_: *mut crate::leanh::LeanObject,
    mut v_a_895_: *mut crate::leanh::LeanObject,
    mut v_a_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_boxed_900_: u8 = 0;
    let mut v_unique_boxed_901_: u8 = 0;
    let mut v_res_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_900_ = (crate::leanh::lean_unbox(v_synthetic_893_) as u8);
    v_unique_boxed_901_ = (crate::leanh::lean_unbox(v_unique_894_) as u8);
    v_res_902_ = l_Lean_Meta_mkLabeledSorry(
        v_type_892_,
        v_synthetic_boxed_900_,
        v_unique_boxed_901_,
        v_a_895_,
        v_a_896_,
        v_a_897_,
        v_a_898_,
    );
    crate::leanh::lean_dec(v_a_898_);
    crate::leanh::lean_dec_ref(v_a_897_);
    crate::leanh::lean_dec(v_a_896_);
    crate::leanh::lean_dec_ref(v_a_895_);
    return v_res_902_;
}
pub unsafe fn l_Lean_Meta_isLabeledSorry_x3f(
    mut v_e_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    v___x_904_ = l_Lean_Meta_mkSorry___closed__1;
    v___x_905_ = l_Lean_Expr_isAppOf(v_e_903_, v___x_904_);
    if v___x_905_ == 0 {
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_906_ = crate::leanh::lean_box(0);
        return v___x_906_;
    } else {
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: u8 = 0;
        v___x_907_ = l_Lean_Expr_getAppNumArgs(v_e_903_);
        v___x_908_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_909_ = lean_nat_dec_le(v___x_908_, v___x_907_);
        if v___x_909_ == 0 {
            let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_907_);
            v___x_910_ = crate::leanh::lean_box(0);
            return v___x_910_;
        } else {
            let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_911_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_912_ = lean_nat_sub(v___x_907_, v___x_911_);
            crate::leanh::lean_dec(v___x_907_);
            v___x_913_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_914_ = lean_nat_sub(v___x_912_, v___x_913_);
            crate::leanh::lean_dec(v___x_912_);
            v___x_915_ = l_Lean_Expr_getRevArg_x21(v_e_903_, v___x_914_);
            crate::leanh::lean_inc_ref(v___x_915_);
            v___x_916_ = l_Lean_Expr_name_x3f(v___x_915_);
            if crate::leanh::lean_obj_tag(v___x_916_) == 1 {
                let mut v_val_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_915_);
                v_val_917_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                crate::leanh::lean_inc(v_val_917_);
                crate::leanh::lean_dec_ref_known(v___x_916_, 1);
                v___x_918_ = l_Lean_Meta_SorryLabelView_decode_x3f(v_val_917_);
                return v___x_918_;
            } else {
                let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_921_: u8 = 0;
                crate::leanh::lean_dec(v___x_916_);
                v___x_919_ = l_Lean_Meta_mkLabeledSorry___closed__10;
                v___x_920_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_921_ = l_Lean_Expr_isAppOfArity(v___x_915_, v___x_919_, v___x_920_);
                if v___x_921_ == 0 {
                    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v___x_915_);
                    v___x_922_ = crate::leanh::lean_box(0);
                    return v___x_922_;
                } else {
                    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_927_: u8 = 0;
                    v___x_923_ = l_Lean_Expr_appFn_x21(v___x_915_);
                    v___x_924_ = l_Lean_Expr_appArg_x21(v___x_923_);
                    crate::leanh::lean_dec_ref(v___x_923_);
                    v___x_925_ = l_Lean_Meta_mkLabeledSorry___closed__17;
                    v___x_926_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_927_ = l_Lean_Expr_isAppOfArity(v___x_924_, v___x_925_, v___x_926_);
                    crate::leanh::lean_dec_ref(v___x_924_);
                    if v___x_927_ == 0 {
                        let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v___x_915_);
                        v___x_928_ = crate::leanh::lean_box(0);
                        return v___x_928_;
                    } else {
                        let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_929_ = l_Lean_Expr_appArg_x21(v___x_915_);
                        crate::leanh::lean_dec_ref(v___x_915_);
                        v___x_930_ = l_Lean_Expr_name_x3f(v___x_929_);
                        if crate::leanh::lean_obj_tag(v___x_930_) == 0 {
                            let mut v___x_931_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_931_ = crate::leanh::lean_box(0);
                            return v___x_931_;
                        } else {
                            let mut v_val_932_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_933_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_val_932_ = crate::leanh::lean_ctor_get(v___x_930_, 0);
                            crate::leanh::lean_inc(v_val_932_);
                            crate::leanh::lean_dec_ref_known(v___x_930_, 1);
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
    mut v_e_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_934_);
    crate::leanh::lean_dec_ref(v_e_934_);
    return v_res_935_;
}
pub unsafe fn l_Lean_Expr_getSorry_x3f(
    mut v_e_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_unused_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_943_ = l_Lean_Expr_isSorry(v_e_936_);
                if v___x_943_ == 0 {
                    v___x_944_ = crate::leanh::lean_box(0);
                    return v___x_944_;
                } else {
                    v___x_945_ = l_Lean_Meta_isLabeledSorry_x3f(v_e_936_);
                    if crate::leanh::lean_obj_tag(v___x_945_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_956_ = (!crate::leanh::lean_is_exclusive(v___x_945_)) as u8;
                        if v_isSharedCheck_956_ == 0 {
                            v_unused_957_ = crate::leanh::lean_ctor_get(v___x_945_, 0);
                            crate::leanh::lean_dec(v_unused_957_);
                            v___x_947_ = v___x_945_;
                            v_isShared_948_ = v_isSharedCheck_956_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_945_);
                            v___x_947_ = crate::leanh::lean_box(0);
                            v_isShared_948_ = v_isSharedCheck_956_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_938_ = l_Lean_Expr_getAppNumArgs(v_e_936_);
                v___x_939_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_940_ = lean_nat_sub(v___x_938_, v___x_939_);
                crate::leanh::lean_dec(v___x_938_);
                v___x_941_ = l_Lean_Expr_getBoundedAppFn(v___x_940_, v_e_936_);
                v___x_942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
                return v___x_942_;
            }
            2 => {
                if v___x_943_ == 0 {
                    crate::leanh::lean_del_object(v___x_947_);
                    state = 1;
                    continue;
                } else {
                    v___x_949_ = l_Lean_Expr_getAppNumArgs(v_e_936_);
                    v___x_950_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_951_ = lean_nat_sub(v___x_949_, v___x_950_);
                    crate::leanh::lean_dec(v___x_949_);
                    v___x_952_ = l_Lean_Expr_getBoundedAppFn(v___x_951_, v_e_936_);
                    if v_isShared_948_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_947_, 0, v___x_952_);
                        v___x_954_ = v___x_947_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
pub unsafe fn l_Lean_Expr_getSorry_x3f___boxed(
    mut v_e_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lean_Expr_getSorry_x3f(v_e_958_);
    crate::leanh::lean_dec_ref(v_e_958_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__0(
    mut v_toPure_960_: *mut crate::leanh::LeanObject,
    mut v_____r_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = 0;
    v___x_963_ = crate::leanh::lean_box((v___x_962_) as usize);
    v___x_964_ = crate::leanh::lean_apply_2(v_toPure_960_, crate::leanh::lean_box(0), v___x_963_);
    return v___x_964_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__1(
    mut v_fn_965_: *mut crate::leanh::LeanObject,
    mut v_toBind_966_: *mut crate::leanh::LeanObject,
    mut v___f_967_: *mut crate::leanh::LeanObject,
    mut v_toPure_968_: *mut crate::leanh::LeanObject,
    mut v_e_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_Expr_getSorry_x3f(v_e_969_);
    if crate::leanh::lean_obj_tag(v___x_970_) == 1 {
        let mut v_val_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_968_);
        v_val_971_ = crate::leanh::lean_ctor_get(v___x_970_, 0);
        crate::leanh::lean_inc(v_val_971_);
        crate::leanh::lean_dec_ref_known(v___x_970_, 1);
        v___x_972_ = crate::leanh::lean_apply_1(v_fn_965_, v_val_971_);
        v___x_973_ = crate::leanh::lean_apply_4(
            v_toBind_966_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_972_,
            v___f_967_,
        );
        return v___x_973_;
    } else {
        let mut v___x_974_: u8 = 0;
        let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_970_);
        crate::leanh::lean_dec(v___f_967_);
        crate::leanh::lean_dec(v_toBind_966_);
        crate::leanh::lean_dec(v_fn_965_);
        v___x_974_ = 1;
        v___x_975_ = crate::leanh::lean_box((v___x_974_) as usize);
        v___x_976_ =
            crate::leanh::lean_apply_2(v_toPure_968_, crate::leanh::lean_box(0), v___x_975_);
        return v___x_976_;
    }
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(
    mut v_fn_977_: *mut crate::leanh::LeanObject,
    mut v_toBind_978_: *mut crate::leanh::LeanObject,
    mut v___f_979_: *mut crate::leanh::LeanObject,
    mut v_toPure_980_: *mut crate::leanh::LeanObject,
    mut v_e_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_Meta_forEachSorryM___redArg___lam__1(
        v_fn_977_,
        v_toBind_978_,
        v___f_979_,
        v_toPure_980_,
        v_e_981_,
    );
    crate::leanh::lean_dec_ref(v_e_981_);
    return v_res_982_;
}
pub unsafe fn l_Lean_Meta_forEachSorryM___redArg(
    mut v_inst_983_: *mut crate::leanh::LeanObject,
    mut v_inst_984_: *mut crate::leanh::LeanObject,
    mut v_inst_985_: *mut crate::leanh::LeanObject,
    mut v_input_986_: *mut crate::leanh::LeanObject,
    mut v_fn_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_988_ = crate::leanh::lean_ctor_get(v_inst_983_, 0);
    v_toBind_989_ = crate::leanh::lean_ctor_get(v_inst_983_, 1);
    v_toPure_990_ = crate::leanh::lean_ctor_get(v_toApplicative_988_, 1);
    crate::leanh::lean_inc_n(v_toPure_990_, 2);
    v___f_991_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_forEachSorryM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_991_, 0, v_toPure_990_);
    crate::leanh::lean_inc(v_toBind_989_);
    v___f_992_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_992_, 0, v_fn_987_);
    crate::leanh::lean_closure_set(v___f_992_, 1, v_toBind_989_);
    crate::leanh::lean_closure_set(v___f_992_, 2, v___f_991_);
    crate::leanh::lean_closure_set(v___f_992_, 3, v_toPure_990_);
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
    mut v_m_994_: *mut crate::leanh::LeanObject,
    mut v_inst_995_: *mut crate::leanh::LeanObject,
    mut v_inst_996_: *mut crate::leanh::LeanObject,
    mut v_inst_997_: *mut crate::leanh::LeanObject,
    mut v_input_998_: *mut crate::leanh::LeanObject,
    mut v_fn_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1001_: *mut crate::leanh::LeanObject,
    mut v_inst_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_fn_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
    mut v_a_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1008_: *mut crate::leanh::LeanObject,
    mut v_inst_1009_: *mut crate::leanh::LeanObject,
    mut v_inst_1010_: *mut crate::leanh::LeanObject,
    mut v_decl_1011_: *mut crate::leanh::LeanObject,
    mut v_fn_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1008_);
    v___f_1013_ = crate::leanh::lean_alloc_closure(
        l_Lean_Declaration_forEachSorryM___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1013_, 0, v_inst_1008_);
    crate::leanh::lean_closure_set(v___f_1013_, 1, v_inst_1009_);
    crate::leanh::lean_closure_set(v___f_1013_, 2, v_inst_1010_);
    crate::leanh::lean_closure_set(v___f_1013_, 3, v_fn_1012_);
    v___x_1014_ = crate::leanh::lean_box(0);
    v___x_1015_ =
        l_Lean_Declaration_foldExprM___redArg(v_inst_1008_, v_decl_1011_, v___f_1013_, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_Declaration_forEachSorryM(
    mut v_m_1016_: *mut crate::leanh::LeanObject,
    mut v_inst_1017_: *mut crate::leanh::LeanObject,
    mut v_inst_1018_: *mut crate::leanh::LeanObject,
    mut v_inst_1019_: *mut crate::leanh::LeanObject,
    mut v_decl_1020_: *mut crate::leanh::LeanObject,
    mut v_fn_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Meta_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sorry(builtin);
}

// Lean compiler output
// Module: Lean.Meta.StringLitProof
// Imports: Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::List::Basic::l_List_drop___redArg;
use crate::r#gen::Init::Data::List::BasicAux::{
    l_List_head_x21___redArg, l_List_tail_x21___redArg,
};
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkAppB,
    l_Lean_mkBVar, l_Lean_mkConst, l_Lean_mkLambda, l_Lean_mkNatLit, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEqRefl, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_data;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_uint32_dec_eq, lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint32, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 104, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value) as *mut LeanObject,18098914779984442139 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
static mut l_Lean_Meta_mkStringLitNeProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__2_value: LeanStringObject<5> =
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
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__3_value: LeanStringObject<4> =
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
        m_data: [110, 105, 108, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkStringLitNeProof___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__3_value) as *mut LeanObject,
        18135193680607614554 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__8_value: LeanStringObject<5> =
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
        m_data: [99, 111, 110, 115, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__8_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkStringLitNeProof___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__9_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__8_value) as *mut LeanObject,
        8614124190858717794 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__9_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__12_value: LeanStringObject<7> =
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
        m_data: [83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__12_value) as *mut LeanObject,
        3136308715950998022 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__13_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__15_value: LeanStringObject<7> =
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
        m_data: [111, 102, 76, 105, 115, 116, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__15_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__12_value)
                as *mut LeanObject,
            3136308715950998022 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__16_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__15_value) as *mut LeanObject,
        16845443598000453238 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__16_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__18_value: LeanStringObject<3> =
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
        m_data: [109, 116, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__19_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__18_value) as *mut LeanObject,
        5379098739744254188 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__19_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__21_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            111, 102, 76, 105, 115, 116, 95, 105, 110, 106, 101, 99, 116, 105, 118, 101, 0,
        ],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__21_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__22_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__12_value)
                as *mut LeanObject,
            3136308715950998022 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__22_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__21_value) as *mut LeanObject,
        4921736549043561301 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__22_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__24_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__27_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 111, 110, 115, 95, 110, 101, 95, 110, 105, 108, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__27_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__28_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__28_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__28_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__27_value) as *mut LeanObject,
        11625806356709288508 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__28_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__30_value: LeanStringObject<3> =
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
        m_data: [78, 101, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__30_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__31_value: LeanStringObject<5> =
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
        m_data: [115, 121, 109, 109, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__31_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__32_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__30_value)
                as *mut LeanObject,
            6695605208187598753 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__32_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__32_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__31_value) as *mut LeanObject,
        6773482220982667626 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__32_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__33_value: LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__33_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__34_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__33_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__34_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__35: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__36: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__37: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__38_value: LeanStringObject<2> =
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
        m_data: [108, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__38_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__39_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__38_value) as *mut LeanObject,
        17059415643108953228 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__39_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__40_value: LeanStringObject<5> =
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
        m_data: [100, 114, 111, 112, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__40_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__41_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__41_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__41_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__40_value) as *mut LeanObject,
        10539643452699375210 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__41_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__42_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__42: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__43_value: LeanStringObject<9> =
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
        m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__43_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__44_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__43_value) as *mut LeanObject,
        2642306550782628284 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__44_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__45: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkStringLitNeProof___closed__46_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__46: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__47_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            105, 110, 115, 116, 73, 110, 104, 97, 98, 105, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__47_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
pub static l_Lean_Meta_mkStringLitNeProof___closed__48_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__48_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__47_value) as *mut LeanObject,
        8179841645180766187 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__48_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__49_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__49: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__50_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__50_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__51_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__50_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__51_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__52_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__52: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__53_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 111, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__53_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
pub static l_Lean_Meta_mkStringLitNeProof___closed__54_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__54_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__53_value) as *mut LeanObject,
        5008959047061076168 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__54_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__55_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__55: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__56_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__56_value) as *mut LeanObject;
pub static l_Lean_Meta_mkStringLitNeProof___closed__57_value: LeanStringObject<6> =
    LeanStringObject {
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
static mut l_Lean_Meta_mkStringLitNeProof___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__57_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__58_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__56_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__58_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__58_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__57_value) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__58_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__59_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__59: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__60_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [103, 101, 116, 33, 73, 110, 116, 101, 114, 110, 97, 108, 0],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__60_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__61_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__2_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__61_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__61_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__60_value) as *mut LeanObject,
        1470318723338093382 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__61_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__62_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__62: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkStringLitNeProof___closed__63_value: LeanStringObject<19> =
    LeanStringObject {
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
            110, 101, 95, 111, 102, 95, 98, 101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
        ],
    };
static mut l_Lean_Meta_mkStringLitNeProof___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__63_value) as *mut LeanObject;
static l_Lean_Meta_mkStringLitNeProof___closed__64_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__50_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkStringLitNeProof___closed__64_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__64_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__63_value) as *mut LeanObject,
        1750192217580950936 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkStringLitNeProof___closed__64_value) as *mut LeanObject;
static mut l_Lean_Meta_mkStringLitNeProof___closed__65_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkStringLitNeProof___closed__65: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_mkStringLitNeProof___lam__0(
    mut v___x_361_: *mut LeanObject,
    mut v_type_362_: *mut LeanObject,
    mut v_inhabCharExpr_363_: *mut LeanObject,
    mut v_iExpr_364_: *mut LeanObject,
    mut v___x_365_: *mut LeanObject,
    mut v_lExpr_366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_367_ = l_Lean_mkApp4(
        v___x_361_,
        v_type_362_,
        v_inhabCharExpr_363_,
        v_lExpr_366_,
        v_iExpr_364_,
    );
    v___x_368_ = l_Lean_Expr_app___override(v___x_365_, v___x_367_);
    return v___x_368_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_372_: u32 = 0;
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = 65;
    v___x_373_ = lean_box_uint32(v___x_372_);
    return v___x_373_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(
    mut v_l_u2081_374_: *mut LeanObject,
    mut v_l_u2082_375_: *mut LeanObject,
    mut v_range_376_: *mut LeanObject,
    mut v_b_377_: *mut LeanObject,
    mut v_i_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: u8 = 0;
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u32 = 0;
    let mut v___x_392_: u32 = 0;
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_379_ = lean_ctor_get(v_range_376_, 1);
                v_step_380_ = lean_ctor_get(v_range_376_, 2);
                v___x_381_ = lean_nat_dec_lt(v_i_378_, v_stop_379_);
                if v___x_381_ == 0 {
                    lean_dec(v_i_378_);
                    lean_inc_ref(v_b_377_);
                    return v_b_377_;
                } else {
                    v___x_382_ = lean_box(0);
                    v___x_383_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0;
                    v___x_387_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
                    lean_inc_n(v_i_378_, 2);
                    v___x_388_ =
                        l_List_get_x21Internal___redArg(v___x_387_, v_l_u2081_374_, v_i_378_);
                    v___x_389_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
                    v___x_390_ =
                        l_List_get_x21Internal___redArg(v___x_389_, v_l_u2082_375_, v_i_378_);
                    v___x_391_ = lean_unbox_uint32(v___x_388_);
                    lean_dec(v___x_388_);
                    v___x_392_ = lean_unbox_uint32(v___x_390_);
                    lean_dec(v___x_390_);
                    v___x_393_ = lean_uint32_dec_eq(v___x_391_, v___x_392_);
                    if v___x_393_ == 0 {
                        if v___x_381_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_394_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_394_, 0, v_i_378_);
                            v___x_395_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_395_, 0, v___x_394_);
                            lean_ctor_set(v___x_395_, 1, v___x_382_);
                            return v___x_395_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_385_ = lean_nat_add(v_i_378_, v_step_380_);
                lean_dec(v_i_378_);
                v_b_377_ = v___x_383_;
                v_i_378_ = v___x_385_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed(
    mut v_l_u2081_396_: *mut LeanObject,
    mut v_l_u2082_397_: *mut LeanObject,
    mut v_range_398_: *mut LeanObject,
    mut v_b_399_: *mut LeanObject,
    mut v_i_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_401_: *mut LeanObject = core::ptr::null_mut();
    v_res_401_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_396_, v_l_u2082_397_, v_range_398_, v_b_399_, v_i_400_);
    lean_dec_ref(v_b_399_);
    lean_dec_ref(v_range_398_);
    lean_dec(v_l_u2082_397_);
    lean_dec(v_l_u2081_396_);
    return v_res_401_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_box(0);
    v___x_408_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2;
    v___x_409_ = l_Lean_mkConst(v___x_408_, v___x_407_);
    return v___x_409_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(
    mut v_nilFn_410_: *mut LeanObject,
    mut v_consFn_411_: *mut LeanObject,
    mut v_x_412_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_412_) == 0 {
        lean_dec_ref(v_consFn_411_);
        lean_inc_ref(v_nilFn_410_);
        return v_nilFn_410_;
    } else {
        let mut v_head_413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_416_: u32 = 0;
        let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        v_head_413_ = lean_ctor_get(v_x_412_, 0);
        v_tail_414_ = lean_ctor_get(v_x_412_, 1);
        v___x_415_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3);
        v___x_416_ = lean_unbox_uint32(v_head_413_);
        v___x_417_ = lean_uint32_to_nat(v___x_416_);
        v___x_418_ = l_Lean_mkRawNatLit(v___x_417_);
        v___x_419_ = l_Lean_Expr_app___override(v___x_415_, v___x_418_);
        lean_inc_ref(v_consFn_411_);
        v___x_420_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_410_, v_consFn_411_, v_tail_414_);
        v___x_421_ = l_Lean_mkAppB(v_consFn_411_, v___x_419_, v___x_420_);
        return v___x_421_;
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___boxed(
    mut v_nilFn_422_: *mut LeanObject,
    mut v_consFn_423_: *mut LeanObject,
    mut v_x_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_425_: *mut LeanObject = core::ptr::null_mut();
    v_res_425_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_422_, v_consFn_423_, v_x_424_);
    lean_dec(v_x_424_);
    lean_dec_ref(v_nilFn_422_);
    return v_res_425_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__1() -> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_box(0);
    v___x_429_ = l_Lean_Meta_mkStringLitNeProof___closed__0;
    v_type_430_ = l_Lean_mkConst(v___x_429_, v___x_428_);
    return v_type_430_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__6() -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_439_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_440_ = l_Lean_Meta_mkStringLitNeProof___closed__4;
    v___x_441_ = l_Lean_mkConst(v___x_440_, v___x_439_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__7() -> *mut LeanObject {
    let mut v_type_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_444_: *mut LeanObject = core::ptr::null_mut();
    v_type_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__1,
    );
    v___x_443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__6_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__6,
    );
    v_nil_444_ = l_Lean_Expr_app___override(v___x_443_, v_type_442_);
    return v_nil_444_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__10() -> *mut LeanObject {
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_450_ = l_Lean_Meta_mkStringLitNeProof___closed__9;
    v___x_451_ = l_Lean_mkConst(v___x_450_, v___x_449_);
    return v___x_451_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__11() -> *mut LeanObject {
    let mut v_type_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_454_: *mut LeanObject = core::ptr::null_mut();
    v_type_452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__1,
    );
    v___x_453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__10_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__10,
    );
    v_cons_454_ = l_Lean_Expr_app___override(v___x_453_, v_type_452_);
    return v_cons_454_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__14() -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strType_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_458_ = lean_box(0);
    v___x_459_ = l_Lean_Meta_mkStringLitNeProof___closed__13;
    v_strType_460_ = l_Lean_mkConst(v___x_459_, v___x_458_);
    return v_strType_460_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__17() -> *mut LeanObject {
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_465_ = lean_box(0);
    v___x_466_ = l_Lean_Meta_mkStringLitNeProof___closed__16;
    v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
    return v___x_467_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__20() -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_box(0);
    v___x_472_ = l_Lean_Meta_mkStringLitNeProof___closed__19;
    v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_471_);
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__23() -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = lean_box(0);
    v___x_479_ = l_Lean_Meta_mkStringLitNeProof___closed__22;
    v___x_480_ = l_Lean_mkConst(v___x_479_, v___x_478_);
    return v___x_480_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__25() -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_484_ = l_Lean_Meta_mkStringLitNeProof___closed__24;
    v___x_485_ = l_Lean_mkConst(v___x_484_, v___x_483_);
    return v___x_485_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__26() -> *mut LeanObject {
    let mut v_type_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_listCharTy_488_: *mut LeanObject = core::ptr::null_mut();
    v_type_486_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__1,
    );
    v___x_487_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__25_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__25,
    );
    v_listCharTy_488_ = l_Lean_Expr_app___override(v___x_487_, v_type_486_);
    return v_listCharTy_488_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__29() -> *mut LeanObject {
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_494_ = l_Lean_Meta_mkStringLitNeProof___closed__28;
    v___x_495_ = l_Lean_mkConst(v___x_494_, v___x_493_);
    return v___x_495_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__35() -> *mut LeanObject {
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v___x_504_ = lean_box(0);
    v___x_505_ = l_Lean_Level_succ___override(v___x_504_);
    return v___x_505_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__36() -> *mut LeanObject {
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_506_ = lean_box(0);
    v___x_507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__35_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__35,
    );
    v___x_508_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_508_, 0, v___x_507_);
    lean_ctor_set(v___x_508_, 1, v___x_506_);
    return v___x_508_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__37() -> *mut LeanObject {
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    v___x_509_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__36,
    );
    v___x_510_ = l_Lean_Meta_mkStringLitNeProof___closed__34;
    v___x_511_ = l_Lean_mkConst(v___x_510_, v___x_509_);
    return v___x_511_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__42() -> *mut LeanObject {
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    v___x_519_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_520_ = l_Lean_Meta_mkStringLitNeProof___closed__41;
    v___x_521_ = l_Lean_mkConst(v___x_520_, v___x_519_);
    return v___x_521_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__45() -> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    v___x_525_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__36,
    );
    v___x_526_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__35_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__35,
    );
    v___x_527_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_527_, 0, v___x_526_);
    lean_ctor_set(v___x_527_, 1, v___x_525_);
    return v___x_527_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__46() -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__45_once),
        _init_l_Lean_Meta_mkStringLitNeProof___closed__45,
    );
    v___x_529_ = l_Lean_Meta_mkStringLitNeProof___closed__44;
    v___x_530_ = l_Lean_mkConst(v___x_529_, v___x_528_);
    return v___x_530_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__49() -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inhabCharExpr_537_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ = lean_box(0);
    v___x_536_ = l_Lean_Meta_mkStringLitNeProof___closed__48;
    v_inhabCharExpr_537_ = l_Lean_mkConst(v___x_536_, v___x_535_);
    return v_inhabCharExpr_537_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__52() -> *mut LeanObject {
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natConst_543_: *mut LeanObject = core::ptr::null_mut();
    v___x_541_ = lean_box(0);
    v___x_542_ = l_Lean_Meta_mkStringLitNeProof___closed__51;
    v_natConst_543_ = l_Lean_mkConst(v___x_542_, v___x_541_);
    return v_natConst_543_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__55() -> *mut LeanObject {
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v___x_548_ = lean_box(0);
    v___x_549_ = l_Lean_Meta_mkStringLitNeProof___closed__54;
    v___x_550_ = l_Lean_mkConst(v___x_549_, v___x_548_);
    return v___x_550_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__59() -> *mut LeanObject {
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_556_ = lean_box(0);
    v___x_557_ = l_Lean_Meta_mkStringLitNeProof___closed__58;
    v___x_558_ = l_Lean_mkConst(v___x_557_, v___x_556_);
    return v___x_558_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__62() -> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Lean_Meta_mkStringLitNeProof___closed__5;
    v___x_564_ = l_Lean_Meta_mkStringLitNeProof___closed__61;
    v___x_565_ = l_Lean_mkConst(v___x_564_, v___x_563_);
    return v___x_565_;
}
pub unsafe fn _init_l_Lean_Meta_mkStringLitNeProof___closed__65() -> *mut LeanObject {
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    v___x_570_ = lean_box(0);
    v___x_571_ = l_Lean_Meta_mkStringLitNeProof___closed__64;
    v___x_572_ = l_Lean_mkConst(v___x_571_, v___x_570_);
    return v___x_572_;
}
pub unsafe fn l_Lean_Meta_mkStringLitNeProof(
    mut v_s_u2081_573_: *mut LeanObject,
    mut v_s_u2082_574_: *mut LeanObject,
    mut v_a_575_: *mut LeanObject,
    mut v_a_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_u2081_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_u2081Expr_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_u2082Expr_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_listNeProof_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strType_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strEq_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_listCharTy_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_619_: u32 = 0;
    let mut v_snd_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hdExpr_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tlExpr_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consNeNil_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_listEq_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u8 = 0;
    let mut v_nExpr_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dropFn_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dropL1_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dropL2_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dropEq_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrArgFn_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v_dropped_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u32 = 0;
    let mut v_dropped_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: u32 = 0;
    let mut v_inhabCharExpr_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natConst_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_iExpr_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projL1_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projFn_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projL2_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projEq_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrArgFn_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_l_u2081_580_ = lean_string_data(v_s_u2081_573_);
                v_l_u2082_581_ = lean_string_data(v_s_u2082_574_);
                v_type_582_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__1_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__1,
                );
                v_nil_583_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__7_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__7,
                );
                v___x_584_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__10_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__10,
                );
                v_cons_585_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__11_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__11,
                );
                v_l_u2081Expr_586_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_583_, v_cons_585_, v_l_u2081_580_);
                v_l_u2082Expr_587_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_583_, v_cons_585_, v_l_u2082_581_);
                v_listCharTy_610_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__26_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__26,
                );
                v___x_611_ = l_List_lengthTR___redArg(v_l_u2081_580_);
                v___x_612_ = l_List_lengthTR___redArg(v_l_u2082_581_);
                v___x_696_ = lean_nat_dec_le(v___x_611_, v___x_612_);
                if v___x_696_ == 0 {
                    lean_inc(v___x_612_);
                    v___y_688_ = v___x_612_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v___x_611_);
                    v___y_688_ = v___x_611_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v_strType_592_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__14_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__14,
                );
                v___x_593_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__17_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__17,
                );
                lean_inc_ref(v_l_u2081Expr_586_);
                v___x_594_ = l_Lean_Expr_app___override(v___x_593_, v_l_u2081Expr_586_);
                lean_inc_ref(v_l_u2082Expr_587_);
                v___x_595_ = l_Lean_Expr_app___override(v___x_593_, v_l_u2082Expr_587_);
                v_strEq_596_ = l_Lean_mkApp3(v___y_589_, v_strType_592_, v___x_594_, v___x_595_);
                v___x_597_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__20_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__20,
                );
                v___x_598_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__23),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__23_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__23,
                );
                v___x_599_ = l_Lean_mkAppB(v___x_598_, v_l_u2081Expr_586_, v_l_u2082Expr_587_);
                v___x_600_ = l_Lean_mkApp4(
                    v___x_597_,
                    v_strEq_596_,
                    v___y_590_,
                    v___x_599_,
                    v_listNeProof_591_,
                );
                v___x_601_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_601_, 0, v___x_600_);
                return v___x_601_;
            }
            2 => {
                v___x_608_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__20_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__20,
                );
                lean_inc_ref(v___y_606_);
                v___x_609_ =
                    l_Lean_mkApp4(v___x_608_, v___y_606_, v___y_603_, v___y_604_, v___y_607_);
                v___y_589_ = v___y_605_;
                v___y_590_ = v___y_606_;
                v_listNeProof_591_ = v___x_609_;
                state = 1;
                continue;
            }
            3 => {
                v___x_621_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3);
                v___x_622_ = lean_uint32_to_nat(v_fst_619_);
                v___x_623_ = l_Lean_mkRawNatLit(v___x_622_);
                v_hdExpr_624_ = l_Lean_Expr_app___override(v___x_621_, v___x_623_);
                v_tlExpr_625_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_583_, v_cons_585_, v_snd_620_);
                lean_dec(v_snd_620_);
                v___x_626_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__29),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__29_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__29,
                );
                lean_inc_ref(v_tlExpr_625_);
                lean_inc_ref(v_hdExpr_624_);
                v_consNeNil_627_ =
                    l_Lean_mkApp3(v___x_626_, v_type_582_, v_hdExpr_624_, v_tlExpr_625_);
                v___x_628_ = lean_nat_dec_le(v___x_611_, v___x_612_);
                lean_dec(v___x_612_);
                lean_dec(v___x_611_);
                if v___x_628_ == 0 {
                    lean_dec_ref(v_tlExpr_625_);
                    lean_dec_ref(v_hdExpr_624_);
                    v___y_603_ = v___y_614_;
                    v___y_604_ = v___y_615_;
                    v___y_605_ = v___y_616_;
                    v___y_606_ = v___y_618_;
                    v___y_607_ = v_consNeNil_627_;
                    state = 2;
                    continue;
                } else {
                    v___x_629_ = l_Lean_Meta_mkStringLitNeProof___closed__32;
                    lean_inc(v___y_617_);
                    v___x_630_ = l_Lean_mkConst(v___x_629_, v___y_617_);
                    v___x_631_ =
                        l_Lean_mkApp3(v___x_584_, v_type_582_, v_hdExpr_624_, v_tlExpr_625_);
                    v___x_632_ = l_Lean_mkApp4(
                        v___x_630_,
                        v_listCharTy_610_,
                        v___x_631_,
                        v_nil_583_,
                        v_consNeNil_627_,
                    );
                    v___y_603_ = v___y_614_;
                    v___y_604_ = v___y_615_;
                    v___y_605_ = v___y_616_;
                    v___y_606_ = v___y_618_;
                    v___y_607_ = v___x_632_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_637_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__36_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__36,
                );
                v___x_638_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__37),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__37_once),
                    _init_l_Lean_Meta_mkStringLitNeProof___closed__37,
                );
                lean_inc_ref(v_l_u2082Expr_587_);
                lean_inc_ref(v_l_u2081Expr_586_);
                v_listEq_639_ = l_Lean_mkApp3(
                    v___x_638_,
                    v_listCharTy_610_,
                    v_l_u2081Expr_586_,
                    v_l_u2082Expr_587_,
                );
                v___x_640_ = lean_nat_dec_lt(v___y_636_, v___y_635_);
                if v___x_640_ == 0 {
                    lean_dec(v___y_636_);
                    lean_inc(v___y_635_);
                    v_nExpr_641_ = l_Lean_mkNatLit(v___y_635_);
                    v___x_642_ = l_Lean_Meta_mkStringLitNeProof___closed__39;
                    v___x_643_ = 0;
                    v___x_644_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__42),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__42_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__42,
                    );
                    v___x_645_ = l_Lean_mkBVar(v___y_634_);
                    lean_inc_ref_n(v_nExpr_641_, 2);
                    v___x_646_ = l_Lean_mkApp3(v___x_644_, v_type_582_, v_nExpr_641_, v___x_645_);
                    v_dropFn_647_ =
                        l_Lean_mkLambda(v___x_642_, v___x_643_, v_listCharTy_610_, v___x_646_);
                    lean_inc_ref_n(v_l_u2081Expr_586_, 2);
                    v_dropL1_648_ =
                        l_Lean_mkApp3(v___x_644_, v_type_582_, v_nExpr_641_, v_l_u2081Expr_586_);
                    lean_inc_ref_n(v_l_u2082Expr_587_, 2);
                    v_dropL2_649_ =
                        l_Lean_mkApp3(v___x_644_, v_type_582_, v_nExpr_641_, v_l_u2082Expr_587_);
                    v_dropEq_650_ =
                        l_Lean_mkApp3(v___x_638_, v_listCharTy_610_, v_dropL1_648_, v_dropL2_649_);
                    v___x_651_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__46),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__46_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__46,
                    );
                    v_congrArgFn_652_ = l_Lean_mkApp5(
                        v___x_651_,
                        v_listCharTy_610_,
                        v_listCharTy_610_,
                        v_l_u2081Expr_586_,
                        v_l_u2082Expr_587_,
                        v_dropFn_647_,
                    );
                    v___x_653_ = lean_nat_dec_le(v___x_611_, v___x_612_);
                    if v___x_653_ == 0 {
                        lean_dec(v_l_u2082_581_);
                        v_dropped_654_ = l_List_drop___redArg(v___y_635_, v_l_u2081_580_);
                        lean_dec(v_l_u2081_580_);
                        v___x_655_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
                        v___x_656_ = l_List_head_x21___redArg(v___x_655_, v_dropped_654_);
                        v___x_657_ = l_List_tail_x21___redArg(v_dropped_654_);
                        lean_dec(v_dropped_654_);
                        v___x_658_ = lean_unbox_uint32(v___x_656_);
                        lean_dec(v___x_656_);
                        v___y_614_ = v_dropEq_650_;
                        v___y_615_ = v_congrArgFn_652_;
                        v___y_616_ = v___x_638_;
                        v___y_617_ = v___x_637_;
                        v___y_618_ = v_listEq_639_;
                        v_fst_619_ = v___x_658_;
                        v_snd_620_ = v___x_657_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_l_u2081_580_);
                        v_dropped_659_ = l_List_drop___redArg(v___y_635_, v_l_u2082_581_);
                        lean_dec(v_l_u2082_581_);
                        v___x_660_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
                        v___x_661_ = l_List_head_x21___redArg(v___x_660_, v_dropped_659_);
                        v___x_662_ = l_List_tail_x21___redArg(v_dropped_659_);
                        lean_dec(v_dropped_659_);
                        v___x_663_ = lean_unbox_uint32(v___x_661_);
                        lean_dec(v___x_661_);
                        v___y_614_ = v_dropEq_650_;
                        v___y_615_ = v_congrArgFn_652_;
                        v___y_616_ = v___x_638_;
                        v___y_617_ = v___x_637_;
                        v___y_618_ = v_listEq_639_;
                        v_fst_619_ = v___x_663_;
                        v_snd_620_ = v___x_662_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___y_635_);
                    lean_dec(v___x_612_);
                    lean_dec(v___x_611_);
                    lean_dec(v_l_u2082_581_);
                    lean_dec(v_l_u2081_580_);
                    v_inhabCharExpr_664_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__49),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__49_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__49,
                    );
                    v_natConst_665_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__52),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__52_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__52,
                    );
                    v___x_666_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__55),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__55_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__55,
                    );
                    v___x_667_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__59),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__59_once),
                        _init_l_Lean_Meta_mkStringLitNeProof___closed__59,
                    );
                    v___x_668_ =
                        l_Lean_Meta_mkEqRefl(v___x_667_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
                    if lean_obj_tag(v___x_668_) == 0 {
                        v_a_669_ = lean_ctor_get(v___x_668_, 0);
                        lean_inc(v_a_669_);
                        lean_dec_ref_known(v___x_668_, 1);
                        v_iExpr_670_ = l_Lean_mkNatLit(v___y_636_);
                        v___x_671_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__62),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkStringLitNeProof___closed__62_once
                            ),
                            _init_l_Lean_Meta_mkStringLitNeProof___closed__62,
                        );
                        lean_inc_ref_n(v_l_u2081Expr_586_, 2);
                        lean_inc_ref_n(v_iExpr_670_, 2);
                        v_projL1_672_ = l_Lean_Meta_mkStringLitNeProof___lam__0(
                            v___x_671_,
                            v_type_582_,
                            v_inhabCharExpr_664_,
                            v_iExpr_670_,
                            v___x_666_,
                            v_l_u2081Expr_586_,
                        );
                        v___x_673_ = l_Lean_Meta_mkStringLitNeProof___closed__39;
                        v___x_674_ = 0;
                        v___x_675_ = l_Lean_mkBVar(v___y_634_);
                        v___x_676_ = l_Lean_mkApp4(
                            v___x_671_,
                            v_type_582_,
                            v_inhabCharExpr_664_,
                            v___x_675_,
                            v_iExpr_670_,
                        );
                        v___x_677_ = l_Lean_Expr_app___override(v___x_666_, v___x_676_);
                        v_projFn_678_ =
                            l_Lean_mkLambda(v___x_673_, v___x_674_, v_listCharTy_610_, v___x_677_);
                        lean_inc_ref_n(v_l_u2082Expr_587_, 2);
                        v_projL2_679_ = l_Lean_Meta_mkStringLitNeProof___lam__0(
                            v___x_671_,
                            v_type_582_,
                            v_inhabCharExpr_664_,
                            v_iExpr_670_,
                            v___x_666_,
                            v_l_u2082Expr_587_,
                        );
                        lean_inc_ref(v_projL2_679_);
                        lean_inc_ref(v_projL1_672_);
                        v_projEq_680_ = l_Lean_mkApp3(
                            v___x_638_,
                            v_natConst_665_,
                            v_projL1_672_,
                            v_projL2_679_,
                        );
                        v___x_681_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__46),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkStringLitNeProof___closed__46_once
                            ),
                            _init_l_Lean_Meta_mkStringLitNeProof___closed__46,
                        );
                        v_congrArgFn_682_ = l_Lean_mkApp5(
                            v___x_681_,
                            v_listCharTy_610_,
                            v_natConst_665_,
                            v_l_u2081Expr_586_,
                            v_l_u2082Expr_587_,
                            v_projFn_678_,
                        );
                        v___x_683_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__65),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkStringLitNeProof___closed__65_once
                            ),
                            _init_l_Lean_Meta_mkStringLitNeProof___closed__65,
                        );
                        v___x_684_ =
                            l_Lean_mkApp3(v___x_683_, v_projL1_672_, v_projL2_679_, v_a_669_);
                        v___x_685_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkStringLitNeProof___closed__20),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkStringLitNeProof___closed__20_once
                            ),
                            _init_l_Lean_Meta_mkStringLitNeProof___closed__20,
                        );
                        lean_inc_ref(v_listEq_639_);
                        v___x_686_ = l_Lean_mkApp4(
                            v___x_685_,
                            v_listEq_639_,
                            v_projEq_680_,
                            v_congrArgFn_682_,
                            v___x_684_,
                        );
                        v___y_589_ = v___x_638_;
                        v___y_590_ = v_listEq_639_;
                        v_listNeProof_591_ = v___x_686_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_listEq_639_);
                        lean_dec(v___y_636_);
                        lean_dec(v___y_634_);
                        lean_dec_ref(v_l_u2082Expr_587_);
                        lean_dec_ref(v_l_u2081Expr_586_);
                        return v___x_668_;
                    }
                }
            }
            5 => {
                v___x_689_ = lean_unsigned_to_nat(0);
                v___x_690_ = lean_unsigned_to_nat(1);
                lean_inc(v___y_688_);
                v___x_691_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_691_, 0, v___x_689_);
                lean_ctor_set(v___x_691_, 1, v___y_688_);
                lean_ctor_set(v___x_691_, 2, v___x_690_);
                v___x_692_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0;
                v___x_693_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_580_, v_l_u2082_581_, v___x_691_, v___x_692_, v___x_689_);
                lean_dec_ref_known(v___x_691_, 3);
                v_fst_694_ = lean_ctor_get(v___x_693_, 0);
                lean_inc(v_fst_694_);
                lean_dec_ref(v___x_693_);
                if lean_obj_tag(v_fst_694_) == 0 {
                    lean_inc(v___y_688_);
                    v___y_634_ = v___x_689_;
                    v___y_635_ = v___y_688_;
                    v___y_636_ = v___y_688_;
                    state = 4;
                    continue;
                } else {
                    v_val_695_ = lean_ctor_get(v_fst_694_, 0);
                    lean_inc(v_val_695_);
                    lean_dec_ref_known(v_fst_694_, 1);
                    v___y_634_ = v___x_689_;
                    v___y_635_ = v___y_688_;
                    v___y_636_ = v_val_695_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkStringLitNeProof___boxed(
    mut v_s_u2081_697_: *mut LeanObject,
    mut v_s_u2082_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Lean_Meta_mkStringLitNeProof(
        v_s_u2081_697_,
        v_s_u2082_698_,
        v_a_699_,
        v_a_700_,
        v_a_701_,
        v_a_702_,
    );
    lean_dec(v_a_702_);
    lean_dec_ref(v_a_701_);
    lean_dec(v_a_700_);
    lean_dec_ref(v_a_699_);
    return v_res_704_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1(
    mut v_l_u2081_705_: *mut LeanObject,
    mut v_l_u2082_706_: *mut LeanObject,
    mut v_range_707_: *mut LeanObject,
    mut v_b_708_: *mut LeanObject,
    mut v_i_709_: *mut LeanObject,
    mut v_hs_710_: *mut LeanObject,
    mut v_hl_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_705_, v_l_u2082_706_, v_range_707_, v_b_708_, v_i_709_);
    return v___x_712_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___boxed(
    mut v_l_u2081_713_: *mut LeanObject,
    mut v_l_u2082_714_: *mut LeanObject,
    mut v_range_715_: *mut LeanObject,
    mut v_b_716_: *mut LeanObject,
    mut v_i_717_: *mut LeanObject,
    mut v_hs_718_: *mut LeanObject,
    mut v_hl_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1(v_l_u2081_713_, v_l_u2082_714_, v_range_715_, v_b_716_, v_i_717_, v_hs_718_, v_hl_719_);
    lean_dec_ref(v_b_716_);
    lean_dec_ref(v_range_715_);
    lean_dec(v_l_u2082_714_);
    lean_dec(v_l_u2081_713_);
    return v_res_720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_StringLitProof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1();
    lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_StringLitProof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_StringLitProof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_StringLitProof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_StringLitProof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_StringLitProof(builtin);
}

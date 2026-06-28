// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
// Imports: Init.Grind.Ordered.Linarith Lean.ToExpr
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Grind::Ordered::Linarith::{
    initialize_Init_Grind_Ordered_Linarith, runtime_initialize_Init_Grind_Ordered_Linarith,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::ToExpr::{
    initialize_Lean_ToExpr, l_Lean_instToExprInt_mkNat, runtime_initialize_Lean_ToExpr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value: LeanStringObject<6> =
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
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value: LeanStringObject<9> =
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
        m_data: [76, 105, 110, 97, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value: LeanStringObject<5> =
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
        m_data: [80, 111, 108, 121, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value)
                as *mut LeanObject,
            18086031845048846885 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value)
                as *mut LeanObject,
            12807349905836473418 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value: LeanStringObject<4> =
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
        m_data: [97, 100, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value)
                as *mut LeanObject,
            18086031845048846885 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value)
                as *mut LeanObject,
            16553785163089117636 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value: LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value: LeanStringObject<11> =
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
        m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value)
                as *mut LeanObject,
            6362876895233142233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Arith_Linear_ofPoly as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value)
                as *mut LeanObject,
            18086031845048846885 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instToExprPoly: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value: LeanStringObject<5> =
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
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value: LeanStringObject<5> =
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
        m_data: [122, 101, 114, 111, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value)
                as *mut LeanObject,
            323963303538781305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value: LeanStringObject<4> =
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
        m_data: [118, 97, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value)
                as *mut LeanObject,
            12362966294513913524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value)
                as *mut LeanObject,
            10398441587332774232 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value: LeanStringObject<4> =
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
        m_data: [115, 117, 98, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value)
                as *mut LeanObject,
            6057841110732436643 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value)
                as *mut LeanObject,
            1037563969353900954 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value: LeanStringObject<7> =
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
        m_data: [110, 97, 116, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value)
                as *mut LeanObject,
            2429510846301039410 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value: LeanStringObject<7> =
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
        m_data: [105, 110, 116, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value)
                as *mut LeanObject,
            1413842334117914769 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Arith_Linear_ofLinExpr as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value)
                as *mut LeanObject,
            17349746425441669063 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value)
                as *mut LeanObject,
            530968239397099113 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instToExprExpr: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6() -> *mut LeanObject {
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    v___x_227_ = lean_box(0);
    v___x_228_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5;
    v___x_229_ = l_Lean_mkConst(v___x_228_, v___x_227_);
    return v___x_229_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9() -> *mut LeanObject {
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    v___x_237_ = lean_box(0);
    v___x_238_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8;
    v___x_239_ = l_Lean_mkConst(v___x_238_, v___x_237_);
    return v___x_239_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10() -> *mut LeanObject {
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    v___x_240_ = lean_unsigned_to_nat(0);
    v___x_241_ = lean_nat_to_int(v___x_240_);
    return v___x_241_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14() -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = lean_unsigned_to_nat(0);
    v___x_248_ = l_Lean_Level_ofNat(v___x_247_);
    return v___x_248_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15() -> *mut LeanObject {
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    v___x_249_ = lean_box(0);
    v___x_250_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14,
    );
    v___x_251_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_251_, 0, v___x_250_);
    lean_ctor_set(v___x_251_, 1, v___x_249_);
    return v___x_251_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16() -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15,
    );
    v___x_253_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13;
    v___x_254_ = l_Lean_Expr_const___override(v___x_253_, v___x_252_);
    return v___x_254_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19() -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_258_ = lean_box(0);
    v___x_259_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18;
    v___x_260_ = l_Lean_Expr_const___override(v___x_259_, v___x_258_);
    return v___x_260_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22() -> *mut LeanObject {
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    v___x_265_ = lean_box(0);
    v___x_266_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21;
    v___x_267_ = l_Lean_Expr_const___override(v___x_266_, v___x_265_);
    return v___x_267_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofPoly(
    mut v_p_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_268_) == 0 {
                    v___x_269_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6,
                    );
                    return v___x_269_;
                } else {
                    v_k_270_ = lean_ctor_get(v_p_268_, 0);
                    lean_inc(v_k_270_);
                    v_v_271_ = lean_ctor_get(v_p_268_, 1);
                    lean_inc(v_v_271_);
                    v_p_272_ = lean_ctor_get(v_p_268_, 2);
                    lean_inc(v_p_272_);
                    lean_dec_ref_known(v_p_268_, 3);
                    v___x_273_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9,
                    );
                    v___x_279_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10,
                    );
                    v___x_280_ = lean_int_dec_le(v___x_279_, v_k_270_);
                    if v___x_280_ == 0 {
                        v___x_281_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16,
                        );
                        v___x_282_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19,
                        );
                        v___x_283_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22,
                        );
                        v___x_284_ = lean_int_neg(v_k_270_);
                        lean_dec(v_k_270_);
                        v___x_285_ = l_Int_toNat(v___x_284_);
                        lean_dec(v___x_284_);
                        v___x_286_ = l_Lean_instToExprInt_mkNat(v___x_285_);
                        v___x_287_ = l_Lean_mkApp3(v___x_281_, v___x_282_, v___x_283_, v___x_286_);
                        v___y_275_ = v___x_287_;
                        state = 1;
                        continue;
                    } else {
                        v___x_288_ = l_Int_toNat(v_k_270_);
                        lean_dec(v_k_270_);
                        v___x_289_ = l_Lean_instToExprInt_mkNat(v___x_288_);
                        v___y_275_ = v___x_289_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_276_ = l_Lean_mkNatLit(v_v_271_);
                v___x_277_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly(v_p_272_);
                v___x_278_ = l_Lean_mkApp3(v___x_273_, v___y_275_, v___x_276_, v___x_277_);
                return v___x_278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2() -> *mut LeanObject {
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_296_ = lean_box(0);
    v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1;
    v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
    return v___x_298_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3() -> *mut LeanObject {
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2,
    );
    v___x_300_ = l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0;
    v___x_301_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_301_, 0, v___x_300_);
    lean_ctor_set(v___x_301_, 1, v___x_299_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly() -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3,
    );
    return v___x_302_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3() -> *mut LeanObject {
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v___x_311_ = lean_box(0);
    v___x_312_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2;
    v___x_313_ = l_Lean_mkConst(v___x_312_, v___x_311_);
    return v___x_313_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6() -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = lean_box(0);
    v___x_322_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5;
    v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_321_);
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8() -> *mut LeanObject {
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_330_ = lean_box(0);
    v___x_331_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7;
    v___x_332_ = l_Lean_mkConst(v___x_331_, v___x_330_);
    return v___x_332_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = lean_box(0);
    v___x_341_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10;
    v___x_342_ = l_Lean_mkConst(v___x_341_, v___x_340_);
    return v___x_342_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13() -> *mut LeanObject {
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_349_ = lean_box(0);
    v___x_350_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12;
    v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_349_);
    return v___x_351_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16() -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_box(0);
    v___x_360_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15;
    v___x_361_ = l_Lean_mkConst(v___x_360_, v___x_359_);
    return v___x_361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19() -> *mut LeanObject {
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_369_ = lean_box(0);
    v___x_370_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18;
    v___x_371_ = l_Lean_mkConst(v___x_370_, v___x_369_);
    return v___x_371_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(
    mut v_e_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: u8 = 0;
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_372_) {
                0 => {
                    v___x_373_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3,
                    );
                    return v___x_373_;
                }
                1 => {
                    v_i_374_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_i_374_);
                    lean_dec_ref_known(v_e_372_, 1);
                    v___x_375_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6,
                    );
                    v___x_376_ = l_Lean_mkNatLit(v_i_374_);
                    v___x_377_ = l_Lean_Expr_app___override(v___x_375_, v___x_376_);
                    return v___x_377_;
                }
                2 => {
                    v_a_378_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_a_378_);
                    v_b_379_ = lean_ctor_get(v_e_372_, 1);
                    lean_inc(v_b_379_);
                    lean_dec_ref_known(v_e_372_, 2);
                    v___x_380_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8,
                    );
                    v___x_381_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_378_);
                    v___x_382_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_b_379_);
                    v___x_383_ = l_Lean_mkAppB(v___x_380_, v___x_381_, v___x_382_);
                    return v___x_383_;
                }
                3 => {
                    v_a_384_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_a_384_);
                    v_b_385_ = lean_ctor_get(v_e_372_, 1);
                    lean_inc(v_b_385_);
                    lean_dec_ref_known(v_e_372_, 2);
                    v___x_386_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11,
                    );
                    v___x_387_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_384_);
                    v___x_388_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_b_385_);
                    v___x_389_ = l_Lean_mkAppB(v___x_386_, v___x_387_, v___x_388_);
                    return v___x_389_;
                }
                4 => {
                    v_a_390_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_a_390_);
                    lean_dec_ref_known(v_e_372_, 1);
                    v___x_391_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13,
                    );
                    v___x_392_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_390_);
                    v___x_393_ = l_Lean_Expr_app___override(v___x_391_, v___x_392_);
                    return v___x_393_;
                }
                5 => {
                    v_k_394_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_k_394_);
                    v_a_395_ = lean_ctor_get(v_e_372_, 1);
                    lean_inc(v_a_395_);
                    lean_dec_ref_known(v_e_372_, 2);
                    v___x_396_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16,
                    );
                    v___x_397_ = l_Lean_mkNatLit(v_k_394_);
                    v___x_398_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_395_);
                    v___x_399_ = l_Lean_mkAppB(v___x_396_, v___x_397_, v___x_398_);
                    return v___x_399_;
                }
                _ => {
                    v_k_400_ = lean_ctor_get(v_e_372_, 0);
                    lean_inc(v_k_400_);
                    v_a_401_ = lean_ctor_get(v_e_372_, 1);
                    lean_inc(v_a_401_);
                    lean_dec_ref_known(v_e_372_, 2);
                    v___x_402_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19,
                    );
                    v___x_407_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10,
                    );
                    v___x_408_ = lean_int_dec_le(v___x_407_, v_k_400_);
                    if v___x_408_ == 0 {
                        v___x_409_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16,
                        );
                        v___x_410_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19,
                        );
                        v___x_411_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22,
                        );
                        v___x_412_ = lean_int_neg(v_k_400_);
                        lean_dec(v_k_400_);
                        v___x_413_ = l_Int_toNat(v___x_412_);
                        lean_dec(v___x_412_);
                        v___x_414_ = l_Lean_instToExprInt_mkNat(v___x_413_);
                        v___x_415_ = l_Lean_mkApp3(v___x_409_, v___x_410_, v___x_411_, v___x_414_);
                        v___y_404_ = v___x_415_;
                        state = 1;
                        continue;
                    } else {
                        v___x_416_ = l_Int_toNat(v_k_400_);
                        lean_dec(v_k_400_);
                        v___x_417_ = l_Lean_instToExprInt_mkNat(v___x_416_);
                        v___y_404_ = v___x_417_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_405_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_401_);
                v___x_406_ = l_Lean_mkAppB(v___x_402_, v___y_404_, v___x_405_);
                return v___x_406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2() -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_box(0);
    v___x_425_ = l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1;
    v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_424_);
    return v___x_426_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3() -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2,
    );
    v___x_428_ = l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0;
    v___x_429_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_429_, 0, v___x_428_);
    lean_ctor_set(v___x_429_, 1, v___x_427_);
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr() -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3,
    );
    return v___x_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Linear_instToExprPoly =
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly);
    l_Lean_Meta_Grind_Arith_Linear_instToExprExpr =
        _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
}

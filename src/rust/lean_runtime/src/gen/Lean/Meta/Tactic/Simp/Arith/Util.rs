// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Util
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Nat_mkType,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec_ref, lean_dec_ref_known, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_once, lean_obj_tag,
};
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value: LeanStringObject<5> =
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
        m_data: [115, 117, 99, 99, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__2_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__0_value)
                as *mut LeanObject,
            16112798088292836701 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__2_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__3_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value: LeanStringObject<5> =
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
        m_data: [72, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value: LeanStringObject<5> =
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
        m_data: [104, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__5_value)
                as *mut LeanObject,
            16856108565602861689 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__6_value)
                as *mut LeanObject,
            4187025665268973031 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value: LeanStringObject<5> =
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
        m_data: [72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value: LeanStringObject<5> =
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
        m_data: [104, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__8_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__9_value)
                as *mut LeanObject,
            1611444129324655608 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value: LeanStringObject<5> =
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
        m_data: [72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value: LeanStringObject<5> =
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
        m_data: [104, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__11_value)
                as *mut LeanObject,
            10393083817453678557 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__12_value)
                as *mut LeanObject,
            10680564408669940870 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__0_value)
                as *mut LeanObject,
            6695605208187598753 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value: LeanStringObject<3> =
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
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__2_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value: LeanStringObject<3> =
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
        m_data: [71, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value: LeanStringObject<3> =
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
        m_data: [103, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__4_value)
                as *mut LeanObject,
            1755019837031360842 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__5_value)
                as *mut LeanObject,
            5555145617058846791 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value: LeanStringObject<3> =
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
        m_data: [71, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value: LeanStringObject<3> =
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
        m_data: [103, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__7_value)
                as *mut LeanObject,
            2272833755566510320 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__8_value)
                as *mut LeanObject,
            9426339939459091439 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value: LeanStringObject<3> =
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
        m_data: [76, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value: LeanStringObject<3> =
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
        m_data: [108, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__10_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__11_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value: LeanStringObject<3> =
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
        m_data: [76, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value: LeanStringObject<3> =
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
        m_data: [108, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__13_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__14_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value: LeanStringObject<4> =
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
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__0_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value: LeanStringObject<4> =
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
        m_data: [68, 118, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value: LeanStringObject<4> =
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
        m_data: [100, 118, 100, 0],
    };
static mut l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__0_value)
                as *mut LeanObject,
            4493959381811283967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__1_value)
                as *mut LeanObject,
            1297950917268934889 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(
    mut v_type_203_: *mut LeanObject,
) -> u8 {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: u8 = 0;
    v___x_204_ = l_Lean_Expr_cleanupAnnotations(v_type_203_);
    v___x_205_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1;
    v___x_206_ = l_Lean_Expr_isConstOf(v___x_204_, v___x_205_);
    if v___x_206_ == 0 {
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: u8 = 0;
        v___x_207_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__3;
        v___x_208_ = l_Lean_Expr_isConstOf(v___x_204_, v___x_207_);
        lean_dec_ref(v___x_204_);
        return v___x_208_;
    } else {
        lean_dec_ref(v___x_204_);
        return v___x_206_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___boxed(
    mut v_type_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ =
        l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(
            v_type_209_,
        );
    v_r_211_ = lean_box((v_res_210_) as usize);
    return v_r_211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(
    mut v_type_212_: *mut LeanObject,
) -> u8 {
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    v___x_213_ = l_Lean_Expr_cleanupAnnotations(v_type_212_);
    v___x_214_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType___closed__1;
    v___x_215_ = l_Lean_Expr_isConstOf(v___x_213_, v___x_214_);
    lean_dec_ref(v___x_213_);
    return v___x_215_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType___boxed(
    mut v_type_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_217_: u8 = 0;
    let mut v_r_218_: *mut LeanObject = core::ptr::null_mut();
    v_res_217_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_type_216_);
    v_r_218_ = lean_box((v_res_217_) as usize);
    return v_r_218_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14() -> *mut LeanObject {
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    v___x_243_ = l_Lean_Nat_mkType;
    v___x_244_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_244_, 0, v___x_243_);
    return v___x_244_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(
    mut v_e_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: u8 = 0;
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u8 = 0;
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: u8 = 0;
    let mut v___x_262_: u8 = 0;
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: u8 = 0;
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: u8 = 0;
    let mut v___x_271_: u8 = 0;
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: u8 = 0;
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_256_ = l_Lean_Expr_cleanupAnnotations(v_e_245_);
                v___x_257_ = l_Lean_Expr_isApp(v___x_256_);
                if v___x_257_ == 0 {
                    lean_dec_ref(v___x_256_);
                    v___x_258_ = lean_box(0);
                    return v___x_258_;
                } else {
                    v___x_259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_256_);
                    v___x_260_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__1;
                    v___x_261_ = l_Lean_Expr_isConstOf(v___x_259_, v___x_260_);
                    if v___x_261_ == 0 {
                        v___x_262_ = l_Lean_Expr_isApp(v___x_259_);
                        if v___x_262_ == 0 {
                            lean_dec_ref(v___x_259_);
                            v___x_263_ = lean_box(0);
                            return v___x_263_;
                        } else {
                            v___x_264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_259_);
                            v___x_265_ = l_Lean_Expr_isApp(v___x_264_);
                            if v___x_265_ == 0 {
                                lean_dec_ref(v___x_264_);
                                v___x_266_ = lean_box(0);
                                return v___x_266_;
                            } else {
                                v_arg_267_ = lean_ctor_get(v___x_264_, 1);
                                lean_inc_ref(v_arg_267_);
                                v___x_268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_264_);
                                v___x_269_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__4;
                                v___x_270_ = l_Lean_Expr_isConstOf(v___x_268_, v___x_269_);
                                if v___x_270_ == 0 {
                                    lean_dec_ref(v_arg_267_);
                                    v___x_271_ = l_Lean_Expr_isApp(v___x_268_);
                                    if v___x_271_ == 0 {
                                        lean_dec_ref(v___x_268_);
                                        v___x_272_ = lean_box(0);
                                        return v___x_272_;
                                    } else {
                                        v___x_273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_268_);
                                        v___x_274_ = l_Lean_Expr_isApp(v___x_273_);
                                        if v___x_274_ == 0 {
                                            lean_dec_ref(v___x_273_);
                                            v___x_275_ = lean_box(0);
                                            return v___x_275_;
                                        } else {
                                            v___x_276_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_273_);
                                            v___x_277_ = l_Lean_Expr_isApp(v___x_276_);
                                            if v___x_277_ == 0 {
                                                lean_dec_ref(v___x_276_);
                                                v___x_278_ = lean_box(0);
                                                return v___x_278_;
                                            } else {
                                                v_arg_279_ = lean_ctor_get(v___x_276_, 1);
                                                lean_inc_ref(v_arg_279_);
                                                v___x_280_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_276_);
                                                v___x_281_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__7;
                                                v___x_282_ =
                                                    l_Lean_Expr_isConstOf(v___x_280_, v___x_281_);
                                                if v___x_282_ == 0 {
                                                    v___x_283_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__10;
                                                    v___x_284_ = l_Lean_Expr_isConstOf(
                                                        v___x_280_, v___x_283_,
                                                    );
                                                    if v___x_284_ == 0 {
                                                        v___x_285_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__13;
                                                        v___x_286_ = l_Lean_Expr_isConstOf(
                                                            v___x_280_, v___x_285_,
                                                        );
                                                        lean_dec_ref(v___x_280_);
                                                        if v___x_286_ == 0 {
                                                            lean_dec_ref(v_arg_279_);
                                                            v___x_287_ = lean_box(0);
                                                            return v___x_287_;
                                                        } else {
                                                            v_00_u03b1_252_ = v_arg_279_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_280_);
                                                        v_00_u03b1_252_ = v_arg_279_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_280_);
                                                    v_00_u03b1_247_ = v_arg_279_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_268_);
                                    v_00_u03b1_247_ = v_arg_267_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_259_);
                        v___x_288_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14_once
                            ),
                            _init_l_Lean_Meta_Simp_Arith_isLinearTerm_x3f___closed__14,
                        );
                        return v___x_288_;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_00_u03b1_247_);
                v___x_248_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedCommRingType(v_00_u03b1_247_);
                if v___x_248_ == 0 {
                    lean_dec_ref(v_00_u03b1_247_);
                    v___x_249_ = lean_box(0);
                    return v___x_249_;
                } else {
                    v___x_250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_250_, 0, v_00_u03b1_247_);
                    return v___x_250_;
                }
            }
            2 => {
                lean_inc_ref(v_00_u03b1_252_);
                v___x_253_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_00_u03b1_252_);
                if v___x_253_ == 0 {
                    lean_dec_ref(v_00_u03b1_252_);
                    v___x_254_ = lean_box(0);
                    return v___x_254_;
                } else {
                    v___x_255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_255_, 0, v_00_u03b1_252_);
                    return v___x_255_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearTerm(mut v_e_289_: *mut LeanObject) -> u8 {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Lean_Meta_Simp_Arith_isLinearTerm_x3f(v_e_289_);
    if lean_obj_tag(v___x_290_) == 0 {
        let mut v___x_291_: u8 = 0;
        v___x_291_ = 0;
        return v___x_291_;
    } else {
        let mut v___x_292_: u8 = 0;
        lean_dec_ref_known(v___x_290_, 1);
        v___x_292_ = 1;
        return v___x_292_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearTerm___boxed(
    mut v_e_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: u8 = 0;
    let mut v_r_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_e_293_);
    v_r_295_ = lean_box((v_res_294_) as usize);
    return v_r_295_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearPosCnstr(mut v_e_322_: *mut LeanObject) -> u8 {
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: u8 = 0;
    v___x_323_ = l_Lean_Expr_cleanupAnnotations(v_e_322_);
    v___x_324_ = l_Lean_Expr_isApp(v___x_323_);
    if v___x_324_ == 0 {
        lean_dec_ref(v___x_323_);
        return v___x_324_;
    } else {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_326_: u8 = 0;
        v___x_325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_323_);
        v___x_326_ = l_Lean_Expr_isApp(v___x_325_);
        if v___x_326_ == 0 {
            lean_dec_ref(v___x_325_);
            return v___x_326_;
        } else {
            let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_328_: u8 = 0;
            v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_325_);
            v___x_328_ = l_Lean_Expr_isApp(v___x_327_);
            if v___x_328_ == 0 {
                lean_dec_ref(v___x_327_);
                return v___x_328_;
            } else {
                let mut v_arg_329_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_332_: u8 = 0;
                v_arg_329_ = lean_ctor_get(v___x_327_, 1);
                lean_inc_ref(v_arg_329_);
                v___x_330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
                v___x_331_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__1;
                v___x_332_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_331_);
                if v___x_332_ == 0 {
                    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_334_: u8 = 0;
                    v___x_333_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__3;
                    v___x_334_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_333_);
                    if v___x_334_ == 0 {
                        let mut v___x_335_: u8 = 0;
                        lean_dec_ref(v_arg_329_);
                        v___x_335_ = l_Lean_Expr_isApp(v___x_330_);
                        if v___x_335_ == 0 {
                            lean_dec_ref(v___x_330_);
                            return v___x_335_;
                        } else {
                            let mut v_arg_336_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_339_: u8 = 0;
                            v_arg_336_ = lean_ctor_get(v___x_330_, 1);
                            lean_inc_ref(v_arg_336_);
                            v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_330_);
                            v___x_338_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__6;
                            v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
                            if v___x_339_ == 0 {
                                let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_341_: u8 = 0;
                                v___x_340_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__9;
                                v___x_341_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_340_);
                                if v___x_341_ == 0 {
                                    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_343_: u8 = 0;
                                    v___x_342_ =
                                        l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__12;
                                    v___x_343_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_342_);
                                    if v___x_343_ == 0 {
                                        let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_345_: u8 = 0;
                                        v___x_344_ =
                                            l_Lean_Meta_Simp_Arith_isLinearPosCnstr___closed__15;
                                        v___x_345_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_344_);
                                        lean_dec_ref(v___x_337_);
                                        if v___x_345_ == 0 {
                                            lean_dec_ref(v_arg_336_);
                                            return v___x_345_;
                                        } else {
                                            let mut v___x_346_: u8 = 0;
                                            v___x_346_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_336_);
                                            return v___x_346_;
                                        }
                                    } else {
                                        let mut v___x_347_: u8 = 0;
                                        lean_dec_ref(v___x_337_);
                                        v___x_347_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_336_);
                                        return v___x_347_;
                                    }
                                } else {
                                    let mut v___x_348_: u8 = 0;
                                    lean_dec_ref(v___x_337_);
                                    v___x_348_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_336_);
                                    return v___x_348_;
                                }
                            } else {
                                let mut v___x_349_: u8 = 0;
                                lean_dec_ref(v___x_337_);
                                v___x_349_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_336_);
                                return v___x_349_;
                            }
                        }
                    } else {
                        let mut v___x_350_: u8 = 0;
                        lean_dec_ref(v___x_330_);
                        v___x_350_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_329_);
                        return v___x_350_;
                    }
                } else {
                    let mut v___x_351_: u8 = 0;
                    lean_dec_ref(v___x_330_);
                    v___x_351_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_329_);
                    return v___x_351_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearPosCnstr___boxed(
    mut v_e_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_353_: u8 = 0;
    let mut v_r_354_: *mut LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_352_);
    v_r_354_ = lean_box((v_res_353_) as usize);
    return v_r_354_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearCnstr(mut v_e_358_: *mut LeanObject) -> u8 {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: u8 = 0;
    lean_inc_ref(v_e_358_);
    v___x_359_ = l_Lean_Expr_cleanupAnnotations(v_e_358_);
    v___x_360_ = l_Lean_Expr_isApp(v___x_359_);
    if v___x_360_ == 0 {
        let mut v___x_361_: u8 = 0;
        lean_dec_ref(v___x_359_);
        v___x_361_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_358_);
        return v___x_361_;
    } else {
        let mut v_arg_362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_365_: u8 = 0;
        v_arg_362_ = lean_ctor_get(v___x_359_, 1);
        lean_inc_ref(v_arg_362_);
        v___x_363_ = l_Lean_Expr_appFnCleanup___redArg(v___x_359_);
        v___x_364_ = l_Lean_Meta_Simp_Arith_isLinearCnstr___closed__1;
        v___x_365_ = l_Lean_Expr_isConstOf(v___x_363_, v___x_364_);
        lean_dec_ref(v___x_363_);
        if v___x_365_ == 0 {
            let mut v___x_366_: u8 = 0;
            lean_dec_ref(v_arg_362_);
            v___x_366_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_e_358_);
            return v___x_366_;
        } else {
            let mut v___x_367_: u8 = 0;
            lean_dec_ref(v_e_358_);
            v___x_367_ = l_Lean_Meta_Simp_Arith_isLinearPosCnstr(v_arg_362_);
            return v___x_367_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isLinearCnstr___boxed(
    mut v_e_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_369_: u8 = 0;
    let mut v_r_370_: *mut LeanObject = core::ptr::null_mut();
    v_res_369_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_e_368_);
    v_r_370_ = lean_box((v_res_369_) as usize);
    return v_r_370_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isDvdCnstr(mut v_e_376_: *mut LeanObject) -> u8 {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    v___x_377_ = l_Lean_Expr_cleanupAnnotations(v_e_376_);
    v___x_378_ = l_Lean_Expr_isApp(v___x_377_);
    if v___x_378_ == 0 {
        lean_dec_ref(v___x_377_);
        return v___x_378_;
    } else {
        let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_380_: u8 = 0;
        v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_377_);
        v___x_380_ = l_Lean_Expr_isApp(v___x_379_);
        if v___x_380_ == 0 {
            lean_dec_ref(v___x_379_);
            return v___x_380_;
        } else {
            let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_382_: u8 = 0;
            v___x_381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_379_);
            v___x_382_ = l_Lean_Expr_isApp(v___x_381_);
            if v___x_382_ == 0 {
                lean_dec_ref(v___x_381_);
                return v___x_382_;
            } else {
                let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_384_: u8 = 0;
                v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_381_);
                v___x_384_ = l_Lean_Expr_isApp(v___x_383_);
                if v___x_384_ == 0 {
                    lean_dec_ref(v___x_383_);
                    return v___x_384_;
                } else {
                    let mut v_arg_385_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_388_: u8 = 0;
                    v_arg_385_ = lean_ctor_get(v___x_383_, 1);
                    lean_inc_ref(v_arg_385_);
                    v___x_386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
                    v___x_387_ = l_Lean_Meta_Simp_Arith_isDvdCnstr___closed__2;
                    v___x_388_ = l_Lean_Expr_isConstOf(v___x_386_, v___x_387_);
                    lean_dec_ref(v___x_386_);
                    if v___x_388_ == 0 {
                        lean_dec_ref(v_arg_385_);
                        return v___x_388_;
                    } else {
                        let mut v___x_389_: u8 = 0;
                        v___x_389_ = l___private_Lean_Meta_Tactic_Simp_Arith_Util_0__Lean_Meta_Simp_Arith_isSupportedType(v_arg_385_);
                        return v___x_389_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_isDvdCnstr___boxed(
    mut v_e_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_391_: u8 = 0;
    let mut v_r_392_: *mut LeanObject = core::ptr::null_mut();
    v_res_391_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_e_390_);
    v_r_392_ = lean_box((v_res_391_) as usize);
    return v_r_392_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
}

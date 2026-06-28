// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isConstOf,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp7, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVExpr::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_eq;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [82, 101, 102, 108, 101, 99, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 102, 66, 111, 111, 108, 95, 99, 111, 110, 103, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value
            ) as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 102, 66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value)
            as *mut LeanObject,
        5394957827732845164 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value
            ) as *mut LeanObject,
            17737472716185871225 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 86, 80, 114, 101, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 101, 116, 76, 115, 98, 68, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value)
            as *mut LeanObject,
        18198180362361044236 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value)
            as *mut LeanObject,
        4649274213110965225 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 101, 113, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value) as *mut LeanObject,403369037444587699 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value) as *mut LeanObject,16815404653606075659 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 108, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value) as *mut LeanObject,403369037444587699 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value) as *mut LeanObject,13532434073858392211 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 105, 110, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_3:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value)
            as *mut LeanObject,
        18198180362361044236 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value
        ) as *mut LeanObject,
        9369798261105284388 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [66, 86, 66, 105, 110, 80, 114, 101, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [101, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_3:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value
        ) as *mut LeanObject,
        14358323385385135839 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value
        ) as *mut LeanObject,
        9171839772800810094 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 108, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value)
            as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value)
            as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_3:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value
        ) as *mut LeanObject,
        14358323385385135839 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value
        ) as *mut LeanObject,
        6679632329825533760 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 101, 116, 76, 115, 98, 68, 95, 99, 111, 110, 103, 114, 0]};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(
    mut v_width_529_: *mut LeanObject,
    mut v_expr_530_: *mut LeanObject,
    mut v_a_531_: *mut LeanObject,
    mut v___x_532_: *mut LeanObject,
    mut v___x_533_: *mut LeanObject,
    mut v___x_534_: *mut LeanObject,
    mut v___x_535_: *mut LeanObject,
    mut v___x_536_: *mut LeanObject,
    mut v_origExpr_537_: *mut LeanObject,
    mut v___y_538_: *mut LeanObject,
    mut v___y_539_: *mut LeanObject,
    mut v___y_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
    mut v___y_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___y_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_564_: u8 = 0;
    let mut v_a_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_568_: u8 = 0;
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_width_529_);
                v___x_544_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_529_,
                    v_expr_530_,
                    v___y_538_,
                    v___y_539_,
                    v___y_540_,
                    v___y_541_,
                    v___y_542_,
                );
                if lean_obj_tag(v___x_544_) == 0 {
                    v_a_545_ = lean_ctor_get(v___x_544_, 0);
                    lean_inc(v_a_545_);
                    lean_dec_ref_known(v___x_544_, 1);
                    v___x_546_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_a_531_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_,
                    );
                    if lean_obj_tag(v___x_546_) == 0 {
                        v_a_547_ = lean_ctor_get(v___x_546_, 0);
                        v_isSharedCheck_564_ = (!lean_is_exclusive(v___x_546_)) as u8;
                        if v_isSharedCheck_564_ == 0 {
                            v___x_549_ = v___x_546_;
                            v_isShared_550_ = v_isSharedCheck_564_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_547_);
                            lean_dec(v___x_546_);
                            v___x_549_ = lean_box(0);
                            v_isShared_550_ = v_isSharedCheck_564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_545_);
                        lean_dec_ref(v_origExpr_537_);
                        lean_dec(v___x_536_);
                        lean_dec_ref(v___x_535_);
                        lean_dec_ref(v___x_534_);
                        lean_dec_ref(v___x_533_);
                        lean_dec_ref(v___x_532_);
                        lean_dec(v_width_529_);
                        return v___x_546_;
                    }
                } else {
                    lean_dec_ref(v_origExpr_537_);
                    lean_dec(v___x_536_);
                    lean_dec_ref(v___x_535_);
                    lean_dec_ref(v___x_534_);
                    lean_dec_ref(v___x_533_);
                    lean_dec_ref(v___x_532_);
                    lean_dec_ref(v_a_531_);
                    lean_dec(v_width_529_);
                    v_a_565_ = lean_ctor_get(v___x_544_, 0);
                    v_isSharedCheck_572_ = (!lean_is_exclusive(v___x_544_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v___x_567_ = v___x_544_;
                        v_isShared_568_ = v_isSharedCheck_572_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_565_);
                        lean_dec(v___x_544_);
                        v___x_567_ = lean_box(0);
                        v_isShared_568_ = v_isSharedCheck_572_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_547_) == 0 {
                    lean_inc(v_a_545_);
                    v___x_562_ =
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v_width_529_, v_a_545_);
                    v___y_552_ = v___x_562_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_width_529_);
                    v_val_563_ = lean_ctor_get(v_a_547_, 0);
                    lean_inc(v_val_563_);
                    lean_dec_ref_known(v_a_547_, 1);
                    v___y_552_ = v_val_563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_553_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0;
                v___x_554_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1;
                v___x_555_ = l_Lean_Name_mkStr6(
                    v___x_532_, v___x_533_, v___x_534_, v___x_553_, v___x_535_, v___x_554_,
                );
                v___x_556_ = l_Lean_mkConst(v___x_555_, v___x_536_);
                v___x_557_ = l_Lean_mkApp3(v___x_556_, v_origExpr_537_, v_a_545_, v___y_552_);
                v___x_558_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_558_, 0, v___x_557_);
                if v_isShared_550_ == 0 {
                    lean_ctor_set(v___x_549_, 0, v___x_558_);
                    v___x_560_ = v___x_549_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_560_;
            }
            4 => {
                if v_isShared_568_ == 0 {
                    v___x_570_ = v___x_567_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
                    v___x_570_ = v_reuseFailAlloc_571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed(
    mut v_width_573_: *mut LeanObject,
    mut v_expr_574_: *mut LeanObject,
    mut v_a_575_: *mut LeanObject,
    mut v___x_576_: *mut LeanObject,
    mut v___x_577_: *mut LeanObject,
    mut v___x_578_: *mut LeanObject,
    mut v___x_579_: *mut LeanObject,
    mut v___x_580_: *mut LeanObject,
    mut v_origExpr_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
    mut v___y_584_: *mut LeanObject,
    mut v___y_585_: *mut LeanObject,
    mut v___y_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_588_: *mut LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(
        v_width_573_,
        v_expr_574_,
        v_a_575_,
        v___x_576_,
        v___x_577_,
        v___x_578_,
        v___x_579_,
        v___x_580_,
        v_origExpr_581_,
        v___y_582_,
        v___y_583_,
        v___y_584_,
        v___y_585_,
        v___y_586_,
    );
    lean_dec(v___y_586_);
    lean_dec_ref(v___y_585_);
    lean_dec(v___y_584_);
    lean_dec_ref(v___y_583_);
    lean_dec(v___y_582_);
    return v_res_588_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5()
-> *mut LeanObject {
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_597_ = lean_box(0);
    v___x_598_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4;
    v___x_599_ = l_Lean_mkConst(v___x_598_, v___x_597_);
    return v___x_599_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12()
-> *mut LeanObject {
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_611_ = lean_box(0);
    v___x_612_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11;
    v___x_613_ = l_Lean_mkConst(v___x_612_, v___x_611_);
    return v___x_613_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13()
-> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_unsigned_to_nat(1);
    v___x_615_ = l_Lean_mkNatLit(v___x_614_);
    return v___x_615_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14()
-> *mut LeanObject {
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_616_ = lean_unsigned_to_nat(0);
    v___x_617_ = l_Lean_mkNatLit(v___x_616_);
    return v___x_617_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(
    mut v_origExpr_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
    mut v_a_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_629_: u8 = 0;
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v_width_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_a_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_a_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_679_: u8 = 0;
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_623_);
                lean_inc_ref(v_a_622_);
                lean_inc(v_a_621_);
                lean_inc_ref(v_a_620_);
                lean_inc_ref(v_origExpr_618_);
                v___x_625_ =
                    lean_infer_type(v_origExpr_618_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
                if lean_obj_tag(v___x_625_) == 0 {
                    v_a_626_ = lean_ctor_get(v___x_625_, 0);
                    v_isSharedCheck_675_ = (!lean_is_exclusive(v___x_625_)) as u8;
                    if v_isSharedCheck_675_ == 0 {
                        v___x_628_ = v___x_625_;
                        v_isShared_629_ = v_isSharedCheck_675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_626_);
                        lean_dec(v___x_625_);
                        v___x_628_ = lean_box(0);
                        v_isShared_629_ = v_isSharedCheck_675_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_origExpr_618_);
                    v_a_676_ = lean_ctor_get(v___x_625_, 0);
                    v_isSharedCheck_683_ = (!lean_is_exclusive(v___x_625_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v___x_678_ = v___x_625_;
                        v_isShared_679_ = v_isSharedCheck_683_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_676_);
                        lean_dec(v___x_625_);
                        v___x_678_ = lean_box(0);
                        v_isShared_679_ = v_isSharedCheck_683_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_630_ = l_Lean_Expr_cleanupAnnotations(v_a_626_);
                v___x_631_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1;
                v___x_632_ = l_Lean_Expr_isConstOf(v___x_630_, v___x_631_);
                lean_dec_ref(v___x_630_);
                if v___x_632_ == 0 {
                    lean_dec_ref(v_origExpr_618_);
                    v___x_633_ = lean_box(0);
                    if v_isShared_629_ == 0 {
                        lean_ctor_set(v___x_628_, 0, v___x_633_);
                        v___x_635_ = v___x_628_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
                        v___x_635_ = v_reuseFailAlloc_636_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_628_);
                    v___x_637_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2;
                    v___x_638_ = lean_box(0);
                    v___x_639_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5,
                    );
                    lean_inc_ref(v_origExpr_618_);
                    v___x_640_ = l_Lean_Expr_app___override(v___x_639_, v_origExpr_618_);
                    v___x_641_ = lean_unsigned_to_nat(1);
                    v___x_642_ = 0;
                    v___x_643_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(
                        v___x_640_, v___x_641_, v___x_642_, v_a_619_, v_a_620_, v_a_621_, v_a_622_,
                        v_a_623_,
                    );
                    if lean_obj_tag(v___x_643_) == 0 {
                        v_a_644_ = lean_ctor_get(v___x_643_, 0);
                        v_isSharedCheck_666_ = (!lean_is_exclusive(v___x_643_)) as u8;
                        if v_isSharedCheck_666_ == 0 {
                            v___x_646_ = v___x_643_;
                            v_isShared_647_ = v_isSharedCheck_666_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_644_);
                            lean_dec(v___x_643_);
                            v___x_646_ = lean_box(0);
                            v_isShared_647_ = v_isSharedCheck_666_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_origExpr_618_);
                        v_a_667_ = lean_ctor_get(v___x_643_, 0);
                        v_isSharedCheck_674_ = (!lean_is_exclusive(v___x_643_)) as u8;
                        if v_isSharedCheck_674_ == 0 {
                            v___x_669_ = v___x_643_;
                            v_isShared_670_ = v_isSharedCheck_674_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_667_);
                            lean_dec(v___x_643_);
                            v___x_669_ = lean_box(0);
                            v_isShared_670_ = v_isSharedCheck_674_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_635_;
            }
            3 => {
                v_width_648_ = lean_ctor_get(v_a_644_, 0);
                lean_inc_n(v_width_648_, 2);
                v_bvExpr_649_ = lean_ctor_get(v_a_644_, 1);
                v_expr_650_ = lean_ctor_get(v_a_644_, 4);
                lean_inc_ref_n(v_expr_650_, 2);
                v___x_651_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_bvExpr_649_);
                v___x_652_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_652_, 0, v_width_648_);
                lean_ctor_set(v___x_652_, 1, v_bvExpr_649_);
                lean_ctor_set(v___x_652_, 2, v___x_651_);
                v___x_653_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6;
                v___x_654_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7;
                v___x_655_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8;
                lean_inc_ref(v_origExpr_618_);
                v___f_656_ = lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed
                        as *mut core::ffi::c_void,
                    15,
                    9,
                );
                lean_closure_set(v___f_656_, 0, v_width_648_);
                lean_closure_set(v___f_656_, 1, v_expr_650_);
                lean_closure_set(v___f_656_, 2, v_a_644_);
                lean_closure_set(v___f_656_, 3, v___x_653_);
                lean_closure_set(v___f_656_, 4, v___x_654_);
                lean_closure_set(v___f_656_, 5, v___x_655_);
                lean_closure_set(v___f_656_, 6, v___x_637_);
                lean_closure_set(v___f_656_, 7, v___x_638_);
                lean_closure_set(v___f_656_, 8, v_origExpr_618_);
                v___x_657_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12,
                );
                v___x_658_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13,
                );
                v___x_659_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14,
                );
                v___x_660_ = l_Lean_mkApp3(v___x_657_, v___x_658_, v_expr_650_, v___x_659_);
                v___x_661_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_661_, 0, v___x_652_);
                lean_ctor_set(v___x_661_, 1, v_origExpr_618_);
                lean_ctor_set(v___x_661_, 2, v___f_656_);
                lean_ctor_set(v___x_661_, 3, v___x_660_);
                v___x_662_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_662_, 0, v___x_661_);
                if v_isShared_647_ == 0 {
                    lean_ctor_set(v___x_646_, 0, v___x_662_);
                    v___x_664_ = v___x_646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
                    v___x_664_ = v_reuseFailAlloc_665_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_664_;
            }
            5 => {
                if v_isShared_670_ == 0 {
                    v___x_672_ = v___x_669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
                    v___x_672_ = v_reuseFailAlloc_673_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_672_;
            }
            7 => {
                if v_isShared_679_ == 0 {
                    v___x_681_ = v___x_678_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___boxed(
    mut v_origExpr_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_691_: *mut LeanObject = core::ptr::null_mut();
    v_res_691_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(
        v_origExpr_684_,
        v_a_685_,
        v_a_686_,
        v_a_687_,
        v_a_688_,
        v_a_689_,
    );
    lean_dec(v_a_689_);
    lean_dec_ref(v_a_688_);
    lean_dec(v_a_687_);
    lean_dec_ref(v_a_686_);
    lean_dec(v_a_685_);
    return v_res_691_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(
    mut v_pred_708_: u8,
) -> *mut LeanObject {
    if v_pred_708_ == 0 {
        let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
        v___x_709_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1;
        return v___x_709_;
    } else {
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        v___x_710_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3;
        return v___x_710_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___boxed(
    mut v_pred_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pred_boxed_712_: u8 = 0;
    let mut v_res_713_: *mut LeanObject = core::ptr::null_mut();
    v_pred_boxed_712_ = (lean_unbox(v_pred_711_) as u8);
    v_res_713_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_boxed_712_);
    return v_res_713_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(
    mut v___x_714_: *mut LeanObject,
    mut v_fst_715_: *mut LeanObject,
    mut v_fproof_716_: *mut LeanObject,
    mut v_snd_717_: *mut LeanObject,
    mut v_sproof_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_723_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut v_val_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_739_: u8 = 0;
    let mut v_val_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_744_: u8 = 0;
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_fproof_716_) == 0 {
                    lean_dec_ref(v_snd_717_);
                    if lean_obj_tag(v_sproof_718_) == 0 {
                        lean_dec_ref(v_fst_715_);
                        lean_dec(v___x_714_);
                        v___x_719_ = lean_box(0);
                        return v___x_719_;
                    } else {
                        v_val_720_ = lean_ctor_get(v_sproof_718_, 0);
                        v_isSharedCheck_729_ = (!lean_is_exclusive(v_sproof_718_)) as u8;
                        if v_isSharedCheck_729_ == 0 {
                            v___x_722_ = v_sproof_718_;
                            v_isShared_723_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_720_);
                            lean_dec(v_sproof_718_);
                            v___x_722_ = lean_box(0);
                            v_isShared_723_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fst_715_);
                    if lean_obj_tag(v_sproof_718_) == 0 {
                        v_val_730_ = lean_ctor_get(v_fproof_716_, 0);
                        v_isSharedCheck_739_ = (!lean_is_exclusive(v_fproof_716_)) as u8;
                        if v_isSharedCheck_739_ == 0 {
                            v___x_732_ = v_fproof_716_;
                            v_isShared_733_ = v_isSharedCheck_739_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_730_);
                            lean_dec(v_fproof_716_);
                            v___x_732_ = lean_box(0);
                            v_isShared_733_ = v_isSharedCheck_739_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_snd_717_);
                        lean_dec(v___x_714_);
                        v_val_740_ = lean_ctor_get(v_fproof_716_, 0);
                        lean_inc(v_val_740_);
                        lean_dec_ref_known(v_fproof_716_, 1);
                        v_val_741_ = lean_ctor_get(v_sproof_718_, 0);
                        v_isSharedCheck_749_ = (!lean_is_exclusive(v_sproof_718_)) as u8;
                        if v_isSharedCheck_749_ == 0 {
                            v___x_743_ = v_sproof_718_;
                            v_isShared_744_ = v_isSharedCheck_749_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_741_);
                            lean_dec(v_sproof_718_);
                            v___x_743_ = lean_box(0);
                            v_isShared_744_ = v_isSharedCheck_749_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_724_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_714_, v_fst_715_);
                v___x_725_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_725_, 0, v___x_724_);
                lean_ctor_set(v___x_725_, 1, v_val_720_);
                if v_isShared_723_ == 0 {
                    lean_ctor_set(v___x_722_, 0, v___x_725_);
                    v___x_727_ = v___x_722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
                    v___x_727_ = v_reuseFailAlloc_728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_727_;
            }
            3 => {
                v___x_734_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_714_, v_snd_717_);
                v___x_735_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_735_, 0, v_val_730_);
                lean_ctor_set(v___x_735_, 1, v___x_734_);
                if v_isShared_733_ == 0 {
                    lean_ctor_set(v___x_732_, 0, v___x_735_);
                    v___x_737_ = v___x_732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
                    v___x_737_ = v_reuseFailAlloc_738_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_737_;
            }
            5 => {
                v___x_745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_745_, 0, v_val_740_);
                lean_ctor_set(v___x_745_, 1, v_val_741_);
                if v_isShared_744_ == 0 {
                    lean_ctor_set(v___x_743_, 0, v___x_745_);
                    v___x_747_ = v___x_743_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
                    v___x_747_ = v_reuseFailAlloc_748_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(
    mut v_width_750_: *mut LeanObject,
    mut v_expr_751_: *mut LeanObject,
    mut v_width_752_: *mut LeanObject,
    mut v_expr_753_: *mut LeanObject,
    mut v_lhs_754_: *mut LeanObject,
    mut v_rhs_755_: *mut LeanObject,
    mut v_congrThm_756_: *mut LeanObject,
    mut v___x_757_: *mut LeanObject,
    mut v___x_758_: *mut LeanObject,
    mut v_lhsExpr_759_: *mut LeanObject,
    mut v_rhsExpr_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v_fst_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_793_: u8 = 0;
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_798_: u8 = 0;
    let mut v_a_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut v_a_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_width_750_);
                v___x_767_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_750_,
                    v_expr_751_,
                    v___y_761_,
                    v___y_762_,
                    v___y_763_,
                    v___y_764_,
                    v___y_765_,
                );
                if lean_obj_tag(v___x_767_) == 0 {
                    v_a_768_ = lean_ctor_get(v___x_767_, 0);
                    lean_inc(v_a_768_);
                    lean_dec_ref_known(v___x_767_, 1);
                    v___x_769_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                        v_width_752_,
                        v_expr_753_,
                        v___y_761_,
                        v___y_762_,
                        v___y_763_,
                        v___y_764_,
                        v___y_765_,
                    );
                    if lean_obj_tag(v___x_769_) == 0 {
                        v_a_770_ = lean_ctor_get(v___x_769_, 0);
                        lean_inc(v_a_770_);
                        lean_dec_ref_known(v___x_769_, 1);
                        v___x_771_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                            v_lhs_754_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_,
                        );
                        if lean_obj_tag(v___x_771_) == 0 {
                            v_a_772_ = lean_ctor_get(v___x_771_, 0);
                            lean_inc(v_a_772_);
                            lean_dec_ref_known(v___x_771_, 1);
                            v___x_773_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                                v_rhs_755_, v___y_761_, v___y_762_, v___y_763_, v___y_764_,
                                v___y_765_,
                            );
                            if lean_obj_tag(v___x_773_) == 0 {
                                v_a_774_ = lean_ctor_get(v___x_773_, 0);
                                v_isSharedCheck_798_ = (!lean_is_exclusive(v___x_773_)) as u8;
                                if v_isSharedCheck_798_ == 0 {
                                    v___x_776_ = v___x_773_;
                                    v_isShared_777_ = v_isSharedCheck_798_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_774_);
                                    lean_dec(v___x_773_);
                                    v___x_776_ = lean_box(0);
                                    v_isShared_777_ = v_isSharedCheck_798_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_772_);
                                lean_dec(v_a_770_);
                                lean_dec(v_a_768_);
                                lean_dec_ref(v_rhsExpr_760_);
                                lean_dec_ref(v_lhsExpr_759_);
                                lean_dec_ref(v___x_758_);
                                lean_dec(v___x_757_);
                                lean_dec(v_congrThm_756_);
                                lean_dec(v_width_750_);
                                return v___x_773_;
                            }
                        } else {
                            lean_dec(v_a_770_);
                            lean_dec(v_a_768_);
                            lean_dec_ref(v_rhsExpr_760_);
                            lean_dec_ref(v_lhsExpr_759_);
                            lean_dec_ref(v___x_758_);
                            lean_dec(v___x_757_);
                            lean_dec(v_congrThm_756_);
                            lean_dec_ref(v_rhs_755_);
                            lean_dec(v_width_750_);
                            return v___x_771_;
                        }
                    } else {
                        lean_dec(v_a_768_);
                        lean_dec_ref(v_rhsExpr_760_);
                        lean_dec_ref(v_lhsExpr_759_);
                        lean_dec_ref(v___x_758_);
                        lean_dec(v___x_757_);
                        lean_dec(v_congrThm_756_);
                        lean_dec_ref(v_rhs_755_);
                        lean_dec_ref(v_lhs_754_);
                        lean_dec(v_width_750_);
                        v_a_799_ = lean_ctor_get(v___x_769_, 0);
                        v_isSharedCheck_806_ = (!lean_is_exclusive(v___x_769_)) as u8;
                        if v_isSharedCheck_806_ == 0 {
                            v___x_801_ = v___x_769_;
                            v_isShared_802_ = v_isSharedCheck_806_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_799_);
                            lean_dec(v___x_769_);
                            v___x_801_ = lean_box(0);
                            v_isShared_802_ = v_isSharedCheck_806_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhsExpr_760_);
                    lean_dec_ref(v_lhsExpr_759_);
                    lean_dec_ref(v___x_758_);
                    lean_dec(v___x_757_);
                    lean_dec(v_congrThm_756_);
                    lean_dec_ref(v_rhs_755_);
                    lean_dec_ref(v_lhs_754_);
                    lean_dec_ref(v_expr_753_);
                    lean_dec(v_width_752_);
                    lean_dec(v_width_750_);
                    v_a_807_ = lean_ctor_get(v___x_767_, 0);
                    v_isSharedCheck_814_ = (!lean_is_exclusive(v___x_767_)) as u8;
                    if v_isSharedCheck_814_ == 0 {
                        v___x_809_ = v___x_767_;
                        v_isShared_810_ = v_isSharedCheck_814_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_807_);
                        lean_dec(v___x_767_);
                        v___x_809_ = lean_box(0);
                        v_isShared_810_ = v_isSharedCheck_814_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_770_);
                lean_inc(v_a_768_);
                v___x_778_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(v_width_750_, v_a_768_, v_a_772_, v_a_770_, v_a_774_);
                if lean_obj_tag(v___x_778_) == 1 {
                    v_val_779_ = lean_ctor_get(v___x_778_, 0);
                    v_isSharedCheck_793_ = (!lean_is_exclusive(v___x_778_)) as u8;
                    if v_isSharedCheck_793_ == 0 {
                        v___x_781_ = v___x_778_;
                        v_isShared_782_ = v_isSharedCheck_793_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_779_);
                        lean_dec(v___x_778_);
                        v___x_781_ = lean_box(0);
                        v_isShared_782_ = v_isSharedCheck_793_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_778_);
                    lean_dec(v_a_770_);
                    lean_dec(v_a_768_);
                    lean_dec_ref(v_rhsExpr_760_);
                    lean_dec_ref(v_lhsExpr_759_);
                    lean_dec_ref(v___x_758_);
                    lean_dec(v___x_757_);
                    lean_dec(v_congrThm_756_);
                    v___x_794_ = lean_box(0);
                    if v_isShared_777_ == 0 {
                        lean_ctor_set(v___x_776_, 0, v___x_794_);
                        v___x_796_ = v___x_776_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
                        v___x_796_ = v_reuseFailAlloc_797_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_783_ = lean_ctor_get(v_val_779_, 0);
                lean_inc(v_fst_783_);
                v_snd_784_ = lean_ctor_get(v_val_779_, 1);
                lean_inc(v_snd_784_);
                lean_dec(v_val_779_);
                v___x_785_ = l_Lean_mkConst(v_congrThm_756_, v___x_757_);
                v___x_786_ = l_Lean_mkApp7(
                    v___x_785_,
                    v___x_758_,
                    v_lhsExpr_759_,
                    v_rhsExpr_760_,
                    v_a_768_,
                    v_a_770_,
                    v_fst_783_,
                    v_snd_784_,
                );
                if v_isShared_782_ == 0 {
                    lean_ctor_set(v___x_781_, 0, v___x_786_);
                    v___x_788_ = v___x_781_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
                    v___x_788_ = v_reuseFailAlloc_792_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_777_ == 0 {
                    lean_ctor_set(v___x_776_, 0, v___x_788_);
                    v___x_790_ = v___x_776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
                    v___x_790_ = v_reuseFailAlloc_791_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_790_;
            }
            5 => {
                return v___x_796_;
            }
            6 => {
                if v_isShared_802_ == 0 {
                    v___x_804_ = v___x_801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
                    v___x_804_ = v_reuseFailAlloc_805_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_804_;
            }
            8 => {
                if v_isShared_810_ == 0 {
                    v___x_812_ = v___x_809_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
                    v___x_812_ = v_reuseFailAlloc_813_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_width_815_: *mut LeanObject = *_args.add(0);
    let mut v_expr_816_: *mut LeanObject = *_args.add(1);
    let mut v_width_817_: *mut LeanObject = *_args.add(2);
    let mut v_expr_818_: *mut LeanObject = *_args.add(3);
    let mut v_lhs_819_: *mut LeanObject = *_args.add(4);
    let mut v_rhs_820_: *mut LeanObject = *_args.add(5);
    let mut v_congrThm_821_: *mut LeanObject = *_args.add(6);
    let mut v___x_822_: *mut LeanObject = *_args.add(7);
    let mut v___x_823_: *mut LeanObject = *_args.add(8);
    let mut v_lhsExpr_824_: *mut LeanObject = *_args.add(9);
    let mut v_rhsExpr_825_: *mut LeanObject = *_args.add(10);
    let mut v___y_826_: *mut LeanObject = *_args.add(11);
    let mut v___y_827_: *mut LeanObject = *_args.add(12);
    let mut v___y_828_: *mut LeanObject = *_args.add(13);
    let mut v___y_829_: *mut LeanObject = *_args.add(14);
    let mut v___y_830_: *mut LeanObject = *_args.add(15);
    let mut v___y_831_: *mut LeanObject = *_args.add(16);
    let mut v_res_832_: *mut LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(
        v_width_815_,
        v_expr_816_,
        v_width_817_,
        v_expr_818_,
        v_lhs_819_,
        v_rhs_820_,
        v_congrThm_821_,
        v___x_822_,
        v___x_823_,
        v_lhsExpr_824_,
        v_rhsExpr_825_,
        v___y_826_,
        v___y_827_,
        v___y_828_,
        v___y_829_,
        v___y_830_,
    );
    lean_dec(v___y_830_);
    lean_dec_ref(v___y_829_);
    lean_dec(v___y_828_);
    lean_dec_ref(v___y_827_);
    lean_dec(v___y_826_);
    return v_res_832_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = lean_box(0);
    v___x_841_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1;
    v___x_842_ = l_Lean_mkConst(v___x_841_, v___x_840_);
    return v___x_842_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_851_ = lean_box(0);
    v___x_852_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5;
    v___x_853_ = l_Lean_mkConst(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = lean_box(0);
    v___x_862_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8;
    v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_861_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
    mut v_lhs_864_: *mut LeanObject,
    mut v_rhs_865_: *mut LeanObject,
    mut v_lhsExpr_866_: *mut LeanObject,
    mut v_rhsExpr_867_: *mut LeanObject,
    mut v_pred_868_: u8,
    mut v_origExpr_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_width_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_width_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrThm_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_width_871_ = lean_ctor_get(v_lhs_864_, 0);
                lean_inc(v_width_871_);
                v_bvExpr_872_ = lean_ctor_get(v_lhs_864_, 1);
                v_expr_873_ = lean_ctor_get(v_lhs_864_, 4);
                lean_inc_ref(v_expr_873_);
                v_width_874_ = lean_ctor_get(v_rhs_865_, 0);
                lean_inc(v_width_874_);
                v_bvExpr_875_ = lean_ctor_get(v_rhs_865_, 1);
                v_expr_876_ = lean_ctor_get(v_rhs_865_, 4);
                lean_inc_ref(v_expr_876_);
                v___x_877_ = lean_nat_dec_eq(v_width_871_, v_width_874_);
                if v___x_877_ == 0 {
                    lean_dec_ref(v_expr_876_);
                    lean_dec(v_width_874_);
                    lean_dec_ref(v_expr_873_);
                    lean_dec(v_width_871_);
                    lean_dec_ref(v_origExpr_869_);
                    lean_dec_ref(v_rhsExpr_867_);
                    lean_dec_ref(v_lhsExpr_866_);
                    lean_dec_ref(v_rhs_865_);
                    lean_dec_ref(v_lhs_864_);
                    v___x_878_ = lean_box(0);
                    v___x_879_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_879_, 0, v___x_878_);
                    return v___x_879_;
                } else {
                    v_congrThm_880_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_868_);
                    lean_inc_ref(v_bvExpr_875_);
                    lean_inc_ref(v_bvExpr_872_);
                    lean_inc_n(v_width_871_, 2);
                    v_bvExpr_881_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_bvExpr_881_, 0, v_width_871_);
                    lean_ctor_set(v_bvExpr_881_, 1, v_bvExpr_872_);
                    lean_ctor_set(v_bvExpr_881_, 2, v_bvExpr_875_);
                    lean_ctor_set_uint8(
                        v_bvExpr_881_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_pred_868_,
                    );
                    v___x_882_ = lean_box(0);
                    v___x_883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2);
                    v___x_884_ = l_Lean_mkNatLit(v_width_871_);
                    lean_inc_ref(v___x_884_);
                    lean_inc_ref(v_expr_876_);
                    lean_inc_ref(v_expr_873_);
                    v_proof_885_ = lean_alloc_closure(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed as *mut core::ffi::c_void, 17, 11);
                    lean_closure_set(v_proof_885_, 0, v_width_871_);
                    lean_closure_set(v_proof_885_, 1, v_expr_873_);
                    lean_closure_set(v_proof_885_, 2, v_width_874_);
                    lean_closure_set(v_proof_885_, 3, v_expr_876_);
                    lean_closure_set(v_proof_885_, 4, v_lhs_864_);
                    lean_closure_set(v_proof_885_, 5, v_rhs_865_);
                    lean_closure_set(v_proof_885_, 6, v_congrThm_880_);
                    lean_closure_set(v_proof_885_, 7, v___x_882_);
                    lean_closure_set(v_proof_885_, 8, v___x_884_);
                    lean_closure_set(v_proof_885_, 9, v_lhsExpr_866_);
                    lean_closure_set(v_proof_885_, 10, v_rhsExpr_867_);
                    if v_pred_868_ == 0 {
                        v___x_892_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6);
                        v___y_887_ = v___x_892_;
                        state = 1;
                        continue;
                    } else {
                        v___x_893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9);
                        v___y_887_ = v___x_893_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_887_);
                v_expr_888_ =
                    l_Lean_mkApp4(v___x_883_, v___x_884_, v_expr_873_, v___y_887_, v_expr_876_);
                v___x_889_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_889_, 0, v_bvExpr_881_);
                lean_ctor_set(v___x_889_, 1, v_origExpr_869_);
                lean_ctor_set(v___x_889_, 2, v_proof_885_);
                lean_ctor_set(v___x_889_, 3, v_expr_888_);
                v___x_890_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_890_, 0, v___x_889_);
                v___x_891_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_891_, 0, v___x_890_);
                return v___x_891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___boxed(
    mut v_lhs_894_: *mut LeanObject,
    mut v_rhs_895_: *mut LeanObject,
    mut v_lhsExpr_896_: *mut LeanObject,
    mut v_rhsExpr_897_: *mut LeanObject,
    mut v_pred_898_: *mut LeanObject,
    mut v_origExpr_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pred_boxed_901_: u8 = 0;
    let mut v_res_902_: *mut LeanObject = core::ptr::null_mut();
    v_pred_boxed_901_ = (lean_unbox(v_pred_898_) as u8);
    v_res_902_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
        v_lhs_894_,
        v_rhs_895_,
        v_lhsExpr_896_,
        v_rhsExpr_897_,
        v_pred_boxed_901_,
        v_origExpr_899_,
    );
    return v_res_902_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(
    mut v_lhs_903_: *mut LeanObject,
    mut v_rhs_904_: *mut LeanObject,
    mut v_lhsExpr_905_: *mut LeanObject,
    mut v_rhsExpr_906_: *mut LeanObject,
    mut v_pred_907_: u8,
    mut v_origExpr_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_a_910_: *mut LeanObject,
    mut v_a_911_: *mut LeanObject,
    mut v_a_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
        v_lhs_903_,
        v_rhs_904_,
        v_lhsExpr_905_,
        v_rhsExpr_906_,
        v_pred_907_,
        v_origExpr_908_,
    );
    return v___x_915_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___boxed(
    mut v_lhs_916_: *mut LeanObject,
    mut v_rhs_917_: *mut LeanObject,
    mut v_lhsExpr_918_: *mut LeanObject,
    mut v_rhsExpr_919_: *mut LeanObject,
    mut v_pred_920_: *mut LeanObject,
    mut v_origExpr_921_: *mut LeanObject,
    mut v_a_922_: *mut LeanObject,
    mut v_a_923_: *mut LeanObject,
    mut v_a_924_: *mut LeanObject,
    mut v_a_925_: *mut LeanObject,
    mut v_a_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pred_boxed_928_: u8 = 0;
    let mut v_res_929_: *mut LeanObject = core::ptr::null_mut();
    v_pred_boxed_928_ = (lean_unbox(v_pred_920_) as u8);
    v_res_929_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(
        v_lhs_916_,
        v_rhs_917_,
        v_lhsExpr_918_,
        v_rhsExpr_919_,
        v_pred_boxed_928_,
        v_origExpr_921_,
        v_a_922_,
        v_a_923_,
        v_a_924_,
        v_a_925_,
        v_a_926_,
    );
    lean_dec(v_a_926_);
    lean_dec_ref(v_a_925_);
    lean_dec(v_a_924_);
    lean_dec_ref(v_a_923_);
    lean_dec(v_a_922_);
    return v_res_929_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(
    mut v_sub_931_: *mut LeanObject,
    mut v_width_932_: *mut LeanObject,
    mut v_expr_933_: *mut LeanObject,
    mut v___x_934_: *mut LeanObject,
    mut v___x_935_: *mut LeanObject,
    mut v___x_936_: *mut LeanObject,
    mut v___x_937_: *mut LeanObject,
    mut v_idxExpr_938_: *mut LeanObject,
    mut v___x_939_: *mut LeanObject,
    mut v_subExpr_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
    mut v___y_942_: *mut LeanObject,
    mut v___y_943_: *mut LeanObject,
    mut v___y_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_951_: u8 = 0;
    let mut v_val_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_955_: u8 = 0;
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_a_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_981_: u8 = 0;
    let mut v_isSharedCheck_982_: u8 = 0;
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_947_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                    v_sub_931_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_,
                );
                if lean_obj_tag(v___x_947_) == 0 {
                    v_a_948_ = lean_ctor_get(v___x_947_, 0);
                    v_isSharedCheck_987_ = (!lean_is_exclusive(v___x_947_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v___x_950_ = v___x_947_;
                        v_isShared_951_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_948_);
                        lean_dec(v___x_947_);
                        v___x_950_ = lean_box(0);
                        v_isShared_951_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_subExpr_940_);
                    lean_dec_ref(v___x_939_);
                    lean_dec_ref(v_idxExpr_938_);
                    lean_dec(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    lean_dec_ref(v_expr_933_);
                    lean_dec(v_width_932_);
                    return v___x_947_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_948_) == 1 {
                    lean_del_object(v___x_950_);
                    v_val_952_ = lean_ctor_get(v_a_948_, 0);
                    v_isSharedCheck_982_ = (!lean_is_exclusive(v_a_948_)) as u8;
                    if v_isSharedCheck_982_ == 0 {
                        v___x_954_ = v_a_948_;
                        v_isShared_955_ = v_isSharedCheck_982_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_952_);
                        lean_dec(v_a_948_);
                        v___x_954_ = lean_box(0);
                        v_isShared_955_ = v_isSharedCheck_982_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_948_);
                    lean_dec_ref(v_subExpr_940_);
                    lean_dec_ref(v___x_939_);
                    lean_dec_ref(v_idxExpr_938_);
                    lean_dec(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    lean_dec_ref(v_expr_933_);
                    lean_dec(v_width_932_);
                    v___x_983_ = lean_box(0);
                    if v_isShared_951_ == 0 {
                        lean_ctor_set(v___x_950_, 0, v___x_983_);
                        v___x_985_ = v___x_950_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
                        v___x_985_ = v_reuseFailAlloc_986_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_956_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_932_,
                    v_expr_933_,
                    v___y_941_,
                    v___y_942_,
                    v___y_943_,
                    v___y_944_,
                    v___y_945_,
                );
                if lean_obj_tag(v___x_956_) == 0 {
                    v_a_957_ = lean_ctor_get(v___x_956_, 0);
                    v_isSharedCheck_973_ = (!lean_is_exclusive(v___x_956_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_959_ = v___x_956_;
                        v_isShared_960_ = v_isSharedCheck_973_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_957_);
                        lean_dec(v___x_956_);
                        v___x_959_ = lean_box(0);
                        v_isShared_960_ = v_isSharedCheck_973_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_954_);
                    lean_dec(v_val_952_);
                    lean_dec_ref(v_subExpr_940_);
                    lean_dec_ref(v___x_939_);
                    lean_dec_ref(v_idxExpr_938_);
                    lean_dec(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    v_a_974_ = lean_ctor_get(v___x_956_, 0);
                    v_isSharedCheck_981_ = (!lean_is_exclusive(v___x_956_)) as u8;
                    if v_isSharedCheck_981_ == 0 {
                        v___x_976_ = v___x_956_;
                        v_isShared_977_ = v_isSharedCheck_981_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_974_);
                        lean_dec(v___x_956_);
                        v___x_976_ = lean_box(0);
                        v_isShared_977_ = v_isSharedCheck_981_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_961_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0;
                v___x_962_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2;
                v___x_963_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0;
                v___x_964_ = l_Lean_Name_mkStr6(
                    v___x_934_, v___x_935_, v___x_936_, v___x_961_, v___x_962_, v___x_963_,
                );
                v___x_965_ = l_Lean_mkConst(v___x_964_, v___x_937_);
                v___x_966_ = l_Lean_mkApp5(
                    v___x_965_,
                    v_idxExpr_938_,
                    v___x_939_,
                    v_subExpr_940_,
                    v_a_957_,
                    v_val_952_,
                );
                if v_isShared_955_ == 0 {
                    lean_ctor_set(v___x_954_, 0, v___x_966_);
                    v___x_968_ = v___x_954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_966_);
                    v___x_968_ = v_reuseFailAlloc_972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_960_ == 0 {
                    lean_ctor_set(v___x_959_, 0, v___x_968_);
                    v___x_970_ = v___x_959_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
                    v___x_970_ = v_reuseFailAlloc_971_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_970_;
            }
            6 => {
                if v_isShared_977_ == 0 {
                    v___x_979_ = v___x_976_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
                    v___x_979_ = v_reuseFailAlloc_980_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_979_;
            }
            8 => {
                return v___x_985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed(
    mut v_sub_988_: *mut LeanObject,
    mut v_width_989_: *mut LeanObject,
    mut v_expr_990_: *mut LeanObject,
    mut v___x_991_: *mut LeanObject,
    mut v___x_992_: *mut LeanObject,
    mut v___x_993_: *mut LeanObject,
    mut v___x_994_: *mut LeanObject,
    mut v_idxExpr_995_: *mut LeanObject,
    mut v___x_996_: *mut LeanObject,
    mut v_subExpr_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_res_1004_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(
        v_sub_988_,
        v_width_989_,
        v_expr_990_,
        v___x_991_,
        v___x_992_,
        v___x_993_,
        v___x_994_,
        v_idxExpr_995_,
        v___x_996_,
        v_subExpr_997_,
        v___y_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
    );
    lean_dec(v___y_1002_);
    lean_dec_ref(v___y_1001_);
    lean_dec(v___y_1000_);
    lean_dec_ref(v___y_999_);
    lean_dec(v___y_998_);
    return v_res_1004_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(
    mut v_sub_1005_: *mut LeanObject,
    mut v_subExpr_1006_: *mut LeanObject,
    mut v_idx_1007_: *mut LeanObject,
    mut v_origExpr_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_width_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idxExpr_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    v_width_1010_ = lean_ctor_get(v_sub_1005_, 0);
    lean_inc_n(v_width_1010_, 3);
    v_bvExpr_1011_ = lean_ctor_get(v_sub_1005_, 1);
    v_expr_1012_ = lean_ctor_get(v_sub_1005_, 4);
    lean_inc_ref_n(v_expr_1012_, 2);
    lean_inc(v_idx_1007_);
    lean_inc_ref(v_bvExpr_1011_);
    v_bvExpr_1013_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v_bvExpr_1013_, 0, v_width_1010_);
    lean_ctor_set(v_bvExpr_1013_, 1, v_bvExpr_1011_);
    lean_ctor_set(v_bvExpr_1013_, 2, v_idx_1007_);
    v_idxExpr_1014_ = l_Lean_mkNatLit(v_idx_1007_);
    v___x_1015_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6;
    v___x_1016_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7;
    v___x_1017_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8;
    v___x_1018_ = lean_box(0);
    v___x_1019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12,
    );
    v___x_1020_ = l_Lean_mkNatLit(v_width_1010_);
    lean_inc_ref(v___x_1020_);
    lean_inc_ref(v_idxExpr_1014_);
    v_proof_1021_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        16,
        10,
    );
    lean_closure_set(v_proof_1021_, 0, v_sub_1005_);
    lean_closure_set(v_proof_1021_, 1, v_width_1010_);
    lean_closure_set(v_proof_1021_, 2, v_expr_1012_);
    lean_closure_set(v_proof_1021_, 3, v___x_1015_);
    lean_closure_set(v_proof_1021_, 4, v___x_1016_);
    lean_closure_set(v_proof_1021_, 5, v___x_1017_);
    lean_closure_set(v_proof_1021_, 6, v___x_1018_);
    lean_closure_set(v_proof_1021_, 7, v_idxExpr_1014_);
    lean_closure_set(v_proof_1021_, 8, v___x_1020_);
    lean_closure_set(v_proof_1021_, 9, v_subExpr_1006_);
    v_expr_1022_ = l_Lean_mkApp3(v___x_1019_, v___x_1020_, v_expr_1012_, v_idxExpr_1014_);
    v___x_1023_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1023_, 0, v_bvExpr_1013_);
    lean_ctor_set(v___x_1023_, 1, v_origExpr_1008_);
    lean_ctor_set(v___x_1023_, 2, v_proof_1021_);
    lean_ctor_set(v___x_1023_, 3, v_expr_1022_);
    v___x_1024_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1024_, 0, v___x_1023_);
    return v___x_1024_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___boxed(
    mut v_sub_1025_: *mut LeanObject,
    mut v_subExpr_1026_: *mut LeanObject,
    mut v_idx_1027_: *mut LeanObject,
    mut v_origExpr_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(
        v_sub_1025_,
        v_subExpr_1026_,
        v_idx_1027_,
        v_origExpr_1028_,
    );
    return v_res_1030_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(
    mut v_sub_1031_: *mut LeanObject,
    mut v_subExpr_1032_: *mut LeanObject,
    mut v_idx_1033_: *mut LeanObject,
    mut v_origExpr_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    v___x_1041_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(
        v_sub_1031_,
        v_subExpr_1032_,
        v_idx_1033_,
        v_origExpr_1034_,
    );
    return v___x_1041_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___boxed(
    mut v_sub_1042_: *mut LeanObject,
    mut v_subExpr_1043_: *mut LeanObject,
    mut v_idx_1044_: *mut LeanObject,
    mut v_origExpr_1045_: *mut LeanObject,
    mut v_a_1046_: *mut LeanObject,
    mut v_a_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1052_: *mut LeanObject = core::ptr::null_mut();
    v_res_1052_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(
        v_sub_1042_,
        v_subExpr_1043_,
        v_idx_1044_,
        v_origExpr_1045_,
        v_a_1046_,
        v_a_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
    );
    lean_dec(v_a_1050_);
    lean_dec_ref(v_a_1049_);
    lean_dec(v_a_1048_);
    lean_dec_ref(v_a_1047_);
    lean_dec(v_a_1046_);
    return v_res_1052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
}

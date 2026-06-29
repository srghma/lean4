// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Util
// Imports: Init.Grind.Ring.Basic Lean.Meta.SynthInstance
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_int_dec_eq, lean_int_ediv,
    lean_int_emod, lean_int_mul, lean_int_sub, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_abs, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_to_int, lean_ptr_addr, lean_uint64_dec_eq, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_uint64,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_forIn___redArg, l_Lean_PersistentArray_pop___redArg,
    l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_FVarIdSet_insert, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_aquote};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, runtime_initialize_Lean_Meta_SynthInstance,
};
pub static l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [79, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isNatNum___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isNatNum___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17636616155771105671 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15578568367168711682 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isNatNum___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isNatNum___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value)
                as *mut crate::leanh::LeanObject,
            6887128300681693401 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isNatNum___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10588691866721272861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9626815015619986526 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17185717442815859305 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value)
                as *mut crate::leanh::LeanObject,
            6362876895233142233 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isIntNum___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatType___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isNatType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatType___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatType___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isNatType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatType___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isIntType___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isIntType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isIntType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9594062259507646949 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 65, 100, 100, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            13235980228967245028 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 115, 116, 76, 69, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInstLENat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInstLENat___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7582202872767459283 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInstLENat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            10680564408669940870 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [73, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4977321555018234431 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4463466624472370110 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [78, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5779414593499529281 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value)
                as *mut crate::leanh::LeanObject,
            7063772860359172143 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [72, 83, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [104, 83, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value)
            as *mut crate::leanh::LeanObject,
        15703084674812832738 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value)
                as *mut crate::leanh::LeanObject,
            13609749952674037527 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value)
            as *mut crate::leanh::LeanObject,
        12847922472053947547 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value)
                as *mut crate::leanh::LeanObject,
            10422657989269798688 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value)
            as *mut crate::leanh::LeanObject,
        13744984671752750173 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value)
                as *mut crate::leanh::LeanObject,
            9682224670061807480 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value)
            as *mut crate::leanh::LeanObject,
        11858238400308895562 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value)
                as *mut crate::leanh::LeanObject,
            6100819061652633370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value)
                as *mut crate::leanh::LeanObject,
            1611444129324655608 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value)
            as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value)
                as *mut crate::leanh::LeanObject,
            4187025665268973031 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isArithTerm___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_gcdExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________: u8 = 0;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11079354408986465895 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10352885018404983386 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value)
            as *mut crate::leanh::LeanObject,
        13556645696814629918 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value)
            as *mut crate::leanh::LeanObject,
        18261494228143523011 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value)
            as *mut crate::leanh::LeanObject,
        622053547050603573 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [65, 114, 105, 116, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value)
            as *mut crate::leanh::LeanObject,
        7655114909728474417 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value:
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
    m_data: [85, 116, 105, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value)
            as *mut crate::leanh::LeanObject,
        3289248155724230499 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        13012082450689143598 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2254088570334970967 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2117929650198872583 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value)
            as *mut crate::leanh::LeanObject,
        15204302795302152265 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value)
            as *mut crate::leanh::LeanObject,
        16847748369629721125 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        95, 95, 95, 95, 105, 110, 116, 77, 111, 100, 117, 108, 101, 77, 97, 114, 107, 101, 114, 95,
        95, 95, 95, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value)
            as *mut crate::leanh::LeanObject,
        13283876736535007430 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_split___redArg___closed__12_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_split___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_split___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatNum(mut v_e_799_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    v___x_800_ = l_Lean_Expr_cleanupAnnotations(v_e_799_);
    v___x_801_ = l_Lean_Expr_isApp(v___x_800_);
    if v___x_801_ == 0 {
        crate::leanh::lean_dec_ref(v___x_800_);
        return v___x_801_;
    } else {
        let mut v_arg_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: u8 = 0;
        v_arg_802_ = crate::leanh::lean_ctor_get(v___x_800_, 1);
        crate::leanh::lean_inc_ref(v_arg_802_);
        v___x_803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_800_);
        v___x_804_ = l_Lean_Expr_isApp(v___x_803_);
        if v___x_804_ == 0 {
            crate::leanh::lean_dec_ref(v___x_803_);
            crate::leanh::lean_dec_ref(v_arg_802_);
            return v___x_804_;
        } else {
            let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_806_: u8 = 0;
            v___x_805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_803_);
            v___x_806_ = l_Lean_Expr_isApp(v___x_805_);
            if v___x_806_ == 0 {
                crate::leanh::lean_dec_ref(v___x_805_);
                crate::leanh::lean_dec_ref(v_arg_802_);
                return v___x_806_;
            } else {
                let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_809_: u8 = 0;
                v___x_807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_805_);
                v___x_808_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__2;
                v___x_809_ = l_Lean_Expr_isConstOf(v___x_807_, v___x_808_);
                crate::leanh::lean_dec_ref(v___x_807_);
                if v___x_809_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_802_);
                    return v___x_809_;
                } else {
                    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_811_: u8 = 0;
                    v___x_810_ = l_Lean_Expr_cleanupAnnotations(v_arg_802_);
                    v___x_811_ = l_Lean_Expr_isApp(v___x_810_);
                    if v___x_811_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_810_);
                        return v___x_811_;
                    } else {
                        let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_814_: u8 = 0;
                        v___x_812_ = l_Lean_Expr_appFnCleanup___redArg(v___x_810_);
                        v___x_813_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__4;
                        v___x_814_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_813_);
                        crate::leanh::lean_dec_ref(v___x_812_);
                        return v___x_814_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatNum___boxed(
    mut v_e_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_816_: u8 = 0;
    let mut v_r_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_815_);
    v_r_817_ = crate::leanh::lean_box((v_res_816_) as usize);
    return v_r_817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNonnegIntNum(
    mut v_e_821_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    v___x_822_ = l_Lean_Expr_cleanupAnnotations(v_e_821_);
    v___x_823_ = l_Lean_Expr_isApp(v___x_822_);
    if v___x_823_ == 0 {
        crate::leanh::lean_dec_ref(v___x_822_);
        return v___x_823_;
    } else {
        let mut v_arg_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_826_: u8 = 0;
        v_arg_824_ = crate::leanh::lean_ctor_get(v___x_822_, 1);
        crate::leanh::lean_inc_ref(v_arg_824_);
        v___x_825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_822_);
        v___x_826_ = l_Lean_Expr_isApp(v___x_825_);
        if v___x_826_ == 0 {
            crate::leanh::lean_dec_ref(v___x_825_);
            crate::leanh::lean_dec_ref(v_arg_824_);
            return v___x_826_;
        } else {
            let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_828_: u8 = 0;
            v___x_827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_825_);
            v___x_828_ = l_Lean_Expr_isApp(v___x_827_);
            if v___x_828_ == 0 {
                crate::leanh::lean_dec_ref(v___x_827_);
                crate::leanh::lean_dec_ref(v_arg_824_);
                return v___x_828_;
            } else {
                let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_831_: u8 = 0;
                v___x_829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_827_);
                v___x_830_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__2;
                v___x_831_ = l_Lean_Expr_isConstOf(v___x_829_, v___x_830_);
                crate::leanh::lean_dec_ref(v___x_829_);
                if v___x_831_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_824_);
                    return v___x_831_;
                } else {
                    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_833_: u8 = 0;
                    v___x_832_ = l_Lean_Expr_cleanupAnnotations(v_arg_824_);
                    v___x_833_ = l_Lean_Expr_isApp(v___x_832_);
                    if v___x_833_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_832_);
                        return v___x_833_;
                    } else {
                        let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_836_: u8 = 0;
                        v___x_834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_832_);
                        v___x_835_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1;
                        v___x_836_ = l_Lean_Expr_isConstOf(v___x_834_, v___x_835_);
                        crate::leanh::lean_dec_ref(v___x_834_);
                        return v___x_836_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNonnegIntNum___boxed(
    mut v_e_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_837_);
    v_r_839_ = crate::leanh::lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntNum(mut v_e_850_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    crate::leanh::lean_inc_ref(v_e_850_);
    v___x_851_ = l_Lean_Expr_cleanupAnnotations(v_e_850_);
    v___x_852_ = l_Lean_Expr_isApp(v___x_851_);
    if v___x_852_ == 0 {
        let mut v___x_853_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_851_);
        v___x_853_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_850_);
        return v___x_853_;
    } else {
        let mut v_arg_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_856_: u8 = 0;
        v_arg_854_ = crate::leanh::lean_ctor_get(v___x_851_, 1);
        crate::leanh::lean_inc_ref(v_arg_854_);
        v___x_855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_851_);
        v___x_856_ = l_Lean_Expr_isApp(v___x_855_);
        if v___x_856_ == 0 {
            let mut v___x_857_: u8 = 0;
            crate::leanh::lean_dec_ref(v___x_855_);
            crate::leanh::lean_dec_ref(v_arg_854_);
            v___x_857_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_850_);
            return v___x_857_;
        } else {
            let mut v_arg_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_860_: u8 = 0;
            v_arg_858_ = crate::leanh::lean_ctor_get(v___x_855_, 1);
            crate::leanh::lean_inc_ref(v_arg_858_);
            v___x_859_ = l_Lean_Expr_appFnCleanup___redArg(v___x_855_);
            v___x_860_ = l_Lean_Expr_isApp(v___x_859_);
            if v___x_860_ == 0 {
                let mut v___x_861_: u8 = 0;
                crate::leanh::lean_dec_ref(v___x_859_);
                crate::leanh::lean_dec_ref(v_arg_858_);
                crate::leanh::lean_dec_ref(v_arg_854_);
                v___x_861_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_850_);
                return v___x_861_;
            } else {
                let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_864_: u8 = 0;
                v___x_862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_859_);
                v___x_863_ = l_Lean_Meta_Grind_Arith_isIntNum___closed__2;
                v___x_864_ = l_Lean_Expr_isConstOf(v___x_862_, v___x_863_);
                crate::leanh::lean_dec_ref(v___x_862_);
                if v___x_864_ == 0 {
                    let mut v___x_865_: u8 = 0;
                    crate::leanh::lean_dec_ref(v_arg_858_);
                    crate::leanh::lean_dec_ref(v_arg_854_);
                    v___x_865_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_850_);
                    return v___x_865_;
                } else {
                    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_868_: u8 = 0;
                    crate::leanh::lean_dec_ref(v_e_850_);
                    v___x_866_ = l_Lean_Expr_cleanupAnnotations(v_arg_858_);
                    v___x_867_ = l_Lean_Meta_Grind_Arith_isIntNum___closed__5;
                    v___x_868_ = l_Lean_Expr_isConstOf(v___x_866_, v___x_867_);
                    crate::leanh::lean_dec_ref(v___x_866_);
                    if v___x_868_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_854_);
                        return v___x_868_;
                    } else {
                        let mut v___x_869_: u8 = 0;
                        v___x_869_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_arg_854_);
                        return v___x_869_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntNum___boxed(
    mut v_e_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_871_: u8 = 0;
    let mut v_r_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_871_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_870_);
    v_r_872_ = crate::leanh::lean_box((v_res_871_) as usize);
    return v_r_872_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNum(mut v_e_873_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_874_: u8 = 0;
    crate::leanh::lean_inc_ref(v_e_873_);
    v___x_874_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_873_);
    if v___x_874_ == 0 {
        let mut v___x_875_: u8 = 0;
        v___x_875_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_873_);
        return v___x_875_;
    } else {
        crate::leanh::lean_dec_ref(v_e_873_);
        return v___x_874_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNum___boxed(
    mut v_e_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_877_: u8 = 0;
    let mut v_r_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l_Lean_Meta_Grind_Arith_isNum(v_e_876_);
    v_r_878_ = crate::leanh::lean_box((v_res_877_) as usize);
    return v_r_878_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatType(mut v_e_882_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    v___x_883_ = l_Lean_Meta_Grind_Arith_isNatType___closed__1;
    v___x_884_ = l_Lean_Expr_isConstOf(v_e_882_, v___x_883_);
    return v___x_884_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatType___boxed(
    mut v_e_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_886_: u8 = 0;
    let mut v_r_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Lean_Meta_Grind_Arith_isNatType(v_e_885_);
    crate::leanh::lean_dec_ref(v_e_885_);
    v_r_887_ = crate::leanh::lean_box((v_res_886_) as usize);
    return v_r_887_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntType(mut v_e_890_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    v___x_891_ = l_Lean_Meta_Grind_Arith_isIntType___closed__0;
    v___x_892_ = l_Lean_Expr_isConstOf(v_e_890_, v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntType___boxed(
    mut v_e_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_894_: u8 = 0;
    let mut v_r_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ = l_Lean_Meta_Grind_Arith_isIntType(v_e_893_);
    crate::leanh::lean_dec_ref(v_e_893_);
    v_r_895_ = crate::leanh::lean_box((v_res_894_) as usize);
    return v_r_895_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInstAddNat(
    mut v_e_902_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    v___x_903_ = l_Lean_Expr_cleanupAnnotations(v_e_902_);
    v___x_904_ = l_Lean_Expr_isApp(v___x_903_);
    if v___x_904_ == 0 {
        crate::leanh::lean_dec_ref(v___x_903_);
        return v___x_904_;
    } else {
        let mut v_arg_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: u8 = 0;
        v_arg_905_ = crate::leanh::lean_ctor_get(v___x_903_, 1);
        crate::leanh::lean_inc_ref(v_arg_905_);
        v___x_906_ = l_Lean_Expr_appFnCleanup___redArg(v___x_903_);
        v___x_907_ = l_Lean_Expr_isApp(v___x_906_);
        if v___x_907_ == 0 {
            crate::leanh::lean_dec_ref(v___x_906_);
            crate::leanh::lean_dec_ref(v_arg_905_);
            return v___x_907_;
        } else {
            let mut v_arg_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_911_: u8 = 0;
            v_arg_908_ = crate::leanh::lean_ctor_get(v___x_906_, 1);
            crate::leanh::lean_inc_ref(v_arg_908_);
            v___x_909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_906_);
            v___x_910_ = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1;
            v___x_911_ = l_Lean_Expr_isConstOf(v___x_909_, v___x_910_);
            crate::leanh::lean_dec_ref(v___x_909_);
            if v___x_911_ == 0 {
                crate::leanh::lean_dec_ref(v_arg_908_);
                crate::leanh::lean_dec_ref(v_arg_905_);
                return v___x_911_;
            } else {
                let mut v___x_912_: u8 = 0;
                v___x_912_ = l_Lean_Meta_Grind_Arith_isNatType(v_arg_908_);
                crate::leanh::lean_dec_ref(v_arg_908_);
                if v___x_912_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_905_);
                    return v___x_912_;
                } else {
                    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_914_: u8 = 0;
                    v___x_913_ = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3;
                    v___x_914_ = l_Lean_Expr_isConstOf(v_arg_905_, v___x_913_);
                    crate::leanh::lean_dec_ref(v_arg_905_);
                    return v___x_914_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(
    mut v_e_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_916_: u8 = 0;
    let mut v_r_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_e_915_);
    v_r_917_ = crate::leanh::lean_box((v_res_916_) as usize);
    return v_r_917_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInstLENat(
    mut v_e_921_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: u8 = 0;
    v___x_922_ = l_Lean_Meta_Grind_Arith_isInstLENat___closed__1;
    v___x_923_ = l_Lean_Expr_isConstOf(v_e_921_, v___x_922_);
    return v___x_923_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInstLENat___boxed(
    mut v_e_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_925_: u8 = 0;
    let mut v_r_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l_Lean_Meta_Grind_Arith_isInstLENat(v_e_924_);
    crate::leanh::lean_dec_ref(v_e_924_);
    v_r_926_ = crate::leanh::lean_box((v_res_925_) as usize);
    return v_r_926_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatAdd_x3f(
    mut v_e_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    v___x_933_ = l_Lean_Expr_cleanupAnnotations(v_e_932_);
    v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
    if v___x_934_ == 0 {
        let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_933_);
        v___x_935_ = crate::leanh::lean_box(0);
        return v___x_935_;
    } else {
        let mut v_arg_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: u8 = 0;
        v_arg_936_ = crate::leanh::lean_ctor_get(v___x_933_, 1);
        crate::leanh::lean_inc_ref(v_arg_936_);
        v___x_937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
        v___x_938_ = l_Lean_Expr_isApp(v___x_937_);
        if v___x_938_ == 0 {
            let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_937_);
            crate::leanh::lean_dec_ref(v_arg_936_);
            v___x_939_ = crate::leanh::lean_box(0);
            return v___x_939_;
        } else {
            let mut v_arg_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_942_: u8 = 0;
            v_arg_940_ = crate::leanh::lean_ctor_get(v___x_937_, 1);
            crate::leanh::lean_inc_ref(v_arg_940_);
            v___x_941_ = l_Lean_Expr_appFnCleanup___redArg(v___x_937_);
            v___x_942_ = l_Lean_Expr_isApp(v___x_941_);
            if v___x_942_ == 0 {
                let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_941_);
                crate::leanh::lean_dec_ref(v_arg_940_);
                crate::leanh::lean_dec_ref(v_arg_936_);
                v___x_943_ = crate::leanh::lean_box(0);
                return v___x_943_;
            } else {
                let mut v_arg_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_946_: u8 = 0;
                v_arg_944_ = crate::leanh::lean_ctor_get(v___x_941_, 1);
                crate::leanh::lean_inc_ref(v_arg_944_);
                v___x_945_ = l_Lean_Expr_appFnCleanup___redArg(v___x_941_);
                v___x_946_ = l_Lean_Expr_isApp(v___x_945_);
                if v___x_946_ == 0 {
                    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v___x_945_);
                    crate::leanh::lean_dec_ref(v_arg_944_);
                    crate::leanh::lean_dec_ref(v_arg_940_);
                    crate::leanh::lean_dec_ref(v_arg_936_);
                    v___x_947_ = crate::leanh::lean_box(0);
                    return v___x_947_;
                } else {
                    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_949_: u8 = 0;
                    v___x_948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_945_);
                    v___x_949_ = l_Lean_Expr_isApp(v___x_948_);
                    if v___x_949_ == 0 {
                        let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v___x_948_);
                        crate::leanh::lean_dec_ref(v_arg_944_);
                        crate::leanh::lean_dec_ref(v_arg_940_);
                        crate::leanh::lean_dec_ref(v_arg_936_);
                        v___x_950_ = crate::leanh::lean_box(0);
                        return v___x_950_;
                    } else {
                        let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_952_: u8 = 0;
                        v___x_951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_948_);
                        v___x_952_ = l_Lean_Expr_isApp(v___x_951_);
                        if v___x_952_ == 0 {
                            let mut v___x_953_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref(v___x_951_);
                            crate::leanh::lean_dec_ref(v_arg_944_);
                            crate::leanh::lean_dec_ref(v_arg_940_);
                            crate::leanh::lean_dec_ref(v_arg_936_);
                            v___x_953_ = crate::leanh::lean_box(0);
                            return v___x_953_;
                        } else {
                            let mut v___x_954_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_955_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_956_: u8 = 0;
                            v___x_954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_951_);
                            v___x_955_ = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
                            v___x_956_ = l_Lean_Expr_isConstOf(v___x_954_, v___x_955_);
                            crate::leanh::lean_dec_ref(v___x_954_);
                            if v___x_956_ == 0 {
                                let mut v___x_957_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec_ref(v_arg_944_);
                                crate::leanh::lean_dec_ref(v_arg_940_);
                                crate::leanh::lean_dec_ref(v_arg_936_);
                                v___x_957_ = crate::leanh::lean_box(0);
                                return v___x_957_;
                            } else {
                                let mut v___x_958_: u8 = 0;
                                v___x_958_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_944_);
                                if v___x_958_ == 0 {
                                    let mut v___x_959_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec_ref(v_arg_940_);
                                    crate::leanh::lean_dec_ref(v_arg_936_);
                                    v___x_959_ = crate::leanh::lean_box(0);
                                    return v___x_959_;
                                } else {
                                    let mut v___x_960_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_961_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_960_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_960_, 0, v_arg_940_);
                                    crate::leanh::lean_ctor_set(v___x_960_, 1, v_arg_936_);
                                    v___x_961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_961_, 0, v___x_960_);
                                    return v___x_961_;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatAdd(mut v_e_962_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    v___x_963_ = l_Lean_Expr_cleanupAnnotations(v_e_962_);
    v___x_964_ = l_Lean_Expr_isApp(v___x_963_);
    if v___x_964_ == 0 {
        crate::leanh::lean_dec_ref(v___x_963_);
        return v___x_964_;
    } else {
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: u8 = 0;
        v___x_965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_963_);
        v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
        if v___x_966_ == 0 {
            crate::leanh::lean_dec_ref(v___x_965_);
            return v___x_966_;
        } else {
            let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_968_: u8 = 0;
            v___x_967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
            v___x_968_ = l_Lean_Expr_isApp(v___x_967_);
            if v___x_968_ == 0 {
                crate::leanh::lean_dec_ref(v___x_967_);
                return v___x_968_;
            } else {
                let mut v_arg_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_971_: u8 = 0;
                v_arg_969_ = crate::leanh::lean_ctor_get(v___x_967_, 1);
                crate::leanh::lean_inc_ref(v_arg_969_);
                v___x_970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_967_);
                v___x_971_ = l_Lean_Expr_isApp(v___x_970_);
                if v___x_971_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_970_);
                    crate::leanh::lean_dec_ref(v_arg_969_);
                    return v___x_971_;
                } else {
                    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_973_: u8 = 0;
                    v___x_972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_970_);
                    v___x_973_ = l_Lean_Expr_isApp(v___x_972_);
                    if v___x_973_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_972_);
                        crate::leanh::lean_dec_ref(v_arg_969_);
                        return v___x_973_;
                    } else {
                        let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_975_: u8 = 0;
                        v___x_974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_972_);
                        v___x_975_ = l_Lean_Expr_isApp(v___x_974_);
                        if v___x_975_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_974_);
                            crate::leanh::lean_dec_ref(v_arg_969_);
                            return v___x_975_;
                        } else {
                            let mut v___x_976_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_977_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_978_: u8 = 0;
                            v___x_976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_974_);
                            v___x_977_ = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
                            v___x_978_ = l_Lean_Expr_isConstOf(v___x_976_, v___x_977_);
                            crate::leanh::lean_dec_ref(v___x_976_);
                            if v___x_978_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_969_);
                                return v___x_978_;
                            } else {
                                let mut v___x_979_: u8 = 0;
                                v___x_979_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_969_);
                                return v___x_979_;
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatAdd___boxed(
    mut v_e_980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_981_: u8 = 0;
    let mut v_r_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_981_ = l_Lean_Meta_Grind_Arith_isNatAdd(v_e_980_);
    v_r_982_ = crate::leanh::lean_box((v_res_981_) as usize);
    return v_r_982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isNatNum_x3f(
    mut v_e_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1010_: u8 = 0;
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1014_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_984_ = l_Lean_Expr_cleanupAnnotations(v_e_983_);
                v___x_985_ = l_Lean_Expr_isApp(v___x_984_);
                if v___x_985_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_984_);
                    v___x_986_ = crate::leanh::lean_box(0);
                    return v___x_986_;
                } else {
                    v_arg_987_ = crate::leanh::lean_ctor_get(v___x_984_, 1);
                    crate::leanh::lean_inc_ref(v_arg_987_);
                    v___x_988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_984_);
                    v___x_989_ = l_Lean_Expr_isApp(v___x_988_);
                    if v___x_989_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_988_);
                        crate::leanh::lean_dec_ref(v_arg_987_);
                        v___x_990_ = crate::leanh::lean_box(0);
                        return v___x_990_;
                    } else {
                        v___x_991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_988_);
                        v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
                        if v___x_992_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_991_);
                            crate::leanh::lean_dec_ref(v_arg_987_);
                            v___x_993_ = crate::leanh::lean_box(0);
                            return v___x_993_;
                        } else {
                            v___x_994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
                            v___x_995_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__2;
                            v___x_996_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_995_);
                            crate::leanh::lean_dec_ref(v___x_994_);
                            if v___x_996_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_987_);
                                v___x_997_ = crate::leanh::lean_box(0);
                                return v___x_997_;
                            } else {
                                v___x_998_ = l_Lean_Expr_cleanupAnnotations(v_arg_987_);
                                v___x_999_ = l_Lean_Expr_isApp(v___x_998_);
                                if v___x_999_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_998_);
                                    v___x_1000_ = crate::leanh::lean_box(0);
                                    return v___x_1000_;
                                } else {
                                    v_arg_1001_ = crate::leanh::lean_ctor_get(v___x_998_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_1001_);
                                    v___x_1002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_998_);
                                    v___x_1003_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__4;
                                    v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1003_);
                                    crate::leanh::lean_dec_ref(v___x_1002_);
                                    if v___x_1004_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_1001_);
                                        v___x_1005_ = crate::leanh::lean_box(0);
                                        return v___x_1005_;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_arg_1001_) == 9 {
                                            v_a_1006_ = crate::leanh::lean_ctor_get(v_arg_1001_, 0);
                                            crate::leanh::lean_inc_ref(v_a_1006_);
                                            crate::leanh::lean_dec_ref_known(v_arg_1001_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_1006_) == 0 {
                                                v_val_1007_ =
                                                    crate::leanh::lean_ctor_get(v_a_1006_, 0);
                                                v_isSharedCheck_1014_ =
                                                    (!crate::leanh::lean_is_exclusive(v_a_1006_))
                                                        as u8;
                                                if v_isSharedCheck_1014_ == 0 {
                                                    v___x_1009_ = v_a_1006_;
                                                    v_isShared_1010_ = v_isSharedCheck_1014_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_val_1007_);
                                                    crate::leanh::lean_dec(v_a_1006_);
                                                    v___x_1009_ = crate::leanh::lean_box(0);
                                                    v_isShared_1010_ = v_isSharedCheck_1014_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_a_1006_);
                                                v___x_1015_ = crate::leanh::lean_box(0);
                                                return v___x_1015_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_1001_);
                                            v___x_1016_ = crate::leanh::lean_box(0);
                                            return v___x_1016_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1010_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1009_, 1);
                    v___x_1012_ = v___x_1009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1007_);
                    v___x_1012_ = v_reuseFailAlloc_1013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isArithTerm(
    mut v_e_1057_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
    v___x_1058_ = l_Lean_Expr_cleanupAnnotations(v_e_1057_);
    v___x_1059_ = l_Lean_Expr_isApp(v___x_1058_);
    if v___x_1059_ == 0 {
        crate::leanh::lean_dec_ref(v___x_1058_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: u8 = 0;
        v___x_1060_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1058_);
        v___x_1061_ = l_Lean_Expr_isApp(v___x_1060_);
        if v___x_1061_ == 0 {
            crate::leanh::lean_dec_ref(v___x_1060_);
            return v___x_1061_;
        } else {
            let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1063_: u8 = 0;
            v___x_1062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1060_);
            v___x_1063_ = l_Lean_Expr_isApp(v___x_1062_);
            if v___x_1063_ == 0 {
                crate::leanh::lean_dec_ref(v___x_1062_);
                return v___x_1063_;
            } else {
                let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1066_: u8 = 0;
                v___x_1064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1062_);
                v___x_1065_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__2;
                v___x_1066_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1065_);
                if v___x_1066_ == 0 {
                    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1068_: u8 = 0;
                    v___x_1067_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__5;
                    v___x_1068_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1067_);
                    if v___x_1068_ == 0 {
                        let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1070_: u8 = 0;
                        v___x_1069_ = l_Lean_Meta_Grind_Arith_isNatNum___closed__2;
                        v___x_1070_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1069_);
                        if v___x_1070_ == 0 {
                            let mut v___x_1071_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1072_: u8 = 0;
                            v___x_1071_ = l_Lean_Meta_Grind_Arith_isIntNum___closed__2;
                            v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1064_, v___x_1071_);
                            if v___x_1072_ == 0 {
                                let mut v___x_1073_: u8 = 0;
                                v___x_1073_ = l_Lean_Expr_isApp(v___x_1064_);
                                if v___x_1073_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1064_);
                                    return v___x_1073_;
                                } else {
                                    let mut v___x_1074_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1075_: u8 = 0;
                                    v___x_1074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1064_);
                                    v___x_1075_ = l_Lean_Expr_isApp(v___x_1074_);
                                    if v___x_1075_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1074_);
                                        return v___x_1075_;
                                    } else {
                                        let mut v___x_1076_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1077_: u8 = 0;
                                        v___x_1076_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1074_);
                                        v___x_1077_ = l_Lean_Expr_isApp(v___x_1076_);
                                        if v___x_1077_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_1076_);
                                            return v___x_1077_;
                                        } else {
                                            let mut v___x_1078_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_1079_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_1080_: u8 = 0;
                                            v___x_1078_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_1076_);
                                            v___x_1079_ =
                                                l_Lean_Meta_Grind_Arith_isArithTerm___closed__8;
                                            v___x_1080_ =
                                                l_Lean_Expr_isConstOf(v___x_1078_, v___x_1079_);
                                            if v___x_1080_ == 0 {
                                                let mut v___x_1081_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_1082_: u8 = 0;
                                                v___x_1081_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__11;
                                                v___x_1082_ =
                                                    l_Lean_Expr_isConstOf(v___x_1078_, v___x_1081_);
                                                if v___x_1082_ == 0 {
                                                    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_1084_: u8 = 0;
                                                    v___x_1083_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__14;
                                                    v___x_1084_ = l_Lean_Expr_isConstOf(
                                                        v___x_1078_,
                                                        v___x_1083_,
                                                    );
                                                    if v___x_1084_ == 0 {
                                                        let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_1086_: u8 = 0;
                                                        v___x_1085_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__17;
                                                        v___x_1086_ = l_Lean_Expr_isConstOf(
                                                            v___x_1078_,
                                                            v___x_1085_,
                                                        );
                                                        if v___x_1086_ == 0 {
                                                            let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_1088_: u8 = 0;
                                                            v___x_1087_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__20;
                                                            v___x_1088_ = l_Lean_Expr_isConstOf(
                                                                v___x_1078_,
                                                                v___x_1087_,
                                                            );
                                                            if v___x_1088_ == 0 {
                                                                let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_1090_: u8 = 0;
                                                                v___x_1089_ = l_Lean_Meta_Grind_Arith_isArithTerm___closed__23;
                                                                v___x_1090_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1078_,
                                                                    v___x_1089_,
                                                                );
                                                                if v___x_1090_ == 0 {
                                                                    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_1092_: u8 = 0;
                                                                    v___x_1091_ = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
                                                                    v___x_1092_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1078_,
                                                                            v___x_1091_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1078_,
                                                                    );
                                                                    return v___x_1092_;
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1078_,
                                                                    );
                                                                    return v___x_1090_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_1078_,
                                                                );
                                                                return v___x_1088_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_1078_);
                                                            return v___x_1086_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_1078_);
                                                        return v___x_1084_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_1078_);
                                                    return v___x_1082_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_1078_);
                                                return v___x_1080_;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1064_);
                                return v___x_1072_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1064_);
                            return v___x_1070_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1064_);
                        return v___x_1068_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1064_);
                    return v___x_1066_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isArithTerm___boxed(
    mut v_e_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1094_: u8 = 0;
    let mut v_r_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1094_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_1093_);
    v_r_1095_ = crate::leanh::lean_box((v_res_1094_) as usize);
    return v_r_1095_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_quoteIfArithTerm(
    mut v_e_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: u8 = 0;
    crate::leanh::lean_inc_ref(v_e_1096_);
    v___x_1097_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_1096_);
    if v___x_1097_ == 0 {
        let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1098_ = l_Lean_MessageData_ofExpr(v_e_1096_);
        return v___x_1098_;
    } else {
        let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1099_ = l_Lean_MessageData_ofExpr(v_e_1096_);
        v___x_1100_ = l_Lean_aquote(v___x_1099_);
        return v___x_1100_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(
    mut v_a_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = lean_nat_to_int(v_a_1101_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1104_ = lean_nat_to_int(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_gcdExt(
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_b_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v_fst_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1120_: u8 = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut v_isSharedCheck_1131_: u8 = 0;
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1107_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_gcdExt___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once),
                    _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0,
                );
                v___x_1108_ = lean_int_dec_eq(v_b_1106_, v___x_1107_);
                if v___x_1108_ == 0 {
                    v___x_1109_ = lean_int_emod(v_a_1105_, v_b_1106_);
                    v___x_1110_ = l_Lean_Meta_Grind_Arith_gcdExt(v_b_1106_, v___x_1109_);
                    crate::leanh::lean_dec(v___x_1109_);
                    v_snd_1111_ = crate::leanh::lean_ctor_get(v___x_1110_, 1);
                    v_fst_1112_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                    v_isSharedCheck_1131_ = (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                    if v_isSharedCheck_1131_ == 0 {
                        v___x_1114_ = v___x_1110_;
                        v_isShared_1115_ = v_isSharedCheck_1131_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1111_);
                        crate::leanh::lean_inc(v_fst_1112_);
                        crate::leanh::lean_dec(v___x_1110_);
                        v___x_1114_ = crate::leanh::lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1131_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1132_ = lean_nat_abs(v_a_1105_);
                    v___x_1133_ = lean_nat_to_int(v___x_1132_);
                    v___x_1138_ = lean_int_dec_eq(v_a_1105_, v___x_1107_);
                    if v___x_1138_ == 0 {
                        v___x_1139_ = lean_int_ediv(v_a_1105_, v___x_1133_);
                        v___y_1135_ = v___x_1139_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1135_ = v___x_1107_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1116_ = crate::leanh::lean_ctor_get(v_snd_1111_, 0);
                v_snd_1117_ = crate::leanh::lean_ctor_get(v_snd_1111_, 1);
                v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v_snd_1111_)) as u8;
                if v_isSharedCheck_1130_ == 0 {
                    v___x_1119_ = v_snd_1111_;
                    v_isShared_1120_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1117_);
                    crate::leanh::lean_inc(v_fst_1116_);
                    crate::leanh::lean_dec(v_snd_1111_);
                    v___x_1119_ = crate::leanh::lean_box(0);
                    v_isShared_1120_ = v_isSharedCheck_1130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1121_ = lean_int_ediv(v_a_1105_, v_b_1106_);
                v___x_1122_ = lean_int_mul(v___x_1121_, v_snd_1117_);
                crate::leanh::lean_dec(v___x_1121_);
                v___x_1123_ = lean_int_sub(v_fst_1116_, v___x_1122_);
                crate::leanh::lean_dec(v___x_1122_);
                crate::leanh::lean_dec(v_fst_1116_);
                if v_isShared_1120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1119_, 1, v___x_1123_);
                    crate::leanh::lean_ctor_set(v___x_1119_, 0, v_snd_1117_);
                    v___x_1125_ = v___x_1119_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_snd_1117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1123_);
                    v___x_1125_ = v_reuseFailAlloc_1129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1114_, 1, v___x_1125_);
                    v___x_1127_ = v___x_1114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
                    v___x_1127_ = v_reuseFailAlloc_1128_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1127_;
            }
            5 => {
                v___x_1136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1136_, 0, v___y_1135_);
                crate::leanh::lean_ctor_set(v___x_1136_, 1, v___x_1107_);
                v___x_1137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1133_);
                crate::leanh::lean_ctor_set(v___x_1137_, 1, v___x_1136_);
                return v___x_1137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_gcdExt___boxed(
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_b_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Lean_Meta_Grind_Arith_gcdExt(v_a_1140_, v_b_1141_);
    crate::leanh::lean_dec(v_b_1141_);
    crate::leanh::lean_dec(v_a_1140_);
    return v_res_1142_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_shrink(
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_sz_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1145_ = crate::leanh::lean_ctor_get(v_a_1143_, 2);
                v___x_1146_ = lean_nat_dec_lt(v_sz_1144_, v_size_1145_);
                if v___x_1146_ == 0 {
                    return v_a_1143_;
                } else {
                    v___x_1147_ = l_Lean_PersistentArray_pop___redArg(v_a_1143_);
                    v_a_1143_ = v___x_1147_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_shrink___boxed(
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_sz_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1151_ = l_Lean_Meta_Grind_Arith_shrink(v_a_1149_, v_sz_1150_);
    crate::leanh::lean_dec(v_sz_1150_);
    return v_res_1151_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(
    mut v_a_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = lean_nat_to_int(v_a_1152_);
    v___x_1154_ = l_Rat_ofInt(v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1156_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(v___x_1155_);
    return v___x_1156_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(
    mut v_sz_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1159_ = crate::leanh::lean_ctor_get(v_a_1158_, 2);
                v___x_1160_ = lean_nat_dec_lt(v_size_1159_, v_sz_1157_);
                if v___x_1160_ == 0 {
                    return v_a_1158_;
                } else {
                    v___x_1161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0);
                    v___x_1162_ = l_Lean_PersistentArray_push___redArg(v_a_1158_, v___x_1161_);
                    v_a_1158_ = v___x_1162_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(
    mut v_sz_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(
        v_sz_1164_, v_a_1165_,
    );
    crate::leanh::lean_dec(v_sz_1164_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_resize(
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_sz_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    v_size_1169_ = crate::leanh::lean_ctor_get(v_a_1167_, 2);
    v___x_1170_ = lean_nat_dec_lt(v_sz_1168_, v_size_1169_);
    if v___x_1170_ == 0 {
        let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1171_ =
            l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(
                v_sz_1168_, v_a_1167_,
            );
        return v___x_1171_;
    } else {
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1172_ = l_Lean_Meta_Grind_Arith_shrink(v_a_1167_, v_sz_1168_);
        return v___x_1172_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_resize___boxed(
    mut v_a_1173_: *mut crate::leanh::LeanObject,
    mut v_sz_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lean_Meta_Grind_Arith_resize(v_a_1173_, v_sz_1174_);
    crate::leanh::lean_dec(v_sz_1174_);
    return v_res_1175_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(
    mut v_c_1176_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_1177_: usize = 0;
    let mut v___x_1178_: u64 = 0;
    let mut v___x_1179_: u64 = 0;
    let mut v___x_1180_: u64 = 0;
    v___x_1177_ = lean_ptr_addr(v_c_1176_);
    v___x_1178_ = lean_usize_to_uint64(v___x_1177_);
    v___x_1179_ = 2u64;
    v___x_1180_ = lean_uint64_shift_right(v___x_1178_, v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(
    mut v_c_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1182_: u64 = 0;
    let mut v_r_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_1181_);
    crate::leanh::lean_dec(v_c_1181_);
    v_r_1183_ = crate::leanh::lean_box_uint64(v_res_1182_);
    return v_r_1183_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(
    mut v_00_u03b1_1184_: *mut crate::leanh::LeanObject,
    mut v_c_1185_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_1186_: u64 = 0;
    v___x_1186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_1185_);
    return v___x_1186_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(
    mut v_00_u03b1_1187_: *mut crate::leanh::LeanObject,
    mut v_c_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: u64 = 0;
    let mut v_r_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(v_00_u03b1_1187_, v_c_1188_);
    crate::leanh::lean_dec(v_c_1188_);
    v_r_1190_ = crate::leanh::lean_box_uint64(v_res_1189_);
    return v_r_1190_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(
    mut v_a_1191_: u64,
    mut v_x_1192_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1193_: u8 = 0;
    let mut v_key_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u64 = 0;
    let mut v___x_1197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1192_) == 0 {
                    v___x_1193_ = 0;
                    return v___x_1193_;
                } else {
                    v_key_1194_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
                    v_tail_1195_ = crate::leanh::lean_ctor_get(v_x_1192_, 2);
                    v___x_1196_ = crate::leanh::lean_unbox_uint64(v_key_1194_);
                    v___x_1197_ = lean_uint64_dec_eq(v___x_1196_, v_a_1191_);
                    if v___x_1197_ == 0 {
                        v_x_1192_ = v_tail_1195_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1197_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_x_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1201_: u64 = 0;
    let mut v_res_1202_: u8 = 0;
    let mut v_r_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1201_ = crate::leanh::lean_unbox_uint64(v_a_1199_);
    crate::leanh::lean_dec_ref(v_a_1199_);
    v_res_1202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_boxed_1201_, v_x_1200_);
    crate::leanh::lean_dec(v_x_1200_);
    v_r_1203_ = crate::leanh::lean_box((v_res_1202_) as usize);
    return v_r_1203_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(
    mut v_m_1204_: *mut crate::leanh::LeanObject,
    mut v_a_1205_: u64,
) -> u8 {
    let mut v_buckets_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: u64 = 0;
    let mut v_fold_1210_: u64 = 0;
    let mut v___x_1211_: u64 = 0;
    let mut v___x_1212_: u64 = 0;
    let mut v___x_1213_: u64 = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: usize = 0;
    let mut v___x_1216_: usize = 0;
    let mut v___x_1217_: usize = 0;
    let mut v___x_1218_: usize = 0;
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    v_buckets_1206_ = crate::leanh::lean_ctor_get(v_m_1204_, 1);
    v___x_1207_ = lean_array_get_size(v_buckets_1206_);
    v___x_1208_ = 32u64;
    v___x_1209_ = lean_uint64_shift_right(v_a_1205_, v___x_1208_);
    v_fold_1210_ = lean_uint64_xor(v_a_1205_, v___x_1209_);
    v___x_1211_ = 16u64;
    v___x_1212_ = lean_uint64_shift_right(v_fold_1210_, v___x_1211_);
    v___x_1213_ = lean_uint64_xor(v_fold_1210_, v___x_1212_);
    v___x_1214_ = lean_uint64_to_usize(v___x_1213_);
    v___x_1215_ = lean_usize_of_nat(v___x_1207_);
    v___x_1216_ = 1usize;
    v___x_1217_ = lean_usize_sub(v___x_1215_, v___x_1216_);
    v___x_1218_ = lean_usize_land(v___x_1214_, v___x_1217_);
    v___x_1219_ = lean_array_uget_borrowed(v_buckets_1206_, v___x_1218_);
    v___x_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_1205_, v___x_1219_);
    return v___x_1220_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(
    mut v_m_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1223_: u64 = 0;
    let mut v_res_1224_: u8 = 0;
    let mut v_r_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1223_ = crate::leanh::lean_unbox_uint64(v_a_1222_);
    crate::leanh::lean_dec_ref(v_a_1222_);
    v_res_1224_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_1221_, v_a_boxed_1223_);
    crate::leanh::lean_dec_ref(v_m_1221_);
    v_r_1225_ = crate::leanh::lean_box((v_res_1224_) as usize);
    return v_r_1225_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_x_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u64 = 0;
    let mut v___x_1236_: u64 = 0;
    let mut v___x_1237_: u64 = 0;
    let mut v___x_1238_: u64 = 0;
    let mut v_fold_1239_: u64 = 0;
    let mut v___x_1240_: u64 = 0;
    let mut v___x_1241_: u64 = 0;
    let mut v___x_1242_: u64 = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1227_) == 0 {
                    return v_x_1226_;
                } else {
                    v_key_1228_ = crate::leanh::lean_ctor_get(v_x_1227_, 0);
                    v_value_1229_ = crate::leanh::lean_ctor_get(v_x_1227_, 1);
                    v_tail_1230_ = crate::leanh::lean_ctor_get(v_x_1227_, 2);
                    v_isSharedCheck_1254_ = (!crate::leanh::lean_is_exclusive(v_x_1227_)) as u8;
                    if v_isSharedCheck_1254_ == 0 {
                        v___x_1232_ = v_x_1227_;
                        v_isShared_1233_ = v_isSharedCheck_1254_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1230_);
                        crate::leanh::lean_inc(v_value_1229_);
                        crate::leanh::lean_inc(v_key_1228_);
                        crate::leanh::lean_dec(v_x_1227_);
                        v___x_1232_ = crate::leanh::lean_box(0);
                        v_isShared_1233_ = v_isSharedCheck_1254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v_x_1226_);
                v___x_1235_ = 32u64;
                v___x_1236_ = crate::leanh::lean_unbox_uint64(v_key_1228_);
                v___x_1237_ = lean_uint64_shift_right(v___x_1236_, v___x_1235_);
                v___x_1238_ = crate::leanh::lean_unbox_uint64(v_key_1228_);
                v_fold_1239_ = lean_uint64_xor(v___x_1238_, v___x_1237_);
                v___x_1240_ = 16u64;
                v___x_1241_ = lean_uint64_shift_right(v_fold_1239_, v___x_1240_);
                v___x_1242_ = lean_uint64_xor(v_fold_1239_, v___x_1241_);
                v___x_1243_ = lean_uint64_to_usize(v___x_1242_);
                v___x_1244_ = lean_usize_of_nat(v___x_1234_);
                v___x_1245_ = 1usize;
                v___x_1246_ = lean_usize_sub(v___x_1244_, v___x_1245_);
                v___x_1247_ = lean_usize_land(v___x_1243_, v___x_1246_);
                v___x_1248_ = lean_array_uget_borrowed(v_x_1226_, v___x_1247_);
                crate::leanh::lean_inc(v___x_1248_);
                if v_isShared_1233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1232_, 2, v___x_1248_);
                    v___x_1250_ = v___x_1232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_key_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_value_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 2, v___x_1248_);
                    v___x_1250_ = v_reuseFailAlloc_1253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1251_ = lean_array_uset(v_x_1226_, v___x_1247_, v___x_1250_);
                v_x_1226_ = v___x_1251_;
                v_x_1227_ = v_tail_1230_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(
    mut v_i_1255_: *mut crate::leanh::LeanObject,
    mut v_source_1256_: *mut crate::leanh::LeanObject,
    mut v_target_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: u8 = 0;
    let mut v_es_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1258_ = lean_array_get_size(v_source_1256_);
                v___x_1259_ = lean_nat_dec_lt(v_i_1255_, v___x_1258_);
                if v___x_1259_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1256_);
                    crate::leanh::lean_dec(v_i_1255_);
                    return v_target_1257_;
                } else {
                    v_es_1260_ = lean_array_fget(v_source_1256_, v_i_1255_);
                    v___x_1261_ = crate::leanh::lean_box(0);
                    v_source_1262_ = lean_array_fset(v_source_1256_, v_i_1255_, v___x_1261_);
                    v_target_1263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1257_, v_es_1260_);
                    v___x_1264_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1265_ = lean_nat_add(v_i_1255_, v___x_1264_);
                    crate::leanh::lean_dec(v_i_1255_);
                    v_i_1255_ = v___x_1265_;
                    v_source_1256_ = v_source_1262_;
                    v_target_1257_ = v_target_1263_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(
    mut v_data_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = lean_array_get_size(v_data_1267_);
    v___x_1269_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1270_ = lean_nat_mul(v___x_1268_, v___x_1269_);
    v___x_1271_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1272_ = crate::leanh::lean_box(0);
    v___x_1273_ = lean_mk_array(v_nbuckets_1270_, v___x_1272_);
    v___x_1274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v___x_1271_, v_data_1267_, v___x_1273_);
    return v___x_1274_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(
    mut v_m_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: u64,
    mut v_b_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    let mut v_fold_1283_: u64 = 0;
    let mut v___x_1284_: u64 = 0;
    let mut v___x_1285_: u64 = 0;
    let mut v___x_1286_: u64 = 0;
    let mut v___x_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v_bkt_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v_val_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v_unused_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1278_ = crate::leanh::lean_ctor_get(v_m_1275_, 0);
                v_buckets_1279_ = crate::leanh::lean_ctor_get(v_m_1275_, 1);
                v___x_1280_ = lean_array_get_size(v_buckets_1279_);
                v___x_1281_ = 32u64;
                v___x_1282_ = lean_uint64_shift_right(v_a_1276_, v___x_1281_);
                v_fold_1283_ = lean_uint64_xor(v_a_1276_, v___x_1282_);
                v___x_1284_ = 16u64;
                v___x_1285_ = lean_uint64_shift_right(v_fold_1283_, v___x_1284_);
                v___x_1286_ = lean_uint64_xor(v_fold_1283_, v___x_1285_);
                v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
                v___x_1288_ = lean_usize_of_nat(v___x_1280_);
                v___x_1289_ = 1usize;
                v___x_1290_ = lean_usize_sub(v___x_1288_, v___x_1289_);
                v___x_1291_ = lean_usize_land(v___x_1287_, v___x_1290_);
                v_bkt_1292_ = lean_array_uget_borrowed(v_buckets_1279_, v___x_1291_);
                v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_1276_, v_bkt_1292_);
                if v___x_1293_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1279_);
                    crate::leanh::lean_inc(v_size_1278_);
                    v_isSharedCheck_1315_ = (!crate::leanh::lean_is_exclusive(v_m_1275_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v_unused_1316_ = crate::leanh::lean_ctor_get(v_m_1275_, 1);
                        crate::leanh::lean_dec(v_unused_1316_);
                        v_unused_1317_ = crate::leanh::lean_ctor_get(v_m_1275_, 0);
                        crate::leanh::lean_dec(v_unused_1317_);
                        v___x_1295_ = v_m_1275_;
                        v_isShared_1296_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1275_);
                        v___x_1295_ = crate::leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1277_);
                    return v_m_1275_;
                }
            }
            1 => {
                v___x_1297_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1298_ = lean_nat_add(v_size_1278_, v___x_1297_);
                crate::leanh::lean_dec(v_size_1278_);
                v___x_1299_ = crate::leanh::lean_box_uint64(v_a_1276_);
                crate::leanh::lean_inc(v_bkt_1292_);
                v___x_1300_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1299_);
                crate::leanh::lean_ctor_set(v___x_1300_, 1, v_b_1277_);
                crate::leanh::lean_ctor_set(v___x_1300_, 2, v_bkt_1292_);
                v_buckets_x27_1301_ = lean_array_uset(v_buckets_1279_, v___x_1291_, v___x_1300_);
                v___x_1302_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1303_ = lean_nat_mul(v_size_x27_1298_, v___x_1302_);
                v___x_1304_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1305_ = lean_nat_div(v___x_1303_, v___x_1304_);
                crate::leanh::lean_dec(v___x_1303_);
                v___x_1306_ = lean_array_get_size(v_buckets_x27_1301_);
                v___x_1307_ = lean_nat_dec_le(v___x_1305_, v___x_1306_);
                crate::leanh::lean_dec(v___x_1305_);
                if v___x_1307_ == 0 {
                    v_val_1308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_buckets_x27_1301_);
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 1, v_val_1308_);
                        crate::leanh::lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1310_ = v___x_1295_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_size_x27_1298_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_val_1308_);
                        v___x_1310_ = v_reuseFailAlloc_1311_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 1, v_buckets_x27_1301_);
                        crate::leanh::lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1313_ = v___x_1295_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_size_x27_1298_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_buckets_x27_1301_);
                        v___x_1313_ = v_reuseFailAlloc_1314_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1310_;
            }
            3 => {
                return v___x_1313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(
    mut v_m_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_b_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1321_: u64 = 0;
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1321_ = crate::leanh::lean_unbox_uint64(v_a_1319_);
    crate::leanh::lean_dec_ref(v_a_1319_);
    v_res_1322_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_1318_, v_a_boxed_1321_, v_b_1320_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(
    mut v_c_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visited_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addr_1327_: u64 = 0;
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut v_unused_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_1325_ = crate::leanh::lean_ctor_get(v_a_1324_, 0);
                v_found_1326_ = crate::leanh::lean_ctor_get(v_a_1324_, 1);
                v_addr_1327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_1323_);
                v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_visited_1325_, v_addr_1327_);
                if v___x_1328_ == 0 {
                    crate::leanh::lean_inc(v_found_1326_);
                    crate::leanh::lean_inc_ref(v_visited_1325_);
                    v_isSharedCheck_1339_ = (!crate::leanh::lean_is_exclusive(v_a_1324_)) as u8;
                    if v_isSharedCheck_1339_ == 0 {
                        v_unused_1340_ = crate::leanh::lean_ctor_get(v_a_1324_, 1);
                        crate::leanh::lean_dec(v_unused_1340_);
                        v_unused_1341_ = crate::leanh::lean_ctor_get(v_a_1324_, 0);
                        crate::leanh::lean_dec(v_unused_1341_);
                        v___x_1330_ = v_a_1324_;
                        v_isShared_1331_ = v_isSharedCheck_1339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1324_);
                        v___x_1330_ = crate::leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1339_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1342_ = crate::leanh::lean_box((v___x_1328_) as usize);
                    v___x_1343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1343_, 0, v___x_1342_);
                    crate::leanh::lean_ctor_set(v___x_1343_, 1, v_a_1324_);
                    return v___x_1343_;
                }
            }
            1 => {
                v___x_1332_ = crate::leanh::lean_box(0);
                v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_visited_1325_, v_addr_1327_, v___x_1332_);
                if v_isShared_1331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_found_1326_);
                    v___x_1335_ = v_reuseFailAlloc_1338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1336_ = crate::leanh::lean_box((v___x_1328_) as usize);
                v___x_1337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
                crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1335_);
                return v___x_1337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(
    mut v_c_1344_: *mut crate::leanh::LeanObject,
    mut v_a_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ =
        l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_1344_, v_a_1345_);
    crate::leanh::lean_dec(v_c_1344_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(
    mut v_00_u03b1_1347_: *mut crate::leanh::LeanObject,
    mut v_c_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ =
        l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_1348_, v_a_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(
    mut v_00_u03b1_1352_: *mut crate::leanh::LeanObject,
    mut v_c_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(
        v_00_u03b1_1352_,
        v_c_1353_,
        v_a_1354_,
        v_a_1355_,
    );
    crate::leanh::lean_dec(v_a_1354_);
    crate::leanh::lean_dec(v_c_1353_);
    return v_res_1356_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(
    mut v_00_u03b2_1357_: *mut crate::leanh::LeanObject,
    mut v_m_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: u64,
) -> u8 {
    let mut v___x_1360_: u8 = 0;
    v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_1358_, v_a_1359_);
    return v___x_1360_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(
    mut v_00_u03b2_1361_: *mut crate::leanh::LeanObject,
    mut v_m_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1364_: u64 = 0;
    let mut v_res_1365_: u8 = 0;
    let mut v_r_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1364_ = crate::leanh::lean_unbox_uint64(v_a_1363_);
    crate::leanh::lean_dec_ref(v_a_1363_);
    v_res_1365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(v_00_u03b2_1361_, v_m_1362_, v_a_boxed_1364_);
    crate::leanh::lean_dec_ref(v_m_1362_);
    v_r_1366_ = crate::leanh::lean_box((v_res_1365_) as usize);
    return v_r_1366_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(
    mut v_00_u03b2_1367_: *mut crate::leanh::LeanObject,
    mut v_m_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: u64,
    mut v_b_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_1368_, v_a_1369_, v_b_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_m_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_b_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1376_: u64 = 0;
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1376_ = crate::leanh::lean_unbox_uint64(v_a_1374_);
    crate::leanh::lean_dec_ref(v_a_1374_);
    v_res_1377_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(v_00_u03b2_1372_, v_m_1373_, v_a_boxed_1376_, v_b_1375_);
    return v_res_1377_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(
    mut v_00_u03b2_1378_: *mut crate::leanh::LeanObject,
    mut v_a_1379_: u64,
    mut v_x_1380_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1381_: u8 = 0;
    v___x_1381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_1379_, v_x_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(
    mut v_00_u03b2_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_x_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1385_: u64 = 0;
    let mut v_res_1386_: u8 = 0;
    let mut v_r_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1385_ = crate::leanh::lean_unbox_uint64(v_a_1383_);
    crate::leanh::lean_dec_ref(v_a_1383_);
    v_res_1386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(v_00_u03b2_1382_, v_a_boxed_1385_, v_x_1384_);
    crate::leanh::lean_dec(v_x_1384_);
    v_r_1387_ = crate::leanh::lean_box((v_res_1386_) as usize);
    return v_r_1387_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(
    mut v_00_u03b2_1388_: *mut crate::leanh::LeanObject,
    mut v_data_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_data_1389_);
    return v___x_1390_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1391_: *mut crate::leanh::LeanObject,
    mut v_i_1392_: *mut crate::leanh::LeanObject,
    mut v_source_1393_: *mut crate::leanh::LeanObject,
    mut v_target_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v_i_1392_, v_source_1393_, v_target_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1396_: *mut crate::leanh::LeanObject,
    mut v_x_1397_: *mut crate::leanh::LeanObject,
    mut v_x_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1397_, v_x_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(
    mut v_fvarId_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visited_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_1402_ = crate::leanh::lean_ctor_get(v_a_1401_, 0);
                v_found_1403_ = crate::leanh::lean_ctor_get(v_a_1401_, 1);
                v_isSharedCheck_1413_ = (!crate::leanh::lean_is_exclusive(v_a_1401_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1405_ = v_a_1401_;
                    v_isShared_1406_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_found_1403_);
                    crate::leanh::lean_inc(v_visited_1402_);
                    crate::leanh::lean_dec(v_a_1401_);
                    v___x_1405_ = crate::leanh::lean_box(0);
                    v_isShared_1406_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1407_ = crate::leanh::lean_box(0);
                v___x_1408_ = l_Lean_FVarIdSet_insert(v_found_1403_, v_fvarId_1400_);
                if v_isShared_1406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1405_, 1, v___x_1408_);
                    v___x_1410_ = v___x_1405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_visited_1402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1408_);
                    v___x_1410_ = v_reuseFailAlloc_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1411_, 0, v___x_1407_);
                crate::leanh::lean_ctor_set(v___x_1411_, 1, v___x_1410_);
                return v___x_1411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(
    mut v_fvarId_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ =
        l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(v_fvarId_1414_, v_a_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(
    mut v_fvarId_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ =
        l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(v_fvarId_1418_, v_a_1419_, v_a_1420_);
    crate::leanh::lean_dec(v_a_1419_);
    return v_res_1421_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = crate::leanh::lean_box(0);
    v___x_1423_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1424_ = lean_mk_array(v___x_1423_, v___x_1422_);
    return v___x_1424_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0,
    );
    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1427_, 0, v___x_1426_);
    crate::leanh::lean_ctor_set(v___x_1427_, 1, v___x_1425_);
    return v___x_1427_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = crate::leanh::lean_box(1);
    v___x_1429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1,
    );
    v___x_1430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    crate::leanh::lean_ctor_set(v___x_1430_, 1, v___x_1428_);
    return v___x_1430_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(
    mut v_x_1431_: *mut crate::leanh::LeanObject,
    mut v_decVars_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2,
    );
    v___x_1434_ = crate::leanh::lean_apply_2(v_x_1431_, v_decVars_1432_, v___x_1433_);
    v_snd_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 1);
    crate::leanh::lean_inc(v_snd_1435_);
    crate::leanh::lean_dec_ref(v___x_1434_);
    v_found_1436_ = crate::leanh::lean_ctor_get(v_snd_1435_, 1);
    crate::leanh::lean_inc(v_found_1436_);
    crate::leanh::lean_dec(v_snd_1435_);
    return v_found_1436_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________()
-> u8 {
    let mut v___x_1437_: u8 = 0;
    v___x_1437_ = 1;
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = crate::leanh::lean_box(0);
    v___x_1486_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20;
    v___x_1487_ = l_Lean_mkConst(v___x_1486_, v___x_1485_);
    return v___x_1487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once
        ),
        _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21,
    );
    return v___x_1488_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(
    mut v_parent_x3f_1489_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_parent_x3f_1489_) == 0 {
        let mut v___x_1490_: u8 = 0;
        v___x_1490_ = 0;
        return v___x_1490_;
    } else {
        let mut v_val_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: u8 = 0;
        v_val_1491_ = crate::leanh::lean_ctor_get(v_parent_x3f_1489_, 0);
        v___x_1492_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
        v___x_1493_ = lean_expr_eqv(v_val_1491_, v___x_1492_);
        return v___x_1493_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(
    mut v_parent_x3f_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: u8 = 0;
    let mut v_r_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_1494_);
    crate::leanh::lean_dec(v_parent_x3f_1494_);
    v_r_1496_ = crate::leanh::lean_box((v_res_1495_) as usize);
    return v_r_1496_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_split___redArg___lam__0(
    mut v_getCoeff_1497_: *mut crate::leanh::LeanObject,
    mut v___x_1498_: *mut crate::leanh::LeanObject,
    mut v_c_1499_: *mut crate::leanh::LeanObject,
    mut v_____s_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v_b_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1501_ = crate::leanh::lean_ctor_get(v_____s_1500_, 0);
                v_snd_1502_ = crate::leanh::lean_ctor_get(v_____s_1500_, 1);
                v_isSharedCheck_1520_ = (!crate::leanh::lean_is_exclusive(v_____s_1500_)) as u8;
                if v_isSharedCheck_1520_ == 0 {
                    v___x_1504_ = v_____s_1500_;
                    v_isShared_1505_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1502_);
                    crate::leanh::lean_inc(v_fst_1501_);
                    crate::leanh::lean_dec(v_____s_1500_);
                    v___x_1504_ = crate::leanh::lean_box(0);
                    v_isShared_1505_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_c_1499_);
                v_b_1506_ = crate::leanh::lean_apply_1(v_getCoeff_1497_, v_c_1499_);
                v___x_1507_ = lean_nat_to_int(v___x_1498_);
                v___x_1508_ = lean_int_dec_eq(v_b_1506_, v___x_1507_);
                crate::leanh::lean_dec(v___x_1507_);
                if v___x_1508_ == 0 {
                    if v_isShared_1505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1504_, 1, v_c_1499_);
                        crate::leanh::lean_ctor_set(v___x_1504_, 0, v_b_1506_);
                        v___x_1510_ = v___x_1504_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_b_1506_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_c_1499_);
                        v___x_1510_ = v_reuseFailAlloc_1514_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1506_);
                    v_cs_x27_1515_ = l_Lean_PersistentArray_push___redArg(v_fst_1501_, v_c_1499_);
                    if v_isShared_1505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1504_, 0, v_cs_x27_1515_);
                        v___x_1517_ = v___x_1504_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_cs_x27_1515_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_snd_1502_);
                        v___x_1517_ = v_reuseFailAlloc_1519_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_todo_1511_ = lean_array_push(v_snd_1502_, v___x_1510_);
                v___x_1512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1512_, 0, v_fst_1501_);
                crate::leanh::lean_ctor_set(v___x_1512_, 1, v_todo_1511_);
                v___x_1513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
                return v___x_1513_;
            }
            3 => {
                v___x_1518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1541_ = lean_mk_empty_array_with_capacity(v___x_1540_);
    v___x_1542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: usize = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = 5usize;
    v___x_1544_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1545_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1546_ = lean_mk_empty_array_with_capacity(v___x_1545_);
    v___x_1547_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_split___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once),
        _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10,
    );
    v_cs_x27_1548_ =
        crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v_cs_x27_1548_, 0, v___x_1547_);
    crate::leanh::lean_ctor_set(v_cs_x27_1548_, 1, v___x_1546_);
    crate::leanh::lean_ctor_set(v_cs_x27_1548_, 2, v___x_1544_);
    crate::leanh::lean_ctor_set(v_cs_x27_1548_, 3, v___x_1544_);
    crate::leanh::lean_ctor_set_usize(v_cs_x27_1548_, 4, v___x_1543_);
    return v_cs_x27_1548_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v_todo_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_todo_1551_ = l_Lean_Meta_Grind_Arith_split___redArg___closed__12;
    v_cs_x27_1552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_split___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once),
        _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11,
    );
    v___x_1553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1553_, 0, v_cs_x27_1552_);
    crate::leanh::lean_ctor_set(v___x_1553_, 1, v_todo_1551_);
    return v___x_1553_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_split___redArg(
    mut v_cs_1554_: *mut crate::leanh::LeanObject,
    mut v_getCoeff_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1556_ = l_Lean_Meta_Grind_Arith_split___redArg___closed__9;
                v___x_1557_ = crate::leanh::lean_unsigned_to_nat(0);
                v___f_1558_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_split___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1558_, 0, v_getCoeff_1555_);
                crate::leanh::lean_closure_set(v___f_1558_, 1, v___x_1557_);
                v___x_1559_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_split___redArg___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13,
                );
                v___x_1560_ = l_Lean_PersistentArray_forIn___redArg(
                    v___x_1556_,
                    v_cs_1554_,
                    v___x_1559_,
                    v___f_1558_,
                );
                v_fst_1561_ = crate::leanh::lean_ctor_get(v___x_1560_, 0);
                v_snd_1562_ = crate::leanh::lean_ctor_get(v___x_1560_, 1);
                v_isSharedCheck_1569_ = (!crate::leanh::lean_is_exclusive(v___x_1560_)) as u8;
                if v_isSharedCheck_1569_ == 0 {
                    v___x_1564_ = v___x_1560_;
                    v_isShared_1565_ = v_isSharedCheck_1569_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1562_);
                    crate::leanh::lean_inc(v_fst_1561_);
                    crate::leanh::lean_dec(v___x_1560_);
                    v___x_1564_ = crate::leanh::lean_box(0);
                    v_isShared_1565_ = v_isSharedCheck_1569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1565_ == 0 {
                    v___x_1567_ = v___x_1564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_fst_1561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_snd_1562_);
                    v___x_1567_ = v_reuseFailAlloc_1568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_split___redArg___boxed(
    mut v_cs_1570_: *mut crate::leanh::LeanObject,
    mut v_getCoeff_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1572_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_1570_, v_getCoeff_1571_);
    crate::leanh::lean_dec_ref(v_cs_1570_);
    return v_res_1572_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_split(
    mut v_00_u03b1_1573_: *mut crate::leanh::LeanObject,
    mut v_cs_1574_: *mut crate::leanh::LeanObject,
    mut v_getCoeff_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_1574_, v_getCoeff_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_split___boxed(
    mut v_00_u03b1_1577_: *mut crate::leanh::LeanObject,
    mut v_cs_1578_: *mut crate::leanh::LeanObject,
    mut v_getCoeff_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1580_ = l_Lean_Meta_Grind_Arith_split(v_00_u03b1_1577_, v_cs_1578_, v_getCoeff_1579_);
    crate::leanh::lean_dec_ref(v_cs_1578_);
    return v_res_1580_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________ = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________();
    l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent =
        _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
}

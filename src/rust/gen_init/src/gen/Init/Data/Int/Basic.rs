// Lean compiler output
// Module: Init.Data.Int.Basic
// Imports: Init.Data.Cast Init.Data.Nat.Basic
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_dec_nonneg,
    lean_int_mul, lean_int_neg, lean_int_neg_succ_of_nat, lean_int_sub, lean_nat_abs,
    lean_nat_dec_eq, lean_nat_mod, lean_nat_pow, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Cast::{
    initialize_Init_Data_Cast, runtime_initialize_Init_Data_Cast,
};
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_instNatCastInt_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_instNatCastInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instNatCastInt_value) as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 45, 91, 95, 43, 49, 93, 0],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15996623541710606861 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [45, 91, 0],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [43, 49, 93, 0],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Int_term_x2d_x5b___x2b1_x5d___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Int_term_x2d_x5b___x2b1_x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 101, 103, 83, 117, 99, 99, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value) as *mut crate::leanh::LeanObject,10068894647755430579 as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int_term_x2d_x5b___x2b1_x5d___closed__0_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5_value) as *mut crate::leanh::LeanObject,14511501467246783669 as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value:
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
        core::ptr::addr_of!(
            l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Int_instInhabited___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_instInhabited___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Int_instInhabited: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Int_instNegInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instNegInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instNegInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instNegInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instNegInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instAdd___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instAdd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instAdd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instAdd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instAdd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instMul___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instMul___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMul___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instMul: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMul___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instSub___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instSub___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instSub___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instSub: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instSub___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instLEInt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Int_instLTInt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int_sign___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_sign___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int_sign___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_sign___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Int_instDvd: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Int_instNatPow___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instNatPow___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instNatPow___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instNatPow: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instNatPow___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instMin___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_instMin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instMin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instMin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int_instMax___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int_instMax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int_instMax: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instIntCastInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instIntCastInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instIntCastInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instIntCastInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instIntCastInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instIntCastInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Int_ofNat___boxed(
    mut v_a_00___x40___internal___hyg_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ = lean_nat_to_int(v_a_00___x40___internal___hyg_379_);
    return v_res_380_;
}
pub unsafe fn l_Int_negSucc___boxed(
    mut v_a_00___x40___internal___hyg_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_383_ = lean_int_neg_succ_of_nat(v_a_00___x40___internal___hyg_382_);
    return v_res_383_;
}
pub unsafe fn l_instOfNat(
    mut v_n_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_386_ = lean_nat_to_int(v_n_385_);
    return v___x_386_;
}
pub unsafe fn _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__5;
    v___x_431_ = l_String_toRawSubstring_x27(v___x_430_);
    return v___x_431_;
}
pub unsafe fn l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(
    mut v_x_451_: *mut crate::leanh::LeanObject,
    mut v_a_452_: *mut crate::leanh::LeanObject,
    mut v_a_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    v___x_454_ = l_Int_term_x2d_x5b___x2b1_x5d___closed__2;
    crate::leanh::lean_inc(v_x_451_);
    v___x_455_ = l_Lean_Syntax_isOfKind(v_x_451_, v___x_454_);
    if v___x_455_ == 0 {
        let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_451_);
        v___x_456_ = crate::leanh::lean_box(1);
        v___x_457_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_457_, 0, v___x_456_);
        crate::leanh::lean_ctor_set(v___x_457_, 1, v_a_453_);
        return v___x_457_;
    } else {
        let mut v_quotContext_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_463_: u8 = 0;
        let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_458_ = crate::leanh::lean_ctor_get(v_a_452_, 1);
        v_currMacroScope_459_ = crate::leanh::lean_ctor_get(v_a_452_, 2);
        v_ref_460_ = crate::leanh::lean_ctor_get(v_a_452_, 5);
        v___x_461_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_462_ = l_Lean_Syntax_getArg(v_x_451_, v___x_461_);
        crate::leanh::lean_dec(v_x_451_);
        v___x_463_ = 0;
        v___x_464_ = l_Lean_SourceInfo_fromRef(v_ref_460_, v___x_463_);
        v___x_465_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4;
        v___x_466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6), core::ptr::addr_of_mut!(l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6_once), _init_l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__6);
        v___x_467_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_459_);
        crate::leanh::lean_inc(v_quotContext_458_);
        v___x_468_ = l_Lean_addMacroScope(v_quotContext_458_, v___x_467_, v_currMacroScope_459_);
        v___x_469_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__12;
        crate::leanh::lean_inc_n(v___x_464_, 2);
        v___x_470_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_470_, 0, v___x_464_);
        crate::leanh::lean_ctor_set(v___x_470_, 1, v___x_466_);
        crate::leanh::lean_ctor_set(v___x_470_, 2, v___x_468_);
        crate::leanh::lean_ctor_set(v___x_470_, 3, v___x_469_);
        v___x_471_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__14;
        v___x_472_ = l_Lean_Syntax_node1(v___x_464_, v___x_471_, v___x_462_);
        v___x_473_ = l_Lean_Syntax_node2(v___x_464_, v___x_465_, v___x_470_, v___x_472_);
        v___x_474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_474_, 0, v___x_473_);
        crate::leanh::lean_ctor_set(v___x_474_, 1, v_a_453_);
        return v___x_474_;
    }
}
pub unsafe fn l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___boxed(
    mut v_x_475_: *mut crate::leanh::LeanObject,
    mut v_a_476_: *mut crate::leanh::LeanObject,
    mut v_a_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ =
        l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1(
            v_x_475_, v_a_476_, v_a_477_,
        );
    crate::leanh::lean_dec_ref(v_a_476_);
    return v_res_478_;
}
pub unsafe fn l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(
    mut v_x_482_: *mut crate::leanh::LeanObject,
    mut v_a_483_: *mut crate::leanh::LeanObject,
    mut v_a_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    v___x_485_ = l_Int___aux__Init__Data__Int__Basic______macroRules__Int__term_x2d_x5b___x2b1_x5d__1___closed__4;
    crate::leanh::lean_inc(v_x_482_);
    v___x_486_ = l_Lean_Syntax_isOfKind(v_x_482_, v___x_485_);
    if v___x_486_ == 0 {
        let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_482_);
        v___x_487_ = crate::leanh::lean_box(0);
        v___x_488_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_488_, 0, v___x_487_);
        crate::leanh::lean_ctor_set(v___x_488_, 1, v_a_484_);
        return v___x_488_;
    } else {
        let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_492_: u8 = 0;
        v___x_489_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_490_ = l_Lean_Syntax_getArg(v_x_482_, v___x_489_);
        v___x_491_ = l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___closed__1;
        crate::leanh::lean_inc(v___x_490_);
        v___x_492_ = l_Lean_Syntax_isOfKind(v___x_490_, v___x_491_);
        if v___x_492_ == 0 {
            let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_490_);
            crate::leanh::lean_dec(v_x_482_);
            v___x_493_ = crate::leanh::lean_box(0);
            v___x_494_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_494_, 0, v___x_493_);
            crate::leanh::lean_ctor_set(v___x_494_, 1, v_a_484_);
            return v___x_494_;
        } else {
            let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: u8 = 0;
            v___x_495_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_496_ = l_Lean_Syntax_getArg(v_x_482_, v___x_495_);
            crate::leanh::lean_dec(v_x_482_);
            crate::leanh::lean_inc(v___x_496_);
            v___x_497_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_495_);
            if v___x_497_ == 0 {
                let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_496_);
                crate::leanh::lean_dec(v___x_490_);
                v___x_498_ = crate::leanh::lean_box(0);
                v___x_499_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_499_, 0, v___x_498_);
                crate::leanh::lean_ctor_set(v___x_499_, 1, v_a_484_);
                return v___x_499_;
            } else {
                let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_502_: u8 = 0;
                let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_500_ = l_Lean_Syntax_getArg(v___x_496_, v___x_489_);
                crate::leanh::lean_dec(v___x_496_);
                v_ref_501_ = l_Lean_replaceRef(v___x_490_, v_a_483_);
                crate::leanh::lean_dec(v___x_490_);
                v___x_502_ = 0;
                v___x_503_ = l_Lean_SourceInfo_fromRef(v_ref_501_, v___x_502_);
                crate::leanh::lean_dec(v_ref_501_);
                v___x_504_ = l_Int_term_x2d_x5b___x2b1_x5d___closed__2;
                v___x_505_ = l_Int_term_x2d_x5b___x2b1_x5d___closed__5;
                crate::leanh::lean_inc_n(v___x_503_, 2);
                v___x_506_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_506_, 0, v___x_503_);
                crate::leanh::lean_ctor_set(v___x_506_, 1, v___x_505_);
                v___x_507_ = l_Int_term_x2d_x5b___x2b1_x5d___closed__11;
                v___x_508_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_508_, 0, v___x_503_);
                crate::leanh::lean_ctor_set(v___x_508_, 1, v___x_507_);
                v___x_509_ =
                    l_Lean_Syntax_node3(v___x_503_, v___x_504_, v___x_506_, v___x_500_, v___x_508_);
                v___x_510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_510_, 0, v___x_509_);
                crate::leanh::lean_ctor_set(v___x_510_, 1, v_a_484_);
                return v___x_510_;
            }
        }
    }
}
pub unsafe fn l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1___boxed(
    mut v_x_511_: *mut crate::leanh::LeanObject,
    mut v_a_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_514_ = l_Int___aux__Init__Data__Int__Basic______unexpand__Int__negSucc__1(
        v_x_511_, v_a_512_, v_a_513_,
    );
    crate::leanh::lean_dec(v_a_512_);
    return v_res_514_;
}
pub unsafe fn _init_l_Int_instInhabited___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_515_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_516_ = lean_nat_to_int(v___x_515_);
    return v___x_516_;
}
pub unsafe fn _init_l_Int_instInhabited() -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    return v___x_517_;
}
pub unsafe fn l_Int_negOfNat(
    mut v_x_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_520_: u8 = 0;
    v_zero_519_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_520_ = lean_nat_dec_eq(v_x_518_, v_zero_519_);
    if v_isZero_520_ == 1 {
        let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_521_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
            core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
            _init_l_Int_instInhabited___closed__0,
        );
        return v___x_521_;
    } else {
        let mut v_one_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_522_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_523_ = lean_nat_sub(v_x_518_, v_one_522_);
        v___x_524_ = lean_int_neg_succ_of_nat(v_n_523_);
        return v___x_524_;
    }
}
pub unsafe fn l_Int_negOfNat___boxed(
    mut v_x_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Int_negOfNat(v_x_525_);
    crate::leanh::lean_dec(v_x_525_);
    return v_res_526_;
}
pub unsafe fn l_Int_neg___boxed(
    mut v_n_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_529_ = lean_int_neg(v_n_528_);
    crate::leanh::lean_dec(v_n_528_);
    return v_res_529_;
}
pub unsafe fn l_Int_subNatNat(
    mut v_m_532_: *mut crate::leanh::LeanObject,
    mut v_n_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_536_: u8 = 0;
    v___x_534_ = lean_nat_sub(v_n_533_, v_m_532_);
    v_zero_535_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_536_ = lean_nat_dec_eq(v___x_534_, v_zero_535_);
    if v_isZero_536_ == 1 {
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_534_);
        v___x_537_ = lean_nat_sub(v_m_532_, v_n_533_);
        v___x_538_ = lean_nat_to_int(v___x_537_);
        return v___x_538_;
    } else {
        let mut v_one_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_539_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_540_ = lean_nat_sub(v___x_534_, v_one_539_);
        crate::leanh::lean_dec(v___x_534_);
        v___x_541_ = lean_int_neg_succ_of_nat(v_n_540_);
        return v___x_541_;
    }
}
pub unsafe fn l_Int_subNatNat___boxed(
    mut v_m_542_: *mut crate::leanh::LeanObject,
    mut v_n_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_544_ = l_Int_subNatNat(v_m_542_, v_n_543_);
    crate::leanh::lean_dec(v_n_543_);
    crate::leanh::lean_dec(v_m_542_);
    return v_res_544_;
}
pub unsafe fn l_Int_add___boxed(
    mut v_m_547_: *mut crate::leanh::LeanObject,
    mut v_n_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = lean_int_add(v_m_547_, v_n_548_);
    crate::leanh::lean_dec(v_n_548_);
    crate::leanh::lean_dec(v_m_547_);
    return v_res_549_;
}
pub unsafe fn l_Int_mul___boxed(
    mut v_m_554_: *mut crate::leanh::LeanObject,
    mut v_n_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_556_ = lean_int_mul(v_m_554_, v_n_555_);
    crate::leanh::lean_dec(v_n_555_);
    crate::leanh::lean_dec(v_m_554_);
    return v_res_556_;
}
pub unsafe fn l_Int_sub___boxed(
    mut v_m_561_: *mut crate::leanh::LeanObject,
    mut v_n_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = lean_int_sub(v_m_561_, v_n_562_);
    crate::leanh::lean_dec(v_n_562_);
    crate::leanh::lean_dec(v_m_561_);
    return v_res_563_;
}
pub unsafe fn _init_l_Int_instLEInt() -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = crate::leanh::lean_box(0);
    return v___x_566_;
}
pub unsafe fn _init_l_Int_instLTInt() -> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = crate::leanh::lean_box(0);
    return v___x_567_;
}
pub unsafe fn l_Int_decEq___boxed(
    mut v_a_570_: *mut crate::leanh::LeanObject,
    mut v_b_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_572_: u8 = 0;
    let mut v_r_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = lean_int_dec_eq(v_a_570_, v_b_571_);
    crate::leanh::lean_dec(v_b_571_);
    crate::leanh::lean_dec(v_a_570_);
    v_r_573_ = crate::leanh::lean_box((v_res_572_) as usize);
    return v_r_573_;
}
pub unsafe fn l_Int_instDecidableEq(
    mut v_a_574_: *mut crate::leanh::LeanObject,
    mut v_b_575_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_576_: u8 = 0;
    v___x_576_ = lean_int_dec_eq(v_a_574_, v_b_575_);
    return v___x_576_;
}
pub unsafe fn l_Int_instDecidableEq___boxed(
    mut v_a_577_: *mut crate::leanh::LeanObject,
    mut v_b_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_579_: u8 = 0;
    let mut v_r_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Int_instDecidableEq(v_a_577_, v_b_578_);
    crate::leanh::lean_dec(v_b_578_);
    crate::leanh::lean_dec(v_a_577_);
    v_r_580_ = crate::leanh::lean_box((v_res_579_) as usize);
    return v_r_580_;
}
pub unsafe fn l_Int_decNonneg___boxed(
    mut v_m_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_583_: u8 = 0;
    let mut v_r_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_583_ = lean_int_dec_nonneg(v_m_582_);
    crate::leanh::lean_dec(v_m_582_);
    v_r_584_ = crate::leanh::lean_box((v_res_583_) as usize);
    return v_r_584_;
}
pub unsafe fn l_Int_decLe___boxed(
    mut v_a_587_: *mut crate::leanh::LeanObject,
    mut v_b_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_589_: u8 = 0;
    let mut v_r_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_589_ = lean_int_dec_le(v_a_587_, v_b_588_);
    crate::leanh::lean_dec(v_b_588_);
    crate::leanh::lean_dec(v_a_587_);
    v_r_590_ = crate::leanh::lean_box((v_res_589_) as usize);
    return v_r_590_;
}
pub unsafe fn l_Int_decLt___boxed(
    mut v_a_593_: *mut crate::leanh::LeanObject,
    mut v_b_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_595_: u8 = 0;
    let mut v_r_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_595_ = lean_int_dec_lt(v_a_593_, v_b_594_);
    crate::leanh::lean_dec(v_b_594_);
    crate::leanh::lean_dec(v_a_593_);
    v_r_596_ = crate::leanh::lean_box((v_res_595_) as usize);
    return v_r_596_;
}
pub unsafe fn l_Int_natAbs___boxed(
    mut v_m_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = lean_nat_abs(v_m_598_);
    crate::leanh::lean_dec(v_m_598_);
    return v_res_599_;
}
pub unsafe fn l_Int_ctorIdx(
    mut v_x_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_603_: u8 = 0;
    v_natZero_601_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_602_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_603_ = lean_int_dec_lt(v_x_600_, v_intZero_602_);
    if v_isNeg_603_ == 0 {
        return v_natZero_601_;
    } else {
        let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_604_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_604_;
    }
}
pub unsafe fn l_Int_ctorIdx___boxed(
    mut v_x_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l_Int_ctorIdx(v_x_605_);
    crate::leanh::lean_dec(v_x_605_);
    return v_res_606_;
}
pub unsafe fn l_Int_ctorElim___redArg(
    mut v_t_607_: *mut crate::leanh::LeanObject,
    mut v_k_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_610_: u8 = 0;
    v_intZero_609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_610_ = lean_int_dec_lt(v_t_607_, v_intZero_609_);
    if v_isNeg_610_ == 0 {
        let mut v_a_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_611_ = lean_nat_abs(v_t_607_);
        v___x_612_ = crate::leanh::lean_apply_1(v_k_608_, v_a_611_);
        return v___x_612_;
    } else {
        let mut v_abs_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_abs_613_ = lean_nat_abs(v_t_607_);
        v_one_614_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_615_ = lean_nat_sub(v_abs_613_, v_one_614_);
        crate::leanh::lean_dec(v_abs_613_);
        v___x_616_ = crate::leanh::lean_apply_1(v_k_608_, v_a_615_);
        return v___x_616_;
    }
}
pub unsafe fn l_Int_ctorElim___redArg___boxed(
    mut v_t_617_: *mut crate::leanh::LeanObject,
    mut v_k_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l_Int_ctorElim___redArg(v_t_617_, v_k_618_);
    crate::leanh::lean_dec(v_t_617_);
    return v_res_619_;
}
pub unsafe fn l_Int_ctorElim(
    mut v_motive_620_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_621_: *mut crate::leanh::LeanObject,
    mut v_t_622_: *mut crate::leanh::LeanObject,
    mut v_h_623_: *mut crate::leanh::LeanObject,
    mut v_k_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Int_ctorElim___redArg(v_t_622_, v_k_624_);
    return v___x_625_;
}
pub unsafe fn l_Int_ctorElim___boxed(
    mut v_motive_626_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_627_: *mut crate::leanh::LeanObject,
    mut v_t_628_: *mut crate::leanh::LeanObject,
    mut v_h_629_: *mut crate::leanh::LeanObject,
    mut v_k_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Int_ctorElim(v_motive_626_, v_ctorIdx_627_, v_t_628_, v_h_629_, v_k_630_);
    crate::leanh::lean_dec(v_t_628_);
    crate::leanh::lean_dec(v_ctorIdx_627_);
    return v_res_631_;
}
pub unsafe fn l_Int_ofNat_elim___redArg(
    mut v_t_632_: *mut crate::leanh::LeanObject,
    mut v_ofNat_633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Int_ctorElim___redArg(v_t_632_, v_ofNat_633_);
    return v___x_634_;
}
pub unsafe fn l_Int_ofNat_elim___redArg___boxed(
    mut v_t_635_: *mut crate::leanh::LeanObject,
    mut v_ofNat_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l_Int_ofNat_elim___redArg(v_t_635_, v_ofNat_636_);
    crate::leanh::lean_dec(v_t_635_);
    return v_res_637_;
}
pub unsafe fn l_Int_ofNat_elim(
    mut v_motive_638_: *mut crate::leanh::LeanObject,
    mut v_t_639_: *mut crate::leanh::LeanObject,
    mut v_h_640_: *mut crate::leanh::LeanObject,
    mut v_ofNat_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = l_Int_ctorElim___redArg(v_t_639_, v_ofNat_641_);
    return v___x_642_;
}
pub unsafe fn l_Int_ofNat_elim___boxed(
    mut v_motive_643_: *mut crate::leanh::LeanObject,
    mut v_t_644_: *mut crate::leanh::LeanObject,
    mut v_h_645_: *mut crate::leanh::LeanObject,
    mut v_ofNat_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_647_ = l_Int_ofNat_elim(v_motive_643_, v_t_644_, v_h_645_, v_ofNat_646_);
    crate::leanh::lean_dec(v_t_644_);
    return v_res_647_;
}
pub unsafe fn l_Int_negSucc_elim___redArg(
    mut v_t_648_: *mut crate::leanh::LeanObject,
    mut v_negSucc_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = l_Int_ctorElim___redArg(v_t_648_, v_negSucc_649_);
    return v___x_650_;
}
pub unsafe fn l_Int_negSucc_elim___redArg___boxed(
    mut v_t_651_: *mut crate::leanh::LeanObject,
    mut v_negSucc_652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Int_negSucc_elim___redArg(v_t_651_, v_negSucc_652_);
    crate::leanh::lean_dec(v_t_651_);
    return v_res_653_;
}
pub unsafe fn l_Int_negSucc_elim(
    mut v_motive_654_: *mut crate::leanh::LeanObject,
    mut v_t_655_: *mut crate::leanh::LeanObject,
    mut v_h_656_: *mut crate::leanh::LeanObject,
    mut v_negSucc_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = l_Int_ctorElim___redArg(v_t_655_, v_negSucc_657_);
    return v___x_658_;
}
pub unsafe fn l_Int_negSucc_elim___boxed(
    mut v_motive_659_: *mut crate::leanh::LeanObject,
    mut v_t_660_: *mut crate::leanh::LeanObject,
    mut v_h_661_: *mut crate::leanh::LeanObject,
    mut v_negSucc_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Int_negSucc_elim(v_motive_659_, v_t_660_, v_h_661_, v_negSucc_662_);
    crate::leanh::lean_dec(v_t_660_);
    return v_res_663_;
}
pub unsafe fn _init_l_Int_sign___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_665_ = lean_nat_to_int(v___x_664_);
    return v___x_665_;
}
pub unsafe fn _init_l_Int_sign___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_sign___closed__0),
        core::ptr::addr_of_mut!(l_Int_sign___closed__0_once),
        _init_l_Int_sign___closed__0,
    );
    v___x_667_ = lean_int_neg(v___x_666_);
    return v___x_667_;
}
pub unsafe fn l_Int_sign(
    mut v_x_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_671_: u8 = 0;
    v_natZero_669_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_671_ = lean_int_dec_lt(v_x_668_, v_intZero_670_);
    if v_isNeg_671_ == 0 {
        let mut v_a_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_673_: u8 = 0;
        v_a_672_ = lean_nat_abs(v_x_668_);
        v_isZero_673_ = lean_nat_dec_eq(v_a_672_, v_natZero_669_);
        crate::leanh::lean_dec(v_a_672_);
        if v_isZero_673_ == 1 {
            return v_intZero_670_;
        } else {
            let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_674_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_sign___closed__0),
                core::ptr::addr_of_mut!(l_Int_sign___closed__0_once),
                _init_l_Int_sign___closed__0,
            );
            return v___x_674_;
        }
    } else {
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_675_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_sign___closed__1),
            core::ptr::addr_of_mut!(l_Int_sign___closed__1_once),
            _init_l_Int_sign___closed__1,
        );
        return v___x_675_;
    }
}
pub unsafe fn l_Int_sign___boxed(
    mut v_x_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Int_sign(v_x_676_);
    crate::leanh::lean_dec(v_x_676_);
    return v_res_677_;
}
pub unsafe fn l_Int_toNat(
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_681_: u8 = 0;
    v_natZero_679_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_681_ = lean_int_dec_lt(v_x_678_, v_intZero_680_);
    if v_isNeg_681_ == 0 {
        let mut v_a_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_682_ = lean_nat_abs(v_x_678_);
        return v_a_682_;
    } else {
        return v_natZero_679_;
    }
}
pub unsafe fn l_Int_toNat___boxed(
    mut v_x_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Int_toNat(v_x_683_);
    crate::leanh::lean_dec(v_x_683_);
    return v_res_684_;
}
pub unsafe fn l_Int_toNat_x3f(
    mut v_x_685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_687_: u8 = 0;
    v_intZero_686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_687_ = lean_int_dec_lt(v_x_685_, v_intZero_686_);
    if v_isNeg_687_ == 0 {
        let mut v_a_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_688_ = lean_nat_abs(v_x_685_);
        v___x_689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_689_, 0, v_a_688_);
        return v___x_689_;
    } else {
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_690_ = crate::leanh::lean_box(0);
        return v___x_690_;
    }
}
pub unsafe fn l_Int_toNat_x3f___boxed(
    mut v_x_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Int_toNat_x3f(v_x_691_);
    crate::leanh::lean_dec(v_x_691_);
    return v_res_692_;
}
pub unsafe fn _init_l_Int_instDvd() -> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = crate::leanh::lean_box(0);
    return v___x_693_;
}
pub unsafe fn l_Int_pow(
    mut v_x_694_: *mut crate::leanh::LeanObject,
    mut v_x_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_698_: u8 = 0;
    v_natZero_696_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_697_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Int_instInhabited___closed__0_once),
        _init_l_Int_instInhabited___closed__0,
    );
    v_isNeg_698_ = lean_int_dec_lt(v_x_694_, v_intZero_697_);
    if v_isNeg_698_ == 0 {
        let mut v_a_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_699_ = lean_nat_abs(v_x_694_);
        v___x_700_ = lean_nat_pow(v_a_699_, v_x_695_);
        crate::leanh::lean_dec(v_a_699_);
        v___x_701_ = lean_nat_to_int(v___x_700_);
        return v___x_701_;
    } else {
        let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: u8 = 0;
        v___x_702_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_703_ = lean_nat_mod(v_x_695_, v___x_702_);
        v___x_704_ = lean_nat_dec_eq(v___x_703_, v_natZero_696_);
        crate::leanh::lean_dec(v___x_703_);
        if v___x_704_ == 0 {
            let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_705_ = lean_nat_abs(v_x_694_);
            v___x_706_ = lean_nat_pow(v___x_705_, v_x_695_);
            crate::leanh::lean_dec(v___x_705_);
            v___x_707_ = lean_nat_to_int(v___x_706_);
            v___x_708_ = lean_int_neg(v___x_707_);
            crate::leanh::lean_dec(v___x_707_);
            return v___x_708_;
        } else {
            let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_709_ = lean_nat_abs(v_x_694_);
            v___x_710_ = lean_nat_pow(v___x_709_, v_x_695_);
            crate::leanh::lean_dec(v___x_709_);
            v___x_711_ = lean_nat_to_int(v___x_710_);
            return v___x_711_;
        }
    }
}
pub unsafe fn l_Int_pow___boxed(
    mut v_x_712_: *mut crate::leanh::LeanObject,
    mut v_x_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Int_pow(v_x_712_, v_x_713_);
    crate::leanh::lean_dec(v_x_713_);
    crate::leanh::lean_dec(v_x_712_);
    return v_res_714_;
}
pub unsafe fn l_Int_instMin___lam__0(
    mut v_x_717_: *mut crate::leanh::LeanObject,
    mut v_y_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_719_: u8 = 0;
    v___x_719_ = lean_int_dec_le(v_x_717_, v_y_718_);
    if v___x_719_ == 0 {
        crate::leanh::lean_inc(v_y_718_);
        return v_y_718_;
    } else {
        crate::leanh::lean_inc(v_x_717_);
        return v_x_717_;
    }
}
pub unsafe fn l_Int_instMin___lam__0___boxed(
    mut v_x_720_: *mut crate::leanh::LeanObject,
    mut v_y_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_722_ = l_Int_instMin___lam__0(v_x_720_, v_y_721_);
    crate::leanh::lean_dec(v_y_721_);
    crate::leanh::lean_dec(v_x_720_);
    return v_res_722_;
}
pub unsafe fn l_Int_instMax___lam__0(
    mut v_x_725_: *mut crate::leanh::LeanObject,
    mut v_y_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: u8 = 0;
    v___x_727_ = lean_int_dec_le(v_x_725_, v_y_726_);
    if v___x_727_ == 0 {
        crate::leanh::lean_inc(v_x_725_);
        return v_x_725_;
    } else {
        crate::leanh::lean_inc(v_y_726_);
        return v_y_726_;
    }
}
pub unsafe fn l_Int_instMax___lam__0___boxed(
    mut v_x_728_: *mut crate::leanh::LeanObject,
    mut v_y_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Int_instMax___lam__0(v_x_728_, v_y_729_);
    crate::leanh::lean_dec(v_y_729_);
    crate::leanh::lean_dec(v_x_728_);
    return v_res_730_;
}
pub unsafe fn l_instIntCastInt___lam__0(
    mut v_n_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_733_);
    return v_n_733_;
}
pub unsafe fn l_instIntCastInt___lam__0___boxed(
    mut v_n_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_735_ = l_instIntCastInt___lam__0(v_n_734_);
    crate::leanh::lean_dec(v_n_734_);
    return v_res_735_;
}
pub unsafe fn l_Int_cast___redArg(
    mut v_inst_738_: *mut crate::leanh::LeanObject,
    mut v_a_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = crate::leanh::lean_apply_1(v_inst_738_, v_a_739_);
    return v___x_740_;
}
pub unsafe fn l_Int_cast(
    mut v_R_741_: *mut crate::leanh::LeanObject,
    mut v_inst_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = crate::leanh::lean_apply_1(v_inst_742_, v_a_743_);
    return v___x_744_;
}
pub unsafe fn l_instCoeTailIntOfIntCast___redArg(
    mut v_inst_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = crate::leanh::lean_alloc_closure(l_Int_cast as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_746_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_746_, 1, v_inst_745_);
    return v___x_746_;
}
pub unsafe fn l_instCoeTailIntOfIntCast(
    mut v_R_747_: *mut crate::leanh::LeanObject,
    mut v_inst_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = crate::leanh::lean_alloc_closure(l_Int_cast as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_749_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_749_, 1, v_inst_748_);
    return v___x_749_;
}
pub unsafe fn l_instCoeHTCTIntOfIntCast___redArg(
    mut v_inst_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = crate::leanh::lean_alloc_closure(l_Int_cast as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_751_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_751_, 1, v_inst_750_);
    return v___x_751_;
}
pub unsafe fn l_instCoeHTCTIntOfIntCast(
    mut v_R_752_: *mut crate::leanh::LeanObject,
    mut v_inst_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = crate::leanh::lean_alloc_closure(l_Int_cast as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_754_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_754_, 1, v_inst_753_);
    return v___x_754_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Cast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Int_instInhabited = _init_l_Int_instInhabited();
    crate::leanh::lean_mark_persistent(l_Int_instInhabited);
    l_Int_instLEInt = _init_l_Int_instLEInt();
    crate::leanh::lean_mark_persistent(l_Int_instLEInt);
    l_Int_instLTInt = _init_l_Int_instLTInt();
    crate::leanh::lean_mark_persistent(l_Int_instLTInt);
    l_Int_instDvd = _init_l_Int_instDvd();
    crate::leanh::lean_mark_persistent(l_Int_instDvd);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Cast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_Basic(builtin);
}

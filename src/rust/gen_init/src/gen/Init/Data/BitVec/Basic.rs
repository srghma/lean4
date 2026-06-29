// Lean compiler output
// Module: Init.Data.BitVec.Basic
// Imports: Init.Data.Int.Bitwise.Basic Init.Data.Bool Init.Data.Int.DivMod.Basic Init.WF Init.Data.Nat.Bitwise.Lemmas Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.Meta.Defs Init.Omega Init.WFTactics
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_ediv, lean_int_emod,
    lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_land, lean_nat_lor, lean_nat_lxor, lean_nat_mod,
    lean_nat_mul, lean_nat_pow, lean_nat_shiftl, lean_nat_shiftr, lean_nat_sub, lean_nat_to_int,
    lean_string_append, lean_string_length, lean_string_mk, lean_uint64_mix_hash,
    lean_uint64_of_nat,
};
use crate::r#gen::Init::Data::BitVec::BasicAux::{l_BitVec_add, l_BitVec_sub};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, l_Bool_toNat, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Data::Int::Bitwise::Basic::{
    initialize_Init_Data_Int_Bitwise_Basic, l_Int_shiftRight,
    runtime_initialize_Init_Data_Int_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::List::Basic::l_List_replicateTR___redArg;
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{l_Nat_shiftRight___boxed, l_Nat_testBit};
use crate::r#gen::Init::Data::Nat::Bitwise::Lemmas::{
    initialize_Init_Data_Nat_Bitwise_Lemmas, runtime_initialize_Init_Data_Nat_Bitwise_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Nat_toDigits};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_BitVec_ofNat, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_List_lengthTR___redArg, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
static mut l_BitVec_nil___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_BitVec_nil___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_BitVec_nil: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_BitVec_instGetElemNatBoolLt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_BitVec_instGetElemNatBoolLt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_BitVec_instGetElemNatBoolLt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_instGetElemNatBoolLt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_BitVec_term_____x23_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 95, 95, 35, 95, 95, 0],
    };
static mut l_BitVec_term_____x23_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_BitVec_term_____x23_____00__closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_BitVec_term_____x23_____00__closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            16433175448540965390 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_BitVec_term_____x23_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__5_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_BitVec_term_____x23_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            6110315075117401315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__8_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_BitVec_term_____x23_____00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            1581446985683836252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__12_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_BitVec_term_____x23_____00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__13_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__16_value: crate::leanh::LeanStringObject<5> =
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
static mut l_BitVec_term_____x23_____00__closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__16_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__17_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_____00__closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_____00__closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_BitVec_term_____x23____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [66, 105, 116, 86, 101, 99, 46, 111, 102, 78, 97, 116, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value) as *mut crate::leanh::LeanObject,7578295756008745317 as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 95, 35, 39, 95, 95, 0],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_BitVec_term_____x23_x27_____00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_BitVec_term_____x23_x27_____00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            2277806277647888355 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [35, 39, 0],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec_term_____x23_x27_____00__closed__7_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_term_____x23_x27_____00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_BitVec_term_____x23_x27____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_term_____x23_x27_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [66, 105, 116, 86, 101, 99, 46, 111, 102, 78, 97, 116, 76, 84, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [111, 102, 78, 97, 116, 76, 84, 0]};
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value) as *mut crate::leanh::LeanObject,2059920148364733515 as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_BitVec_toHex___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_BitVec_repr___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [48, 120, 0],
    };
static mut l_BitVec_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_repr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_BitVec_repr___closed__0_value) as *mut crate::leanh::LeanObject
        ],
    };
static mut l_BitVec_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_repr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_BitVec_repr___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_BitVec_term_____x23_____00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_BitVec_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_repr___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_BitVec_ofBool___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_ofBool___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_BitVec_ofBool___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_ofBool___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_BitVec_instHShiftRight___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_BitVec_instHShiftRight___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_BitVec_instHShiftRight___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_BitVec_saddOverflow___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_saddOverflow___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_BitVec_instNatCast___lam__0(
    mut v_w_1422_: *mut crate::leanh::LeanObject,
    mut v_x_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_BitVec_ofNat(v_w_1422_, v_x_1423_);
    return v___x_1424_;
}
pub unsafe fn l_BitVec_instNatCast___lam__0___boxed(
    mut v_w_1425_: *mut crate::leanh::LeanObject,
    mut v_x_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_BitVec_instNatCast___lam__0(v_w_1425_, v_x_1426_);
    crate::leanh::lean_dec(v_x_1426_);
    crate::leanh::lean_dec(v_w_1425_);
    return v_res_1427_;
}
pub unsafe fn l_BitVec_instNatCast(
    mut v_w_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1429_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instNatCast___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1429_, 0, v_w_1428_);
    return v___f_1429_;
}
pub unsafe fn _init_l_BitVec_nil___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1431_ = l_BitVec_ofNat(v___x_1430_, v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn _init_l_BitVec_nil() -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_nil___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_nil___closed__0_once),
        _init_l_BitVec_nil___closed__0,
    );
    return v___x_1432_;
}
pub unsafe fn l_BitVec_zero(
    mut v_n_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1434_;
}
pub unsafe fn l_BitVec_zero___boxed(
    mut v_n_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_BitVec_zero(v_n_1435_);
    crate::leanh::lean_dec(v_n_1435_);
    return v_res_1436_;
}
pub unsafe fn l_BitVec_instInhabited(
    mut v_n_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1438_;
}
pub unsafe fn l_BitVec_instInhabited___boxed(
    mut v_n_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_BitVec_instInhabited(v_n_1439_);
    crate::leanh::lean_dec(v_n_1439_);
    return v_res_1440_;
}
pub unsafe fn l_BitVec_allOnes(
    mut v_n_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1443_ = lean_nat_pow(v___x_1442_, v_n_1441_);
    v___x_1444_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1445_ = lean_nat_sub(v___x_1443_, v___x_1444_);
    crate::leanh::lean_dec(v___x_1443_);
    return v___x_1445_;
}
pub unsafe fn l_BitVec_allOnes___boxed(
    mut v_n_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_BitVec_allOnes(v_n_1446_);
    crate::leanh::lean_dec(v_n_1446_);
    return v_res_1447_;
}
pub unsafe fn l_BitVec_getLsb___redArg(
    mut v_x_1448_: *mut crate::leanh::LeanObject,
    mut v_i_1449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1450_: u8 = 0;
    v___x_1450_ = l_Nat_testBit(v_x_1448_, v_i_1449_);
    return v___x_1450_;
}
pub unsafe fn l_BitVec_getLsb___redArg___boxed(
    mut v_x_1451_: *mut crate::leanh::LeanObject,
    mut v_i_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1453_: u8 = 0;
    let mut v_r_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_BitVec_getLsb___redArg(v_x_1451_, v_i_1452_);
    crate::leanh::lean_dec(v_i_1452_);
    crate::leanh::lean_dec(v_x_1451_);
    v_r_1454_ = crate::leanh::lean_box((v_res_1453_) as usize);
    return v_r_1454_;
}
pub unsafe fn l_BitVec_getLsb(
    mut v_w_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
    mut v_i_1457_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1458_: u8 = 0;
    v___x_1458_ = l_Nat_testBit(v_x_1456_, v_i_1457_);
    return v___x_1458_;
}
pub unsafe fn l_BitVec_getLsb___boxed(
    mut v_w_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_i_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1462_: u8 = 0;
    let mut v_r_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_BitVec_getLsb(v_w_1459_, v_x_1460_, v_i_1461_);
    crate::leanh::lean_dec(v_i_1461_);
    crate::leanh::lean_dec(v_x_1460_);
    crate::leanh::lean_dec(v_w_1459_);
    v_r_1463_ = crate::leanh::lean_box((v_res_1462_) as usize);
    return v_r_1463_;
}
pub unsafe fn l_BitVec_getLsb_x3f(
    mut v_w_1464_: *mut crate::leanh::LeanObject,
    mut v_x_1465_: *mut crate::leanh::LeanObject,
    mut v_i_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: u8 = 0;
    v___x_1467_ = lean_nat_dec_lt(v_i_1466_, v_w_1464_);
    if v___x_1467_ == 0 {
        let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1468_ = crate::leanh::lean_box(0);
        return v___x_1468_;
    } else {
        let mut v___x_1469_: u8 = 0;
        let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1469_ = l_Nat_testBit(v_x_1465_, v_i_1466_);
        v___x_1470_ = crate::leanh::lean_box((v___x_1469_) as usize);
        v___x_1471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
        return v___x_1471_;
    }
}
pub unsafe fn l_BitVec_getLsb_x3f___boxed(
    mut v_w_1472_: *mut crate::leanh::LeanObject,
    mut v_x_1473_: *mut crate::leanh::LeanObject,
    mut v_i_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l_BitVec_getLsb_x3f(v_w_1472_, v_x_1473_, v_i_1474_);
    crate::leanh::lean_dec(v_i_1474_);
    crate::leanh::lean_dec(v_x_1473_);
    crate::leanh::lean_dec(v_w_1472_);
    return v_res_1475_;
}
pub unsafe fn l_BitVec_getMsb(
    mut v_w_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
    mut v_i_1478_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    v___x_1479_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1480_ = lean_nat_sub(v_w_1476_, v___x_1479_);
    v___x_1481_ = lean_nat_sub(v___x_1480_, v_i_1478_);
    crate::leanh::lean_dec(v___x_1480_);
    v___x_1482_ = l_Nat_testBit(v_x_1477_, v___x_1481_);
    crate::leanh::lean_dec(v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn l_BitVec_getMsb___boxed(
    mut v_w_1483_: *mut crate::leanh::LeanObject,
    mut v_x_1484_: *mut crate::leanh::LeanObject,
    mut v_i_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1486_: u8 = 0;
    let mut v_r_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_BitVec_getMsb(v_w_1483_, v_x_1484_, v_i_1485_);
    crate::leanh::lean_dec(v_i_1485_);
    crate::leanh::lean_dec(v_x_1484_);
    crate::leanh::lean_dec(v_w_1483_);
    v_r_1487_ = crate::leanh::lean_box((v_res_1486_) as usize);
    return v_r_1487_;
}
pub unsafe fn l_BitVec_getMsb_x3f(
    mut v_w_1488_: *mut crate::leanh::LeanObject,
    mut v_x_1489_: *mut crate::leanh::LeanObject,
    mut v_i_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: u8 = 0;
    v___x_1491_ = lean_nat_dec_lt(v_i_1490_, v_w_1488_);
    if v___x_1491_ == 0 {
        let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1492_ = crate::leanh::lean_box(0);
        return v___x_1492_;
    } else {
        let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: u8 = 0;
        let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1493_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1494_ = lean_nat_sub(v_w_1488_, v___x_1493_);
        v___x_1495_ = lean_nat_sub(v___x_1494_, v_i_1490_);
        crate::leanh::lean_dec(v___x_1494_);
        v___x_1496_ = l_Nat_testBit(v_x_1489_, v___x_1495_);
        crate::leanh::lean_dec(v___x_1495_);
        v___x_1497_ = crate::leanh::lean_box((v___x_1496_) as usize);
        v___x_1498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1497_);
        return v___x_1498_;
    }
}
pub unsafe fn l_BitVec_getMsb_x3f___boxed(
    mut v_w_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
    mut v_i_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_BitVec_getMsb_x3f(v_w_1499_, v_x_1500_, v_i_1501_);
    crate::leanh::lean_dec(v_i_1501_);
    crate::leanh::lean_dec(v_x_1500_);
    crate::leanh::lean_dec(v_w_1499_);
    return v_res_1502_;
}
pub unsafe fn l_BitVec_getLsbD___redArg(
    mut v_x_1503_: *mut crate::leanh::LeanObject,
    mut v_i_1504_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1505_: u8 = 0;
    v___x_1505_ = l_Nat_testBit(v_x_1503_, v_i_1504_);
    return v___x_1505_;
}
pub unsafe fn l_BitVec_getLsbD___redArg___boxed(
    mut v_x_1506_: *mut crate::leanh::LeanObject,
    mut v_i_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: u8 = 0;
    let mut v_r_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_BitVec_getLsbD___redArg(v_x_1506_, v_i_1507_);
    crate::leanh::lean_dec(v_i_1507_);
    crate::leanh::lean_dec(v_x_1506_);
    v_r_1509_ = crate::leanh::lean_box((v_res_1508_) as usize);
    return v_r_1509_;
}
pub unsafe fn l_BitVec_getLsbD(
    mut v_w_1510_: *mut crate::leanh::LeanObject,
    mut v_x_1511_: *mut crate::leanh::LeanObject,
    mut v_i_1512_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1513_: u8 = 0;
    v___x_1513_ = l_Nat_testBit(v_x_1511_, v_i_1512_);
    return v___x_1513_;
}
pub unsafe fn l_BitVec_getLsbD___boxed(
    mut v_w_1514_: *mut crate::leanh::LeanObject,
    mut v_x_1515_: *mut crate::leanh::LeanObject,
    mut v_i_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1517_: u8 = 0;
    let mut v_r_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_BitVec_getLsbD(v_w_1514_, v_x_1515_, v_i_1516_);
    crate::leanh::lean_dec(v_i_1516_);
    crate::leanh::lean_dec(v_x_1515_);
    crate::leanh::lean_dec(v_w_1514_);
    v_r_1518_ = crate::leanh::lean_box((v_res_1517_) as usize);
    return v_r_1518_;
}
pub unsafe fn l_BitVec_getMsbD(
    mut v_w_1519_: *mut crate::leanh::LeanObject,
    mut v_x_1520_: *mut crate::leanh::LeanObject,
    mut v_i_1521_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1522_: u8 = 0;
    v___x_1522_ = lean_nat_dec_lt(v_i_1521_, v_w_1519_);
    if v___x_1522_ == 0 {
        return v___x_1522_;
    } else {
        let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1526_: u8 = 0;
        v___x_1523_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1524_ = lean_nat_sub(v_w_1519_, v___x_1523_);
        v___x_1525_ = lean_nat_sub(v___x_1524_, v_i_1521_);
        crate::leanh::lean_dec(v___x_1524_);
        v___x_1526_ = l_Nat_testBit(v_x_1520_, v___x_1525_);
        crate::leanh::lean_dec(v___x_1525_);
        return v___x_1526_;
    }
}
pub unsafe fn l_BitVec_getMsbD___boxed(
    mut v_w_1527_: *mut crate::leanh::LeanObject,
    mut v_x_1528_: *mut crate::leanh::LeanObject,
    mut v_i_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1530_: u8 = 0;
    let mut v_r_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_BitVec_getMsbD(v_w_1527_, v_x_1528_, v_i_1529_);
    crate::leanh::lean_dec(v_i_1529_);
    crate::leanh::lean_dec(v_x_1528_);
    crate::leanh::lean_dec(v_w_1527_);
    v_r_1531_ = crate::leanh::lean_box((v_res_1530_) as usize);
    return v_r_1531_;
}
pub unsafe fn l_BitVec_msb(
    mut v_n_1532_: *mut crate::leanh::LeanObject,
    mut v_x_1533_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    v___x_1534_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1535_ = lean_nat_dec_lt(v___x_1534_, v_n_1532_);
    if v___x_1535_ == 0 {
        return v___x_1535_;
    } else {
        let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: u8 = 0;
        v___x_1536_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1537_ = lean_nat_sub(v_n_1532_, v___x_1536_);
        v___x_1538_ = l_Nat_testBit(v_x_1533_, v___x_1537_);
        crate::leanh::lean_dec(v___x_1537_);
        return v___x_1538_;
    }
}
pub unsafe fn l_BitVec_msb___boxed(
    mut v_n_1539_: *mut crate::leanh::LeanObject,
    mut v_x_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: u8 = 0;
    let mut v_r_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_BitVec_msb(v_n_1539_, v_x_1540_);
    crate::leanh::lean_dec(v_x_1540_);
    crate::leanh::lean_dec(v_n_1539_);
    v_r_1542_ = crate::leanh::lean_box((v_res_1541_) as usize);
    return v_r_1542_;
}
pub unsafe fn l_BitVec_instGetElemNatBoolLt___lam__0(
    mut v_xs_1543_: *mut crate::leanh::LeanObject,
    mut v_i_1544_: *mut crate::leanh::LeanObject,
    mut v_h_1545_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1546_: u8 = 0;
    v___x_1546_ = l_Nat_testBit(v_xs_1543_, v_i_1544_);
    return v___x_1546_;
}
pub unsafe fn l_BitVec_instGetElemNatBoolLt___lam__0___boxed(
    mut v_xs_1547_: *mut crate::leanh::LeanObject,
    mut v_i_1548_: *mut crate::leanh::LeanObject,
    mut v_h_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: u8 = 0;
    let mut v_r_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_BitVec_instGetElemNatBoolLt___lam__0(v_xs_1547_, v_i_1548_, v_h_1549_);
    crate::leanh::lean_dec(v_i_1548_);
    crate::leanh::lean_dec(v_xs_1547_);
    v_r_1551_ = crate::leanh::lean_box((v_res_1550_) as usize);
    return v_r_1551_;
}
pub unsafe fn l_BitVec_instGetElemNatBoolLt(
    mut v_w_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1554_ = l_BitVec_instGetElemNatBoolLt___closed__0;
    return v___f_1554_;
}
pub unsafe fn l_BitVec_instGetElemNatBoolLt___boxed(
    mut v_w_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1556_ = l_BitVec_instGetElemNatBoolLt(v_w_1555_);
    crate::leanh::lean_dec(v_w_1555_);
    return v_res_1556_;
}
pub unsafe fn l_Nat_cast___at___00BitVec_toInt_spec__0(
    mut v_a_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = lean_nat_to_int(v_a_1557_);
    return v___x_1558_;
}
pub unsafe fn l_BitVec_toInt(
    mut v_n_1559_: *mut crate::leanh::LeanObject,
    mut v_x_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    v___x_1561_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1562_ = lean_nat_mul(v___x_1561_, v_x_1560_);
    v___x_1563_ = lean_nat_pow(v___x_1561_, v_n_1559_);
    v___x_1564_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
    crate::leanh::lean_dec(v___x_1562_);
    if v___x_1564_ == 0 {
        let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1565_ = lean_nat_to_int(v_x_1560_);
        v___x_1566_ = lean_nat_to_int(v___x_1563_);
        v___x_1567_ = lean_int_sub(v___x_1565_, v___x_1566_);
        crate::leanh::lean_dec(v___x_1566_);
        crate::leanh::lean_dec(v___x_1565_);
        return v___x_1567_;
    } else {
        let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1563_);
        v___x_1568_ = lean_nat_to_int(v_x_1560_);
        return v___x_1568_;
    }
}
pub unsafe fn l_BitVec_toInt___boxed(
    mut v_n_1569_: *mut crate::leanh::LeanObject,
    mut v_x_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_BitVec_toInt(v_n_1569_, v_x_1570_);
    crate::leanh::lean_dec(v_n_1569_);
    return v_res_1571_;
}
pub unsafe fn l_BitVec_ofInt(
    mut v_n_1572_: *mut crate::leanh::LeanObject,
    mut v_i_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1574_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1575_ = lean_nat_pow(v___x_1574_, v_n_1572_);
    v___x_1576_ = lean_nat_to_int(v___x_1575_);
    v___x_1577_ = lean_int_emod(v_i_1573_, v___x_1576_);
    crate::leanh::lean_dec(v___x_1576_);
    v___x_1578_ = l_Int_toNat(v___x_1577_);
    crate::leanh::lean_dec(v___x_1577_);
    return v___x_1578_;
}
pub unsafe fn l_BitVec_ofInt___boxed(
    mut v_n_1579_: *mut crate::leanh::LeanObject,
    mut v_i_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_BitVec_ofInt(v_n_1579_, v_i_1580_);
    crate::leanh::lean_dec(v_i_1580_);
    crate::leanh::lean_dec(v_n_1579_);
    return v_res_1581_;
}
pub unsafe fn l_BitVec_instIntCast(
    mut v_w_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ =
        crate::leanh::lean_alloc_closure(l_BitVec_ofInt___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_1583_, 0, v_w_1582_);
    return v___x_1583_;
}
pub unsafe fn _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
    v___x_1643_ = l_String_toRawSubstring_x27(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(
    mut v_x_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    v___x_1660_ = l_BitVec_term_____x23_____00__closed__2;
    crate::leanh::lean_inc(v_x_1657_);
    v___x_1661_ = l_Lean_Syntax_isOfKind(v_x_1657_, v___x_1660_);
    if v___x_1661_ == 0 {
        let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1657_);
        v___x_1662_ = crate::leanh::lean_box(1);
        v___x_1663_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1662_);
        crate::leanh::lean_ctor_set(v___x_1663_, 1, v_a_1659_);
        return v___x_1663_;
    } else {
        let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: u8 = 0;
        v___x_1664_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1665_ = l_Lean_Syntax_getArg(v_x_1657_, v___x_1664_);
        v___x_1666_ = l_BitVec_term_____x23_____00__closed__6;
        crate::leanh::lean_inc(v___x_1665_);
        v___x_1667_ = l_Lean_Syntax_isOfKind(v___x_1665_, v___x_1666_);
        if v___x_1667_ == 0 {
            let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1665_);
            crate::leanh::lean_dec(v_x_1657_);
            v___x_1668_ = crate::leanh::lean_box(1);
            v___x_1669_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
            crate::leanh::lean_ctor_set(v___x_1669_, 1, v_a_1659_);
            return v___x_1669_;
        } else {
            let mut v_quotContext_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1675_: u8 = 0;
            let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_1670_ = crate::leanh::lean_ctor_get(v_a_1658_, 1);
            v_currMacroScope_1671_ = crate::leanh::lean_ctor_get(v_a_1658_, 2);
            v_ref_1672_ = crate::leanh::lean_ctor_get(v_a_1658_, 5);
            v___x_1673_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_1674_ = l_Lean_Syntax_getArg(v_x_1657_, v___x_1673_);
            crate::leanh::lean_dec(v_x_1657_);
            v___x_1675_ = 0;
            v___x_1676_ = l_Lean_SourceInfo_fromRef(v_ref_1672_, v___x_1675_);
            v___x_1677_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
            v___x_1678_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6), core::ptr::addr_of_mut!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once), _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
            v___x_1679_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8;
            crate::leanh::lean_inc(v_currMacroScope_1671_);
            crate::leanh::lean_inc(v_quotContext_1670_);
            v___x_1680_ =
                l_Lean_addMacroScope(v_quotContext_1670_, v___x_1679_, v_currMacroScope_1671_);
            v___x_1681_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10;
            crate::leanh::lean_inc_n(v___x_1676_, 2);
            v___x_1682_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1676_);
            crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1678_);
            crate::leanh::lean_ctor_set(v___x_1682_, 2, v___x_1680_);
            crate::leanh::lean_ctor_set(v___x_1682_, 3, v___x_1681_);
            v___x_1683_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12;
            v___x_1684_ = l_Lean_Syntax_node2(v___x_1676_, v___x_1683_, v___x_1674_, v___x_1665_);
            v___x_1685_ = l_Lean_Syntax_node2(v___x_1676_, v___x_1677_, v___x_1682_, v___x_1684_);
            v___x_1686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1686_, 0, v___x_1685_);
            crate::leanh::lean_ctor_set(v___x_1686_, 1, v_a_1659_);
            return v___x_1686_;
        }
    }
}
pub unsafe fn l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___boxed(
    mut v_x_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ =
        l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(
            v_x_1687_, v_a_1688_, v_a_1689_,
        );
    crate::leanh::lean_dec_ref(v_a_1688_);
    return v_res_1690_;
}
pub unsafe fn l_BitVec_unexpandBitVecOfNat(
    mut v_x_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    v___x_1694_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
    crate::leanh::lean_inc(v_x_1691_);
    v___x_1695_ = l_Lean_Syntax_isOfKind(v_x_1691_, v___x_1694_);
    if v___x_1695_ == 0 {
        let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1691_);
        v___x_1696_ = crate::leanh::lean_box(0);
        v___x_1697_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
        crate::leanh::lean_ctor_set(v___x_1697_, 1, v_a_1693_);
        return v___x_1697_;
    } else {
        let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: u8 = 0;
        v___x_1698_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1699_ = l_Lean_Syntax_getArg(v_x_1691_, v___x_1698_);
        crate::leanh::lean_dec(v_x_1691_);
        v___x_1700_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_1699_);
        v___x_1701_ = l_Lean_Syntax_matchesNull(v___x_1699_, v___x_1700_);
        if v___x_1701_ == 0 {
            let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1699_);
            v___x_1702_ = crate::leanh::lean_box(0);
            v___x_1703_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1703_, 0, v___x_1702_);
            crate::leanh::lean_ctor_set(v___x_1703_, 1, v_a_1693_);
            return v___x_1703_;
        } else {
            let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1706_: u8 = 0;
            v___x_1704_ = l_Lean_Syntax_getArg(v___x_1699_, v___x_1698_);
            v___x_1705_ = l_BitVec_term_____x23_____00__closed__6;
            crate::leanh::lean_inc(v___x_1704_);
            v___x_1706_ = l_Lean_Syntax_isOfKind(v___x_1704_, v___x_1705_);
            if v___x_1706_ == 0 {
                let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1704_);
                crate::leanh::lean_dec(v___x_1699_);
                v___x_1707_ = crate::leanh::lean_box(0);
                v___x_1708_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
                crate::leanh::lean_ctor_set(v___x_1708_, 1, v_a_1693_);
                return v___x_1708_;
            } else {
                let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1711_: u8 = 0;
                let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1709_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1710_ = l_Lean_Syntax_getArg(v___x_1699_, v___x_1709_);
                crate::leanh::lean_dec(v___x_1699_);
                v___x_1711_ = 0;
                v___x_1712_ = l_Lean_SourceInfo_fromRef(v_a_1692_, v___x_1711_);
                v___x_1713_ = l_BitVec_term_____x23_____00__closed__2;
                v___x_1714_ = l_BitVec_term_____x23_____00__closed__12;
                crate::leanh::lean_inc(v___x_1712_);
                v___x_1715_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1715_, 0, v___x_1712_);
                crate::leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                v___x_1716_ = l_Lean_Syntax_node3(
                    v___x_1712_,
                    v___x_1713_,
                    v___x_1704_,
                    v___x_1715_,
                    v___x_1710_,
                );
                v___x_1717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                crate::leanh::lean_ctor_set(v___x_1717_, 1, v_a_1693_);
                return v___x_1717_;
            }
        }
    }
}
pub unsafe fn l_BitVec_unexpandBitVecOfNat___boxed(
    mut v_x_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
    mut v_a_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_BitVec_unexpandBitVecOfNat(v_x_1718_, v_a_1719_, v_a_1720_);
    crate::leanh::lean_dec(v_a_1719_);
    return v_res_1721_;
}
pub unsafe fn _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0;
    v___x_1748_ = l_String_toRawSubstring_x27(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(
    mut v_x_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    v___x_1762_ = l_BitVec_term_____x23_x27_____00__closed__1;
    crate::leanh::lean_inc(v_x_1759_);
    v___x_1763_ = l_Lean_Syntax_isOfKind(v_x_1759_, v___x_1762_);
    if v___x_1763_ == 0 {
        let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1759_);
        v___x_1764_ = crate::leanh::lean_box(1);
        v___x_1765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
        crate::leanh::lean_ctor_set(v___x_1765_, 1, v_a_1761_);
        return v___x_1765_;
    } else {
        let mut v_quotContext_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: u8 = 0;
        let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1766_ = crate::leanh::lean_ctor_get(v_a_1760_, 1);
        v_currMacroScope_1767_ = crate::leanh::lean_ctor_get(v_a_1760_, 2);
        v_ref_1768_ = crate::leanh::lean_ctor_get(v_a_1760_, 5);
        v___x_1769_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1770_ = l_Lean_Syntax_getArg(v_x_1759_, v___x_1769_);
        v___x_1771_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1772_ = l_Lean_Syntax_getArg(v_x_1759_, v___x_1771_);
        crate::leanh::lean_dec(v_x_1759_);
        v___x_1773_ = 0;
        v___x_1774_ = l_Lean_SourceInfo_fromRef(v_ref_1768_, v___x_1773_);
        v___x_1775_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
        v___x_1776_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1), core::ptr::addr_of_mut!(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once), _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
        v___x_1777_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_1767_);
        crate::leanh::lean_inc(v_quotContext_1766_);
        v___x_1778_ =
            l_Lean_addMacroScope(v_quotContext_1766_, v___x_1777_, v_currMacroScope_1767_);
        v___x_1779_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5;
        crate::leanh::lean_inc_n(v___x_1774_, 2);
        v___x_1780_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1774_);
        crate::leanh::lean_ctor_set(v___x_1780_, 1, v___x_1776_);
        crate::leanh::lean_ctor_set(v___x_1780_, 2, v___x_1778_);
        crate::leanh::lean_ctor_set(v___x_1780_, 3, v___x_1779_);
        v___x_1781_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12;
        v___x_1782_ = l_Lean_Syntax_node2(v___x_1774_, v___x_1781_, v___x_1770_, v___x_1772_);
        v___x_1783_ = l_Lean_Syntax_node2(v___x_1774_, v___x_1775_, v___x_1780_, v___x_1782_);
        v___x_1784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1783_);
        crate::leanh::lean_ctor_set(v___x_1784_, 1, v_a_1761_);
        return v___x_1784_;
    }
}
pub unsafe fn l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___boxed(
    mut v_x_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ =
        l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(
            v_x_1785_, v_a_1786_, v_a_1787_,
        );
    crate::leanh::lean_dec_ref(v_a_1786_);
    return v_res_1788_;
}
pub unsafe fn l_BitVec_unexpandBitVecOfNatLt(
    mut v_x_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    v___x_1792_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
    crate::leanh::lean_inc(v_x_1789_);
    v___x_1793_ = l_Lean_Syntax_isOfKind(v_x_1789_, v___x_1792_);
    if v___x_1793_ == 0 {
        let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1789_);
        v___x_1794_ = crate::leanh::lean_box(0);
        v___x_1795_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1794_);
        crate::leanh::lean_ctor_set(v___x_1795_, 1, v_a_1791_);
        return v___x_1795_;
    } else {
        let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: u8 = 0;
        v___x_1796_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1797_ = l_Lean_Syntax_getArg(v_x_1789_, v___x_1796_);
        crate::leanh::lean_dec(v_x_1789_);
        v___x_1798_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_1797_);
        v___x_1799_ = l_Lean_Syntax_matchesNull(v___x_1797_, v___x_1798_);
        if v___x_1799_ == 0 {
            let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1797_);
            v___x_1800_ = crate::leanh::lean_box(0);
            v___x_1801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
            crate::leanh::lean_ctor_set(v___x_1801_, 1, v_a_1791_);
            return v___x_1801_;
        } else {
            let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: u8 = 0;
            let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1802_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1803_ = l_Lean_Syntax_getArg(v___x_1797_, v___x_1802_);
            v___x_1804_ = l_Lean_Syntax_getArg(v___x_1797_, v___x_1796_);
            crate::leanh::lean_dec(v___x_1797_);
            v___x_1805_ = 0;
            v___x_1806_ = l_Lean_SourceInfo_fromRef(v_a_1790_, v___x_1805_);
            v___x_1807_ = l_BitVec_term_____x23_x27_____00__closed__1;
            v___x_1808_ = l_BitVec_term_____x23_x27_____00__closed__2;
            crate::leanh::lean_inc(v___x_1806_);
            v___x_1809_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1806_);
            crate::leanh::lean_ctor_set(v___x_1809_, 1, v___x_1808_);
            v___x_1810_ = l_Lean_Syntax_node3(
                v___x_1806_,
                v___x_1807_,
                v___x_1803_,
                v___x_1809_,
                v___x_1804_,
            );
            v___x_1811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
            crate::leanh::lean_ctor_set(v___x_1811_, 1, v_a_1791_);
            return v___x_1811_;
        }
    }
}
pub unsafe fn l_BitVec_unexpandBitVecOfNatLt___boxed(
    mut v_x_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1815_ = l_BitVec_unexpandBitVecOfNatLt(v_x_1812_, v_a_1813_, v_a_1814_);
    crate::leanh::lean_dec(v_a_1813_);
    return v_res_1815_;
}
pub unsafe fn _init_l_BitVec_toHex___boxed__const__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: u32 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = 48;
    v___x_1817_ = crate::leanh::lean_box_uint32(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l_BitVec_toHex(
    mut v_n_1818_: *mut crate::leanh::LeanObject,
    mut v_x_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1821_ = l_Nat_toDigits(v___x_1820_, v_x_1819_);
    v_s_1822_ = lean_string_mk(v___x_1821_);
    v___x_1823_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1824_ = lean_nat_add(v_n_1818_, v___x_1823_);
    v___x_1825_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1826_ = lean_nat_shiftr(v___x_1824_, v___x_1825_);
    crate::leanh::lean_dec(v___x_1824_);
    v___x_1827_ = lean_string_length(v_s_1822_);
    v___x_1828_ = lean_nat_sub(v___x_1826_, v___x_1827_);
    crate::leanh::lean_dec(v___x_1827_);
    crate::leanh::lean_dec(v___x_1826_);
    v___x_1829_ = l_BitVec_toHex___boxed__const__1;
    v___x_1830_ = l_List_replicateTR___redArg(v___x_1828_, v___x_1829_);
    v_t_1831_ = lean_string_mk(v___x_1830_);
    v___x_1832_ = lean_string_append(v_t_1831_, v_s_1822_);
    crate::leanh::lean_dec_ref(v_s_1822_);
    return v___x_1832_;
}
pub unsafe fn l_BitVec_toHex___boxed(
    mut v_n_1833_: *mut crate::leanh::LeanObject,
    mut v_x_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_BitVec_toHex(v_n_1833_, v_x_1834_);
    crate::leanh::lean_dec(v_n_1833_);
    return v_res_1835_;
}
pub unsafe fn l_BitVec_repr(
    mut v_n_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_BitVec_repr___closed__1;
    v___x_1844_ = l_BitVec_toHex(v_n_1841_, v_a_1842_);
    v___x_1845_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1845_, 0, v___x_1844_);
    v___x_1846_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1846_, 0, v___x_1843_);
    crate::leanh::lean_ctor_set(v___x_1846_, 1, v___x_1845_);
    v___x_1847_ = l_BitVec_repr___closed__2;
    v___x_1848_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1846_);
    crate::leanh::lean_ctor_set(v___x_1848_, 1, v___x_1847_);
    v___x_1849_ = l_Nat_reprFast(v_n_1841_);
    v___x_1850_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1850_, 0, v___x_1849_);
    v___x_1851_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1851_, 0, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
    return v___x_1851_;
}
pub unsafe fn l_BitVec_instRepr___lam__0(
    mut v_n_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_x_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_BitVec_repr(v_n_1852_, v_a_1853_);
    return v___x_1855_;
}
pub unsafe fn l_BitVec_instRepr___lam__0___boxed(
    mut v_n_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_BitVec_instRepr___lam__0(v_n_1856_, v_a_1857_, v_x_1858_);
    crate::leanh::lean_dec(v_x_1858_);
    return v_res_1859_;
}
pub unsafe fn l_BitVec_instRepr(
    mut v_n_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1861_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instRepr___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1861_, 0, v_n_1860_);
    return v___f_1861_;
}
pub unsafe fn l_BitVec_instToString___lam__0(
    mut v_n_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = l_BitVec_repr(v_n_1862_, v_a_1863_);
    v___x_1865_ = l_Std_Format_defWidth;
    v___x_1866_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1867_ = l_Std_Format_pretty(v___x_1864_, v___x_1865_, v___x_1866_, v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_BitVec_instToString(
    mut v_n_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1869_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instToString___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1869_, 0, v_n_1868_);
    return v___f_1869_;
}
pub unsafe fn l_BitVec_neg(
    mut v_n_1870_: *mut crate::leanh::LeanObject,
    mut v_x_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1873_ = lean_nat_pow(v___x_1872_, v_n_1870_);
    v___x_1874_ = lean_nat_sub(v___x_1873_, v_x_1871_);
    crate::leanh::lean_dec(v___x_1873_);
    v___x_1875_ = l_BitVec_ofNat(v_n_1870_, v___x_1874_);
    crate::leanh::lean_dec(v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_BitVec_neg___boxed(
    mut v_n_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_BitVec_neg(v_n_1876_, v_x_1877_);
    crate::leanh::lean_dec(v_x_1877_);
    crate::leanh::lean_dec(v_n_1876_);
    return v_res_1878_;
}
pub unsafe fn l_BitVec_instNeg(
    mut v_n_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ =
        crate::leanh::lean_alloc_closure(l_BitVec_neg___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_1880_, 0, v_n_1879_);
    return v___x_1880_;
}
pub unsafe fn l_BitVec_abs(
    mut v_n_1881_: *mut crate::leanh::LeanObject,
    mut v_x_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1884_: u8 = 0;
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1886_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1887_ = lean_nat_dec_lt(v___x_1886_, v_n_1881_);
                if v___x_1887_ == 0 {
                    v___y_1884_ = v___x_1887_;
                    state = 1;
                    continue;
                } else {
                    v___x_1888_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1889_ = lean_nat_sub(v_n_1881_, v___x_1888_);
                    v___x_1890_ = l_Nat_testBit(v_x_1882_, v___x_1889_);
                    crate::leanh::lean_dec(v___x_1889_);
                    v___y_1884_ = v___x_1890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1884_ == 0 {
                    crate::leanh::lean_inc(v_x_1882_);
                    return v_x_1882_;
                } else {
                    v___x_1885_ = l_BitVec_neg(v_n_1881_, v_x_1882_);
                    return v___x_1885_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_abs___boxed(
    mut v_n_1891_: *mut crate::leanh::LeanObject,
    mut v_x_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_BitVec_abs(v_n_1891_, v_x_1892_);
    crate::leanh::lean_dec(v_x_1892_);
    crate::leanh::lean_dec(v_n_1891_);
    return v_res_1893_;
}
pub unsafe fn l_BitVec_mul(
    mut v_n_1894_: *mut crate::leanh::LeanObject,
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_y_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = lean_nat_mul(v_x_1895_, v_y_1896_);
    v___x_1898_ = l_BitVec_ofNat(v_n_1894_, v___x_1897_);
    crate::leanh::lean_dec(v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_BitVec_mul___boxed(
    mut v_n_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
    mut v_y_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_BitVec_mul(v_n_1899_, v_x_1900_, v_y_1901_);
    crate::leanh::lean_dec(v_y_1901_);
    crate::leanh::lean_dec(v_x_1900_);
    crate::leanh::lean_dec(v_n_1899_);
    return v_res_1902_;
}
pub unsafe fn l_BitVec_instMul(
    mut v_n_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ =
        crate::leanh::lean_alloc_closure(l_BitVec_mul___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_1904_, 0, v_n_1903_);
    return v___x_1904_;
}
pub unsafe fn l_BitVec_pow(
    mut v_n_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v_y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1909_: u8 = 0;
    v_zero_1908_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1909_ = lean_nat_dec_eq(v_y_1907_, v_zero_1908_);
    if v_isZero_1909_ == 1 {
        let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1910_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1911_ = l_BitVec_ofNat(v_n_1905_, v___x_1910_);
        return v___x_1911_;
    } else {
        let mut v_one_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_1912_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1913_ = lean_nat_sub(v_y_1907_, v_one_1912_);
        v___x_1914_ = l_BitVec_pow(v_n_1905_, v_x_1906_, v_n_1913_);
        crate::leanh::lean_dec(v_n_1913_);
        v___x_1915_ = l_BitVec_mul(v_n_1905_, v___x_1914_, v_x_1906_);
        crate::leanh::lean_dec(v___x_1914_);
        return v___x_1915_;
    }
}
pub unsafe fn l_BitVec_pow___boxed(
    mut v_n_1916_: *mut crate::leanh::LeanObject,
    mut v_x_1917_: *mut crate::leanh::LeanObject,
    mut v_y_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_BitVec_pow(v_n_1916_, v_x_1917_, v_y_1918_);
    crate::leanh::lean_dec(v_y_1918_);
    crate::leanh::lean_dec(v_x_1917_);
    crate::leanh::lean_dec(v_n_1916_);
    return v_res_1919_;
}
pub unsafe fn l_BitVec_instPowNat___lam__0(
    mut v_n_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v_y_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_BitVec_pow(v_n_1920_, v_x_1921_, v_y_1922_);
    return v___x_1923_;
}
pub unsafe fn l_BitVec_instPowNat___lam__0___boxed(
    mut v_n_1924_: *mut crate::leanh::LeanObject,
    mut v_x_1925_: *mut crate::leanh::LeanObject,
    mut v_y_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_BitVec_instPowNat___lam__0(v_n_1924_, v_x_1925_, v_y_1926_);
    crate::leanh::lean_dec(v_y_1926_);
    crate::leanh::lean_dec(v_x_1925_);
    crate::leanh::lean_dec(v_n_1924_);
    return v_res_1927_;
}
pub unsafe fn l_BitVec_instPowNat(
    mut v_n_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1929_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instPowNat___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1929_, 0, v_n_1928_);
    return v___f_1929_;
}
pub unsafe fn l_BitVec_udiv___redArg(
    mut v_x_1930_: *mut crate::leanh::LeanObject,
    mut v_y_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_nat_div(v_x_1930_, v_y_1931_);
    return v___x_1932_;
}
pub unsafe fn l_BitVec_udiv___redArg___boxed(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
    mut v_y_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_BitVec_udiv___redArg(v_x_1933_, v_y_1934_);
    crate::leanh::lean_dec(v_y_1934_);
    crate::leanh::lean_dec(v_x_1933_);
    return v_res_1935_;
}
pub unsafe fn l_BitVec_udiv(
    mut v_n_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
    mut v_y_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = lean_nat_div(v_x_1937_, v_y_1938_);
    return v___x_1939_;
}
pub unsafe fn l_BitVec_udiv___boxed(
    mut v_n_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
    mut v_y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_BitVec_udiv(v_n_1940_, v_x_1941_, v_y_1942_);
    crate::leanh::lean_dec(v_y_1942_);
    crate::leanh::lean_dec(v_x_1941_);
    crate::leanh::lean_dec(v_n_1940_);
    return v_res_1943_;
}
pub unsafe fn l_BitVec_instDiv(
    mut v_n_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ =
        crate::leanh::lean_alloc_closure(l_BitVec_udiv___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_1945_, 0, v_n_1944_);
    return v___x_1945_;
}
pub unsafe fn l_BitVec_umod___redArg(
    mut v_x_1946_: *mut crate::leanh::LeanObject,
    mut v_y_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_nat_mod(v_x_1946_, v_y_1947_);
    return v___x_1948_;
}
pub unsafe fn l_BitVec_umod___redArg___boxed(
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_y_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_BitVec_umod___redArg(v_x_1949_, v_y_1950_);
    crate::leanh::lean_dec(v_y_1950_);
    crate::leanh::lean_dec(v_x_1949_);
    return v_res_1951_;
}
pub unsafe fn l_BitVec_umod(
    mut v_n_1952_: *mut crate::leanh::LeanObject,
    mut v_x_1953_: *mut crate::leanh::LeanObject,
    mut v_y_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = lean_nat_mod(v_x_1953_, v_y_1954_);
    return v___x_1955_;
}
pub unsafe fn l_BitVec_umod___boxed(
    mut v_n_1956_: *mut crate::leanh::LeanObject,
    mut v_x_1957_: *mut crate::leanh::LeanObject,
    mut v_y_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_BitVec_umod(v_n_1956_, v_x_1957_, v_y_1958_);
    crate::leanh::lean_dec(v_y_1958_);
    crate::leanh::lean_dec(v_x_1957_);
    crate::leanh::lean_dec(v_n_1956_);
    return v_res_1959_;
}
pub unsafe fn l_BitVec_instMod(
    mut v_n_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ =
        crate::leanh::lean_alloc_closure(l_BitVec_umod___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_1961_, 0, v_n_1960_);
    return v___x_1961_;
}
pub unsafe fn l_BitVec_smtUDiv(
    mut v_n_1962_: *mut crate::leanh::LeanObject,
    mut v_x_1963_: *mut crate::leanh::LeanObject,
    mut v_y_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    v___x_1965_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1966_ = l_BitVec_ofNat(v_n_1962_, v___x_1965_);
    v___x_1967_ = lean_nat_dec_eq(v_y_1964_, v___x_1966_);
    crate::leanh::lean_dec(v___x_1966_);
    if v___x_1967_ == 0 {
        let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1968_ = lean_nat_div(v_x_1963_, v_y_1964_);
        return v___x_1968_;
    } else {
        let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1969_ = l_BitVec_allOnes(v_n_1962_);
        return v___x_1969_;
    }
}
pub unsafe fn l_BitVec_smtUDiv___boxed(
    mut v_n_1970_: *mut crate::leanh::LeanObject,
    mut v_x_1971_: *mut crate::leanh::LeanObject,
    mut v_y_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_BitVec_smtUDiv(v_n_1970_, v_x_1971_, v_y_1972_);
    crate::leanh::lean_dec(v_y_1972_);
    crate::leanh::lean_dec(v_x_1971_);
    crate::leanh::lean_dec(v_n_1970_);
    return v_res_1973_;
}
pub unsafe fn l_BitVec_sdiv(
    mut v_n_1974_: *mut crate::leanh::LeanObject,
    mut v_x_1975_: *mut crate::leanh::LeanObject,
    mut v_y_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1978_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1992_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: u8 = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2003_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2004_ = lean_nat_dec_lt(v___x_2003_, v_n_1974_);
                if v___x_2004_ == 0 {
                    v___y_1992_ = v___x_2004_;
                    state = 3;
                    continue;
                } else {
                    v___x_2005_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2006_ = lean_nat_sub(v_n_1974_, v___x_2005_);
                    v___x_2007_ = l_Nat_testBit(v_x_1975_, v___x_2006_);
                    crate::leanh::lean_dec(v___x_2006_);
                    v___y_1992_ = v___x_2007_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_1978_ == 0 {
                    v___x_1979_ = lean_nat_div(v_x_1975_, v_y_1976_);
                    return v___x_1979_;
                } else {
                    v___x_1980_ = l_BitVec_neg(v_n_1974_, v_y_1976_);
                    v___x_1981_ = lean_nat_div(v_x_1975_, v___x_1980_);
                    crate::leanh::lean_dec(v___x_1980_);
                    v___x_1982_ = l_BitVec_neg(v_n_1974_, v___x_1981_);
                    crate::leanh::lean_dec(v___x_1981_);
                    return v___x_1982_;
                }
            }
            2 => {
                if v___y_1984_ == 0 {
                    v___x_1985_ = l_BitVec_neg(v_n_1974_, v_x_1975_);
                    v___x_1986_ = lean_nat_div(v___x_1985_, v_y_1976_);
                    crate::leanh::lean_dec(v___x_1985_);
                    v___x_1987_ = l_BitVec_neg(v_n_1974_, v___x_1986_);
                    crate::leanh::lean_dec(v___x_1986_);
                    return v___x_1987_;
                } else {
                    v___x_1988_ = l_BitVec_neg(v_n_1974_, v_x_1975_);
                    v___x_1989_ = l_BitVec_neg(v_n_1974_, v_y_1976_);
                    v___x_1990_ = lean_nat_div(v___x_1988_, v___x_1989_);
                    crate::leanh::lean_dec(v___x_1989_);
                    crate::leanh::lean_dec(v___x_1988_);
                    return v___x_1990_;
                }
            }
            3 => {
                if v___y_1992_ == 0 {
                    v___x_1993_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1994_ = lean_nat_dec_lt(v___x_1993_, v_n_1974_);
                    if v___x_1994_ == 0 {
                        v___y_1978_ = v___x_1994_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1995_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1996_ = lean_nat_sub(v_n_1974_, v___x_1995_);
                        v___x_1997_ = l_Nat_testBit(v_y_1976_, v___x_1996_);
                        crate::leanh::lean_dec(v___x_1996_);
                        v___y_1978_ = v___x_1997_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1998_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1999_ = lean_nat_dec_lt(v___x_1998_, v_n_1974_);
                    if v___x_1999_ == 0 {
                        v___y_1984_ = v___x_1999_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2000_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2001_ = lean_nat_sub(v_n_1974_, v___x_2000_);
                        v___x_2002_ = l_Nat_testBit(v_y_1976_, v___x_2001_);
                        crate::leanh::lean_dec(v___x_2001_);
                        v___y_1984_ = v___x_2002_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_sdiv___boxed(
    mut v_n_2008_: *mut crate::leanh::LeanObject,
    mut v_x_2009_: *mut crate::leanh::LeanObject,
    mut v_y_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_BitVec_sdiv(v_n_2008_, v_x_2009_, v_y_2010_);
    crate::leanh::lean_dec(v_y_2010_);
    crate::leanh::lean_dec(v_x_2009_);
    crate::leanh::lean_dec(v_n_2008_);
    return v_res_2011_;
}
pub unsafe fn l_BitVec_smtSDiv(
    mut v_n_2012_: *mut crate::leanh::LeanObject,
    mut v_x_2013_: *mut crate::leanh::LeanObject,
    mut v_y_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2022_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2041_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2042_ = lean_nat_dec_lt(v___x_2041_, v_n_2012_);
                if v___x_2042_ == 0 {
                    v___y_2030_ = v___x_2042_;
                    state = 3;
                    continue;
                } else {
                    v___x_2043_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2044_ = lean_nat_sub(v_n_2012_, v___x_2043_);
                    v___x_2045_ = l_Nat_testBit(v_x_2013_, v___x_2044_);
                    crate::leanh::lean_dec(v___x_2044_);
                    v___y_2030_ = v___x_2045_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_2016_ == 0 {
                    v___x_2017_ = l_BitVec_smtUDiv(v_n_2012_, v_x_2013_, v_y_2014_);
                    return v___x_2017_;
                } else {
                    v___x_2018_ = l_BitVec_neg(v_n_2012_, v_y_2014_);
                    v___x_2019_ = l_BitVec_smtUDiv(v_n_2012_, v_x_2013_, v___x_2018_);
                    crate::leanh::lean_dec(v___x_2018_);
                    v___x_2020_ = l_BitVec_neg(v_n_2012_, v___x_2019_);
                    crate::leanh::lean_dec(v___x_2019_);
                    return v___x_2020_;
                }
            }
            2 => {
                if v___y_2022_ == 0 {
                    v___x_2023_ = l_BitVec_neg(v_n_2012_, v_x_2013_);
                    v___x_2024_ = l_BitVec_smtUDiv(v_n_2012_, v___x_2023_, v_y_2014_);
                    crate::leanh::lean_dec(v___x_2023_);
                    v___x_2025_ = l_BitVec_neg(v_n_2012_, v___x_2024_);
                    crate::leanh::lean_dec(v___x_2024_);
                    return v___x_2025_;
                } else {
                    v___x_2026_ = l_BitVec_neg(v_n_2012_, v_x_2013_);
                    v___x_2027_ = l_BitVec_neg(v_n_2012_, v_y_2014_);
                    v___x_2028_ = l_BitVec_smtUDiv(v_n_2012_, v___x_2026_, v___x_2027_);
                    crate::leanh::lean_dec(v___x_2027_);
                    crate::leanh::lean_dec(v___x_2026_);
                    return v___x_2028_;
                }
            }
            3 => {
                if v___y_2030_ == 0 {
                    v___x_2031_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2032_ = lean_nat_dec_lt(v___x_2031_, v_n_2012_);
                    if v___x_2032_ == 0 {
                        v___y_2016_ = v___x_2032_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2033_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2034_ = lean_nat_sub(v_n_2012_, v___x_2033_);
                        v___x_2035_ = l_Nat_testBit(v_y_2014_, v___x_2034_);
                        crate::leanh::lean_dec(v___x_2034_);
                        v___y_2016_ = v___x_2035_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2036_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2037_ = lean_nat_dec_lt(v___x_2036_, v_n_2012_);
                    if v___x_2037_ == 0 {
                        v___y_2022_ = v___x_2037_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2038_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2039_ = lean_nat_sub(v_n_2012_, v___x_2038_);
                        v___x_2040_ = l_Nat_testBit(v_y_2014_, v___x_2039_);
                        crate::leanh::lean_dec(v___x_2039_);
                        v___y_2022_ = v___x_2040_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_smtSDiv___boxed(
    mut v_n_2046_: *mut crate::leanh::LeanObject,
    mut v_x_2047_: *mut crate::leanh::LeanObject,
    mut v_y_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2049_ = l_BitVec_smtSDiv(v_n_2046_, v_x_2047_, v_y_2048_);
    crate::leanh::lean_dec(v_y_2048_);
    crate::leanh::lean_dec(v_x_2047_);
    crate::leanh::lean_dec(v_n_2046_);
    return v_res_2049_;
}
pub unsafe fn l_BitVec_srem(
    mut v_n_2050_: *mut crate::leanh::LeanObject,
    mut v_x_2051_: *mut crate::leanh::LeanObject,
    mut v_y_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2079_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2080_ = lean_nat_dec_lt(v___x_2079_, v_n_2050_);
                if v___x_2080_ == 0 {
                    v___y_2068_ = v___x_2080_;
                    state = 3;
                    continue;
                } else {
                    v___x_2081_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2082_ = lean_nat_sub(v_n_2050_, v___x_2081_);
                    v___x_2083_ = l_Nat_testBit(v_x_2051_, v___x_2082_);
                    crate::leanh::lean_dec(v___x_2082_);
                    v___y_2068_ = v___x_2083_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_2054_ == 0 {
                    v___x_2055_ = lean_nat_mod(v_x_2051_, v_y_2052_);
                    return v___x_2055_;
                } else {
                    v___x_2056_ = l_BitVec_neg(v_n_2050_, v_y_2052_);
                    v___x_2057_ = lean_nat_mod(v_x_2051_, v___x_2056_);
                    crate::leanh::lean_dec(v___x_2056_);
                    return v___x_2057_;
                }
            }
            2 => {
                if v___y_2059_ == 0 {
                    v___x_2060_ = l_BitVec_neg(v_n_2050_, v_x_2051_);
                    v___x_2061_ = lean_nat_mod(v___x_2060_, v_y_2052_);
                    crate::leanh::lean_dec(v___x_2060_);
                    v___x_2062_ = l_BitVec_neg(v_n_2050_, v___x_2061_);
                    crate::leanh::lean_dec(v___x_2061_);
                    return v___x_2062_;
                } else {
                    v___x_2063_ = l_BitVec_neg(v_n_2050_, v_x_2051_);
                    v___x_2064_ = l_BitVec_neg(v_n_2050_, v_y_2052_);
                    v___x_2065_ = lean_nat_mod(v___x_2063_, v___x_2064_);
                    crate::leanh::lean_dec(v___x_2064_);
                    crate::leanh::lean_dec(v___x_2063_);
                    v___x_2066_ = l_BitVec_neg(v_n_2050_, v___x_2065_);
                    crate::leanh::lean_dec(v___x_2065_);
                    return v___x_2066_;
                }
            }
            3 => {
                if v___y_2068_ == 0 {
                    v___x_2069_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2070_ = lean_nat_dec_lt(v___x_2069_, v_n_2050_);
                    if v___x_2070_ == 0 {
                        v___y_2054_ = v___x_2070_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2071_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2072_ = lean_nat_sub(v_n_2050_, v___x_2071_);
                        v___x_2073_ = l_Nat_testBit(v_y_2052_, v___x_2072_);
                        crate::leanh::lean_dec(v___x_2072_);
                        v___y_2054_ = v___x_2073_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2074_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2075_ = lean_nat_dec_lt(v___x_2074_, v_n_2050_);
                    if v___x_2075_ == 0 {
                        v___y_2059_ = v___x_2075_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2076_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2077_ = lean_nat_sub(v_n_2050_, v___x_2076_);
                        v___x_2078_ = l_Nat_testBit(v_y_2052_, v___x_2077_);
                        crate::leanh::lean_dec(v___x_2077_);
                        v___y_2059_ = v___x_2078_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_srem___boxed(
    mut v_n_2084_: *mut crate::leanh::LeanObject,
    mut v_x_2085_: *mut crate::leanh::LeanObject,
    mut v_y_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l_BitVec_srem(v_n_2084_, v_x_2085_, v_y_2086_);
    crate::leanh::lean_dec(v_y_2086_);
    crate::leanh::lean_dec(v_x_2085_);
    crate::leanh::lean_dec(v_n_2084_);
    return v_res_2087_;
}
pub unsafe fn l_BitVec_smod(
    mut v_m_2088_: *mut crate::leanh::LeanObject,
    mut v_x_2089_: *mut crate::leanh::LeanObject,
    mut v_y_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: u8 = 0;
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2122_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2123_ = lean_nat_dec_lt(v___x_2122_, v_m_2088_);
                if v___x_2123_ == 0 {
                    v___y_2111_ = v___x_2123_;
                    state = 3;
                    continue;
                } else {
                    v___x_2124_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2125_ = lean_nat_sub(v_m_2088_, v___x_2124_);
                    v___x_2126_ = l_Nat_testBit(v_x_2089_, v___x_2125_);
                    crate::leanh::lean_dec(v___x_2125_);
                    v___y_2111_ = v___x_2126_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_2092_ == 0 {
                    v___x_2093_ = lean_nat_mod(v_x_2089_, v_y_2090_);
                    return v___x_2093_;
                } else {
                    v___x_2094_ = l_BitVec_neg(v_m_2088_, v_y_2090_);
                    v_u_2095_ = lean_nat_mod(v_x_2089_, v___x_2094_);
                    crate::leanh::lean_dec(v___x_2094_);
                    v___x_2096_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2097_ = lean_nat_dec_eq(v_u_2095_, v___x_2096_);
                    if v___x_2097_ == 0 {
                        v___x_2098_ = l_BitVec_add(v_m_2088_, v_u_2095_, v_y_2090_);
                        crate::leanh::lean_dec(v_u_2095_);
                        return v___x_2098_;
                    } else {
                        return v_u_2095_;
                    }
                }
            }
            2 => {
                if v___y_2100_ == 0 {
                    v___x_2101_ = l_BitVec_neg(v_m_2088_, v_x_2089_);
                    v_u_2102_ = lean_nat_mod(v___x_2101_, v_y_2090_);
                    crate::leanh::lean_dec(v___x_2101_);
                    v___x_2103_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2104_ = lean_nat_dec_eq(v_u_2102_, v___x_2103_);
                    if v___x_2104_ == 0 {
                        v___x_2105_ = l_BitVec_sub(v_m_2088_, v_y_2090_, v_u_2102_);
                        crate::leanh::lean_dec(v_u_2102_);
                        return v___x_2105_;
                    } else {
                        return v_u_2102_;
                    }
                } else {
                    v___x_2106_ = l_BitVec_neg(v_m_2088_, v_x_2089_);
                    v___x_2107_ = l_BitVec_neg(v_m_2088_, v_y_2090_);
                    v___x_2108_ = lean_nat_mod(v___x_2106_, v___x_2107_);
                    crate::leanh::lean_dec(v___x_2107_);
                    crate::leanh::lean_dec(v___x_2106_);
                    v___x_2109_ = l_BitVec_neg(v_m_2088_, v___x_2108_);
                    crate::leanh::lean_dec(v___x_2108_);
                    return v___x_2109_;
                }
            }
            3 => {
                if v___y_2111_ == 0 {
                    v___x_2112_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2113_ = lean_nat_dec_lt(v___x_2112_, v_m_2088_);
                    if v___x_2113_ == 0 {
                        v___y_2092_ = v___x_2113_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2114_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2115_ = lean_nat_sub(v_m_2088_, v___x_2114_);
                        v___x_2116_ = l_Nat_testBit(v_y_2090_, v___x_2115_);
                        crate::leanh::lean_dec(v___x_2115_);
                        v___y_2092_ = v___x_2116_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2117_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2118_ = lean_nat_dec_lt(v___x_2117_, v_m_2088_);
                    if v___x_2118_ == 0 {
                        v___y_2100_ = v___x_2118_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2119_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2120_ = lean_nat_sub(v_m_2088_, v___x_2119_);
                        v___x_2121_ = l_Nat_testBit(v_y_2090_, v___x_2120_);
                        crate::leanh::lean_dec(v___x_2120_);
                        v___y_2100_ = v___x_2121_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_smod___boxed(
    mut v_m_2127_: *mut crate::leanh::LeanObject,
    mut v_x_2128_: *mut crate::leanh::LeanObject,
    mut v_y_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2130_ = l_BitVec_smod(v_m_2127_, v_x_2128_, v_y_2129_);
    crate::leanh::lean_dec(v_y_2129_);
    crate::leanh::lean_dec(v_x_2128_);
    crate::leanh::lean_dec(v_m_2127_);
    return v_res_2130_;
}
pub unsafe fn _init_l_BitVec_ofBool___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2133_ = l_BitVec_ofNat(v___x_2132_, v___x_2131_);
    return v___x_2133_;
}
pub unsafe fn _init_l_BitVec_ofBool___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2135_ = l_BitVec_ofNat(v___x_2134_, v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn l_BitVec_ofBool(mut v_b_2136_: u8) -> *mut crate::leanh::LeanObject {
    if v_b_2136_ == 0 {
        let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2137_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_ofBool___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_ofBool___closed__0_once),
            _init_l_BitVec_ofBool___closed__0,
        );
        return v___x_2137_;
    } else {
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2138_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_ofBool___closed__1),
            core::ptr::addr_of_mut!(l_BitVec_ofBool___closed__1_once),
            _init_l_BitVec_ofBool___closed__1,
        );
        return v___x_2138_;
    }
}
pub unsafe fn l_BitVec_ofBool___boxed(
    mut v_b_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2140_ = (crate::leanh::lean_unbox(v_b_2139_) as u8);
    v_res_2141_ = l_BitVec_ofBool(v_b_boxed_2140_);
    return v_res_2141_;
}
pub unsafe fn l_BitVec_fill(
    mut v_w_2142_: *mut crate::leanh::LeanObject,
    mut v_b_2143_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_b_2143_ == 0 {
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2144_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2145_ = l_BitVec_ofNat(v_w_2142_, v___x_2144_);
        return v___x_2145_;
    } else {
        let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2146_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2147_ = l_BitVec_ofNat(v_w_2142_, v___x_2146_);
        v___x_2148_ = l_BitVec_neg(v_w_2142_, v___x_2147_);
        crate::leanh::lean_dec(v___x_2147_);
        return v___x_2148_;
    }
}
pub unsafe fn l_BitVec_fill___boxed(
    mut v_w_2149_: *mut crate::leanh::LeanObject,
    mut v_b_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2151_: u8 = 0;
    let mut v_res_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2151_ = (crate::leanh::lean_unbox(v_b_2150_) as u8);
    v_res_2152_ = l_BitVec_fill(v_w_2149_, v_b_boxed_2151_);
    crate::leanh::lean_dec(v_w_2149_);
    return v_res_2152_;
}
pub unsafe fn l_BitVec_ult___redArg(
    mut v_x_2153_: *mut crate::leanh::LeanObject,
    mut v_y_2154_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2155_: u8 = 0;
    v___x_2155_ = lean_nat_dec_lt(v_x_2153_, v_y_2154_);
    return v___x_2155_;
}
pub unsafe fn l_BitVec_ult___redArg___boxed(
    mut v_x_2156_: *mut crate::leanh::LeanObject,
    mut v_y_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: u8 = 0;
    let mut v_r_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_BitVec_ult___redArg(v_x_2156_, v_y_2157_);
    crate::leanh::lean_dec(v_y_2157_);
    crate::leanh::lean_dec(v_x_2156_);
    v_r_2159_ = crate::leanh::lean_box((v_res_2158_) as usize);
    return v_r_2159_;
}
pub unsafe fn l_BitVec_ult(
    mut v_n_2160_: *mut crate::leanh::LeanObject,
    mut v_x_2161_: *mut crate::leanh::LeanObject,
    mut v_y_2162_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2163_: u8 = 0;
    v___x_2163_ = lean_nat_dec_lt(v_x_2161_, v_y_2162_);
    return v___x_2163_;
}
pub unsafe fn l_BitVec_ult___boxed(
    mut v_n_2164_: *mut crate::leanh::LeanObject,
    mut v_x_2165_: *mut crate::leanh::LeanObject,
    mut v_y_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: u8 = 0;
    let mut v_r_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_BitVec_ult(v_n_2164_, v_x_2165_, v_y_2166_);
    crate::leanh::lean_dec(v_y_2166_);
    crate::leanh::lean_dec(v_x_2165_);
    crate::leanh::lean_dec(v_n_2164_);
    v_r_2168_ = crate::leanh::lean_box((v_res_2167_) as usize);
    return v_r_2168_;
}
pub unsafe fn l_BitVec_ule___redArg(
    mut v_x_2169_: *mut crate::leanh::LeanObject,
    mut v_y_2170_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2171_: u8 = 0;
    v___x_2171_ = lean_nat_dec_le(v_x_2169_, v_y_2170_);
    return v___x_2171_;
}
pub unsafe fn l_BitVec_ule___redArg___boxed(
    mut v_x_2172_: *mut crate::leanh::LeanObject,
    mut v_y_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: u8 = 0;
    let mut v_r_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_BitVec_ule___redArg(v_x_2172_, v_y_2173_);
    crate::leanh::lean_dec(v_y_2173_);
    crate::leanh::lean_dec(v_x_2172_);
    v_r_2175_ = crate::leanh::lean_box((v_res_2174_) as usize);
    return v_r_2175_;
}
pub unsafe fn l_BitVec_ule(
    mut v_n_2176_: *mut crate::leanh::LeanObject,
    mut v_x_2177_: *mut crate::leanh::LeanObject,
    mut v_y_2178_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2179_: u8 = 0;
    v___x_2179_ = lean_nat_dec_le(v_x_2177_, v_y_2178_);
    return v___x_2179_;
}
pub unsafe fn l_BitVec_ule___boxed(
    mut v_n_2180_: *mut crate::leanh::LeanObject,
    mut v_x_2181_: *mut crate::leanh::LeanObject,
    mut v_y_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2183_: u8 = 0;
    let mut v_r_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2183_ = l_BitVec_ule(v_n_2180_, v_x_2181_, v_y_2182_);
    crate::leanh::lean_dec(v_y_2182_);
    crate::leanh::lean_dec(v_x_2181_);
    crate::leanh::lean_dec(v_n_2180_);
    v_r_2184_ = crate::leanh::lean_box((v_res_2183_) as usize);
    return v_r_2184_;
}
pub unsafe fn l_BitVec_slt(
    mut v_n_2185_: *mut crate::leanh::LeanObject,
    mut v_x_2186_: *mut crate::leanh::LeanObject,
    mut v_y_2187_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    v___x_2188_ = l_BitVec_toInt(v_n_2185_, v_x_2186_);
    v___x_2189_ = l_BitVec_toInt(v_n_2185_, v_y_2187_);
    v___x_2190_ = lean_int_dec_lt(v___x_2188_, v___x_2189_);
    crate::leanh::lean_dec(v___x_2189_);
    crate::leanh::lean_dec(v___x_2188_);
    return v___x_2190_;
}
pub unsafe fn l_BitVec_slt___boxed(
    mut v_n_2191_: *mut crate::leanh::LeanObject,
    mut v_x_2192_: *mut crate::leanh::LeanObject,
    mut v_y_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2194_: u8 = 0;
    let mut v_r_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_BitVec_slt(v_n_2191_, v_x_2192_, v_y_2193_);
    crate::leanh::lean_dec(v_n_2191_);
    v_r_2195_ = crate::leanh::lean_box((v_res_2194_) as usize);
    return v_r_2195_;
}
pub unsafe fn l_BitVec_sle(
    mut v_n_2196_: *mut crate::leanh::LeanObject,
    mut v_x_2197_: *mut crate::leanh::LeanObject,
    mut v_y_2198_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u8 = 0;
    v___x_2199_ = l_BitVec_toInt(v_n_2196_, v_x_2197_);
    v___x_2200_ = l_BitVec_toInt(v_n_2196_, v_y_2198_);
    v___x_2201_ = lean_int_dec_le(v___x_2199_, v___x_2200_);
    crate::leanh::lean_dec(v___x_2200_);
    crate::leanh::lean_dec(v___x_2199_);
    return v___x_2201_;
}
pub unsafe fn l_BitVec_sle___boxed(
    mut v_n_2202_: *mut crate::leanh::LeanObject,
    mut v_x_2203_: *mut crate::leanh::LeanObject,
    mut v_y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2205_: u8 = 0;
    let mut v_r_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_BitVec_sle(v_n_2202_, v_x_2203_, v_y_2204_);
    crate::leanh::lean_dec(v_n_2202_);
    v_r_2206_ = crate::leanh::lean_box((v_res_2205_) as usize);
    return v_r_2206_;
}
pub unsafe fn l_BitVec_cast___redArg(
    mut v_x_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2207_);
    return v_x_2207_;
}
pub unsafe fn l_BitVec_cast___redArg___boxed(
    mut v_x_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2209_ = l_BitVec_cast___redArg(v_x_2208_);
    crate::leanh::lean_dec(v_x_2208_);
    return v_res_2209_;
}
pub unsafe fn l_BitVec_cast(
    mut v_n_2210_: *mut crate::leanh::LeanObject,
    mut v_m_2211_: *mut crate::leanh::LeanObject,
    mut v_eq_2212_: *mut crate::leanh::LeanObject,
    mut v_x_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2213_);
    return v_x_2213_;
}
pub unsafe fn l_BitVec_cast___boxed(
    mut v_n_2214_: *mut crate::leanh::LeanObject,
    mut v_m_2215_: *mut crate::leanh::LeanObject,
    mut v_eq_2216_: *mut crate::leanh::LeanObject,
    mut v_x_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_BitVec_cast(v_n_2214_, v_m_2215_, v_eq_2216_, v_x_2217_);
    crate::leanh::lean_dec(v_x_2217_);
    crate::leanh::lean_dec(v_m_2215_);
    crate::leanh::lean_dec(v_n_2214_);
    return v_res_2218_;
}
pub unsafe fn l_BitVec_extractLsb_x27___redArg(
    mut v_start_2219_: *mut crate::leanh::LeanObject,
    mut v_len_2220_: *mut crate::leanh::LeanObject,
    mut v_x_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = lean_nat_shiftr(v_x_2221_, v_start_2219_);
    v___x_2223_ = l_BitVec_ofNat(v_len_2220_, v___x_2222_);
    crate::leanh::lean_dec(v___x_2222_);
    return v___x_2223_;
}
pub unsafe fn l_BitVec_extractLsb_x27___redArg___boxed(
    mut v_start_2224_: *mut crate::leanh::LeanObject,
    mut v_len_2225_: *mut crate::leanh::LeanObject,
    mut v_x_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ = l_BitVec_extractLsb_x27___redArg(v_start_2224_, v_len_2225_, v_x_2226_);
    crate::leanh::lean_dec(v_x_2226_);
    crate::leanh::lean_dec(v_len_2225_);
    crate::leanh::lean_dec(v_start_2224_);
    return v_res_2227_;
}
pub unsafe fn l_BitVec_extractLsb_x27(
    mut v_n_2228_: *mut crate::leanh::LeanObject,
    mut v_start_2229_: *mut crate::leanh::LeanObject,
    mut v_len_2230_: *mut crate::leanh::LeanObject,
    mut v_x_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2232_ = l_BitVec_extractLsb_x27___redArg(v_start_2229_, v_len_2230_, v_x_2231_);
    return v___x_2232_;
}
pub unsafe fn l_BitVec_extractLsb_x27___boxed(
    mut v_n_2233_: *mut crate::leanh::LeanObject,
    mut v_start_2234_: *mut crate::leanh::LeanObject,
    mut v_len_2235_: *mut crate::leanh::LeanObject,
    mut v_x_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2237_ = l_BitVec_extractLsb_x27(v_n_2233_, v_start_2234_, v_len_2235_, v_x_2236_);
    crate::leanh::lean_dec(v_x_2236_);
    crate::leanh::lean_dec(v_len_2235_);
    crate::leanh::lean_dec(v_start_2234_);
    crate::leanh::lean_dec(v_n_2233_);
    return v_res_2237_;
}
pub unsafe fn l_BitVec_extractLsb___redArg(
    mut v_hi_2238_: *mut crate::leanh::LeanObject,
    mut v_lo_2239_: *mut crate::leanh::LeanObject,
    mut v_x_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = lean_nat_sub(v_hi_2238_, v_lo_2239_);
    v___x_2242_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2243_ = lean_nat_add(v___x_2241_, v___x_2242_);
    crate::leanh::lean_dec(v___x_2241_);
    v___x_2244_ = l_BitVec_extractLsb_x27___redArg(v_lo_2239_, v___x_2243_, v_x_2240_);
    crate::leanh::lean_dec(v___x_2243_);
    return v___x_2244_;
}
pub unsafe fn l_BitVec_extractLsb___redArg___boxed(
    mut v_hi_2245_: *mut crate::leanh::LeanObject,
    mut v_lo_2246_: *mut crate::leanh::LeanObject,
    mut v_x_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2248_ = l_BitVec_extractLsb___redArg(v_hi_2245_, v_lo_2246_, v_x_2247_);
    crate::leanh::lean_dec(v_x_2247_);
    crate::leanh::lean_dec(v_lo_2246_);
    crate::leanh::lean_dec(v_hi_2245_);
    return v_res_2248_;
}
pub unsafe fn l_BitVec_extractLsb(
    mut v_n_2249_: *mut crate::leanh::LeanObject,
    mut v_hi_2250_: *mut crate::leanh::LeanObject,
    mut v_lo_2251_: *mut crate::leanh::LeanObject,
    mut v_x_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2253_ = l_BitVec_extractLsb___redArg(v_hi_2250_, v_lo_2251_, v_x_2252_);
    return v___x_2253_;
}
pub unsafe fn l_BitVec_extractLsb___boxed(
    mut v_n_2254_: *mut crate::leanh::LeanObject,
    mut v_hi_2255_: *mut crate::leanh::LeanObject,
    mut v_lo_2256_: *mut crate::leanh::LeanObject,
    mut v_x_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_BitVec_extractLsb(v_n_2254_, v_hi_2255_, v_lo_2256_, v_x_2257_);
    crate::leanh::lean_dec(v_x_2257_);
    crate::leanh::lean_dec(v_lo_2256_);
    crate::leanh::lean_dec(v_hi_2255_);
    crate::leanh::lean_dec(v_n_2254_);
    return v_res_2258_;
}
pub unsafe fn l_BitVec_setWidth_x27___redArg(
    mut v_x_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2259_);
    return v_x_2259_;
}
pub unsafe fn l_BitVec_setWidth_x27___redArg___boxed(
    mut v_x_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_BitVec_setWidth_x27___redArg(v_x_2260_);
    crate::leanh::lean_dec(v_x_2260_);
    return v_res_2261_;
}
pub unsafe fn l_BitVec_setWidth_x27(
    mut v_n_2262_: *mut crate::leanh::LeanObject,
    mut v_w_2263_: *mut crate::leanh::LeanObject,
    mut v_le_2264_: *mut crate::leanh::LeanObject,
    mut v_x_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2265_);
    return v_x_2265_;
}
pub unsafe fn l_BitVec_setWidth_x27___boxed(
    mut v_n_2266_: *mut crate::leanh::LeanObject,
    mut v_w_2267_: *mut crate::leanh::LeanObject,
    mut v_le_2268_: *mut crate::leanh::LeanObject,
    mut v_x_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_BitVec_setWidth_x27(v_n_2266_, v_w_2267_, v_le_2268_, v_x_2269_);
    crate::leanh::lean_dec(v_x_2269_);
    crate::leanh::lean_dec(v_w_2267_);
    crate::leanh::lean_dec(v_n_2266_);
    return v_res_2270_;
}
pub unsafe fn l_BitVec_shiftLeftZeroExtend___redArg(
    mut v_msbs_2271_: *mut crate::leanh::LeanObject,
    mut v_m_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = lean_nat_shiftl(v_msbs_2271_, v_m_2272_);
    return v___x_2273_;
}
pub unsafe fn l_BitVec_shiftLeftZeroExtend___redArg___boxed(
    mut v_msbs_2274_: *mut crate::leanh::LeanObject,
    mut v_m_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_2274_, v_m_2275_);
    crate::leanh::lean_dec(v_m_2275_);
    crate::leanh::lean_dec(v_msbs_2274_);
    return v_res_2276_;
}
pub unsafe fn l_BitVec_shiftLeftZeroExtend(
    mut v_w_2277_: *mut crate::leanh::LeanObject,
    mut v_msbs_2278_: *mut crate::leanh::LeanObject,
    mut v_m_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = lean_nat_shiftl(v_msbs_2278_, v_m_2279_);
    return v___x_2280_;
}
pub unsafe fn l_BitVec_shiftLeftZeroExtend___boxed(
    mut v_w_2281_: *mut crate::leanh::LeanObject,
    mut v_msbs_2282_: *mut crate::leanh::LeanObject,
    mut v_m_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_BitVec_shiftLeftZeroExtend(v_w_2281_, v_msbs_2282_, v_m_2283_);
    crate::leanh::lean_dec(v_m_2283_);
    crate::leanh::lean_dec(v_msbs_2282_);
    crate::leanh::lean_dec(v_w_2281_);
    return v_res_2284_;
}
pub unsafe fn l_BitVec_setWidth(
    mut v_w_2285_: *mut crate::leanh::LeanObject,
    mut v_v_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2288_: u8 = 0;
    v___x_2288_ = lean_nat_dec_le(v_w_2285_, v_v_2286_);
    if v___x_2288_ == 0 {
        let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2289_ = l_BitVec_ofNat(v_v_2286_, v_x_2287_);
        return v___x_2289_;
    } else {
        crate::leanh::lean_inc(v_x_2287_);
        return v_x_2287_;
    }
}
pub unsafe fn l_BitVec_setWidth___boxed(
    mut v_w_2290_: *mut crate::leanh::LeanObject,
    mut v_v_2291_: *mut crate::leanh::LeanObject,
    mut v_x_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2293_ = l_BitVec_setWidth(v_w_2290_, v_v_2291_, v_x_2292_);
    crate::leanh::lean_dec(v_x_2292_);
    crate::leanh::lean_dec(v_v_2291_);
    crate::leanh::lean_dec(v_w_2290_);
    return v_res_2293_;
}
pub unsafe fn l_BitVec_zeroExtend(
    mut v_w_2294_: *mut crate::leanh::LeanObject,
    mut v_v_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2297_ = l_BitVec_setWidth(v_w_2294_, v_v_2295_, v_x_2296_);
    return v___x_2297_;
}
pub unsafe fn l_BitVec_zeroExtend___boxed(
    mut v_w_2298_: *mut crate::leanh::LeanObject,
    mut v_v_2299_: *mut crate::leanh::LeanObject,
    mut v_x_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_BitVec_zeroExtend(v_w_2298_, v_v_2299_, v_x_2300_);
    crate::leanh::lean_dec(v_x_2300_);
    crate::leanh::lean_dec(v_v_2299_);
    crate::leanh::lean_dec(v_w_2298_);
    return v_res_2301_;
}
pub unsafe fn l_BitVec_truncate(
    mut v_w_2302_: *mut crate::leanh::LeanObject,
    mut v_v_2303_: *mut crate::leanh::LeanObject,
    mut v_x_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_BitVec_setWidth(v_w_2302_, v_v_2303_, v_x_2304_);
    return v___x_2305_;
}
pub unsafe fn l_BitVec_truncate___boxed(
    mut v_w_2306_: *mut crate::leanh::LeanObject,
    mut v_v_2307_: *mut crate::leanh::LeanObject,
    mut v_x_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_BitVec_truncate(v_w_2306_, v_v_2307_, v_x_2308_);
    crate::leanh::lean_dec(v_x_2308_);
    crate::leanh::lean_dec(v_v_2307_);
    crate::leanh::lean_dec(v_w_2306_);
    return v_res_2309_;
}
pub unsafe fn l_BitVec_signExtend(
    mut v_w_2310_: *mut crate::leanh::LeanObject,
    mut v_v_2311_: *mut crate::leanh::LeanObject,
    mut v_x_2312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = l_BitVec_toInt(v_w_2310_, v_x_2312_);
    v___x_2314_ = l_BitVec_ofInt(v_v_2311_, v___x_2313_);
    crate::leanh::lean_dec(v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn l_BitVec_signExtend___boxed(
    mut v_w_2315_: *mut crate::leanh::LeanObject,
    mut v_v_2316_: *mut crate::leanh::LeanObject,
    mut v_x_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_BitVec_signExtend(v_w_2315_, v_v_2316_, v_x_2317_);
    crate::leanh::lean_dec(v_v_2316_);
    crate::leanh::lean_dec(v_w_2315_);
    return v_res_2318_;
}
pub unsafe fn l_BitVec_and___redArg(
    mut v_x_2319_: *mut crate::leanh::LeanObject,
    mut v_y_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = lean_nat_land(v_x_2319_, v_y_2320_);
    return v___x_2321_;
}
pub unsafe fn l_BitVec_and___redArg___boxed(
    mut v_x_2322_: *mut crate::leanh::LeanObject,
    mut v_y_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2324_ = l_BitVec_and___redArg(v_x_2322_, v_y_2323_);
    crate::leanh::lean_dec(v_y_2323_);
    crate::leanh::lean_dec(v_x_2322_);
    return v_res_2324_;
}
pub unsafe fn l_BitVec_and(
    mut v_n_2325_: *mut crate::leanh::LeanObject,
    mut v_x_2326_: *mut crate::leanh::LeanObject,
    mut v_y_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2328_ = lean_nat_land(v_x_2326_, v_y_2327_);
    return v___x_2328_;
}
pub unsafe fn l_BitVec_and___boxed(
    mut v_n_2329_: *mut crate::leanh::LeanObject,
    mut v_x_2330_: *mut crate::leanh::LeanObject,
    mut v_y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l_BitVec_and(v_n_2329_, v_x_2330_, v_y_2331_);
    crate::leanh::lean_dec(v_y_2331_);
    crate::leanh::lean_dec(v_x_2330_);
    crate::leanh::lean_dec(v_n_2329_);
    return v_res_2332_;
}
pub unsafe fn l_BitVec_instAndOp(
    mut v_w_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ =
        crate::leanh::lean_alloc_closure(l_BitVec_and___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_2334_, 0, v_w_2333_);
    return v___x_2334_;
}
pub unsafe fn l_BitVec_or___redArg(
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_y_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = lean_nat_lor(v_x_2335_, v_y_2336_);
    return v___x_2337_;
}
pub unsafe fn l_BitVec_or___redArg___boxed(
    mut v_x_2338_: *mut crate::leanh::LeanObject,
    mut v_y_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2340_ = l_BitVec_or___redArg(v_x_2338_, v_y_2339_);
    crate::leanh::lean_dec(v_y_2339_);
    crate::leanh::lean_dec(v_x_2338_);
    return v_res_2340_;
}
pub unsafe fn l_BitVec_or(
    mut v_n_2341_: *mut crate::leanh::LeanObject,
    mut v_x_2342_: *mut crate::leanh::LeanObject,
    mut v_y_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = lean_nat_lor(v_x_2342_, v_y_2343_);
    return v___x_2344_;
}
pub unsafe fn l_BitVec_or___boxed(
    mut v_n_2345_: *mut crate::leanh::LeanObject,
    mut v_x_2346_: *mut crate::leanh::LeanObject,
    mut v_y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_BitVec_or(v_n_2345_, v_x_2346_, v_y_2347_);
    crate::leanh::lean_dec(v_y_2347_);
    crate::leanh::lean_dec(v_x_2346_);
    crate::leanh::lean_dec(v_n_2345_);
    return v_res_2348_;
}
pub unsafe fn l_BitVec_instOrOp(
    mut v_w_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ =
        crate::leanh::lean_alloc_closure(l_BitVec_or___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_2350_, 0, v_w_2349_);
    return v___x_2350_;
}
pub unsafe fn l_BitVec_xor___redArg(
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_y_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = lean_nat_lxor(v_x_2351_, v_y_2352_);
    return v___x_2353_;
}
pub unsafe fn l_BitVec_xor___redArg___boxed(
    mut v_x_2354_: *mut crate::leanh::LeanObject,
    mut v_y_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_BitVec_xor___redArg(v_x_2354_, v_y_2355_);
    crate::leanh::lean_dec(v_y_2355_);
    crate::leanh::lean_dec(v_x_2354_);
    return v_res_2356_;
}
pub unsafe fn l_BitVec_xor(
    mut v_n_2357_: *mut crate::leanh::LeanObject,
    mut v_x_2358_: *mut crate::leanh::LeanObject,
    mut v_y_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = lean_nat_lxor(v_x_2358_, v_y_2359_);
    return v___x_2360_;
}
pub unsafe fn l_BitVec_xor___boxed(
    mut v_n_2361_: *mut crate::leanh::LeanObject,
    mut v_x_2362_: *mut crate::leanh::LeanObject,
    mut v_y_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_BitVec_xor(v_n_2361_, v_x_2362_, v_y_2363_);
    crate::leanh::lean_dec(v_y_2363_);
    crate::leanh::lean_dec(v_x_2362_);
    crate::leanh::lean_dec(v_n_2361_);
    return v_res_2364_;
}
pub unsafe fn l_BitVec_instXorOp(
    mut v_w_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ =
        crate::leanh::lean_alloc_closure(l_BitVec_xor___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_2366_, 0, v_w_2365_);
    return v___x_2366_;
}
pub unsafe fn l_BitVec_not(
    mut v_n_2367_: *mut crate::leanh::LeanObject,
    mut v_x_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_BitVec_allOnes(v_n_2367_);
    v___x_2370_ = lean_nat_lxor(v___x_2369_, v_x_2368_);
    crate::leanh::lean_dec(v___x_2369_);
    return v___x_2370_;
}
pub unsafe fn l_BitVec_not___boxed(
    mut v_n_2371_: *mut crate::leanh::LeanObject,
    mut v_x_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2373_ = l_BitVec_not(v_n_2371_, v_x_2372_);
    crate::leanh::lean_dec(v_x_2372_);
    crate::leanh::lean_dec(v_n_2371_);
    return v_res_2373_;
}
pub unsafe fn l_BitVec_instComplement(
    mut v_w_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ =
        crate::leanh::lean_alloc_closure(l_BitVec_not___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_2375_, 0, v_w_2374_);
    return v___x_2375_;
}
pub unsafe fn l_BitVec_shiftLeft(
    mut v_n_2376_: *mut crate::leanh::LeanObject,
    mut v_x_2377_: *mut crate::leanh::LeanObject,
    mut v_s_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = lean_nat_shiftl(v_x_2377_, v_s_2378_);
    v___x_2380_ = l_BitVec_ofNat(v_n_2376_, v___x_2379_);
    crate::leanh::lean_dec(v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn l_BitVec_shiftLeft___boxed(
    mut v_n_2381_: *mut crate::leanh::LeanObject,
    mut v_x_2382_: *mut crate::leanh::LeanObject,
    mut v_s_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2384_ = l_BitVec_shiftLeft(v_n_2381_, v_x_2382_, v_s_2383_);
    crate::leanh::lean_dec(v_s_2383_);
    crate::leanh::lean_dec(v_x_2382_);
    crate::leanh::lean_dec(v_n_2381_);
    return v_res_2384_;
}
pub unsafe fn l_BitVec_instHShiftLeftNat(
    mut v_w_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ = crate::leanh::lean_alloc_closure(
        l_BitVec_shiftLeft___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2386_, 0, v_w_2385_);
    return v___x_2386_;
}
pub unsafe fn l_BitVec_ushiftRight___redArg(
    mut v_x_2387_: *mut crate::leanh::LeanObject,
    mut v_s_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = lean_nat_shiftr(v_x_2387_, v_s_2388_);
    return v___x_2389_;
}
pub unsafe fn l_BitVec_ushiftRight___redArg___boxed(
    mut v_x_2390_: *mut crate::leanh::LeanObject,
    mut v_s_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2392_ = l_BitVec_ushiftRight___redArg(v_x_2390_, v_s_2391_);
    crate::leanh::lean_dec(v_s_2391_);
    crate::leanh::lean_dec(v_x_2390_);
    return v_res_2392_;
}
pub unsafe fn l_BitVec_ushiftRight(
    mut v_n_2393_: *mut crate::leanh::LeanObject,
    mut v_x_2394_: *mut crate::leanh::LeanObject,
    mut v_s_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = lean_nat_shiftr(v_x_2394_, v_s_2395_);
    return v___x_2396_;
}
pub unsafe fn l_BitVec_ushiftRight___boxed(
    mut v_n_2397_: *mut crate::leanh::LeanObject,
    mut v_x_2398_: *mut crate::leanh::LeanObject,
    mut v_s_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2400_ = l_BitVec_ushiftRight(v_n_2397_, v_x_2398_, v_s_2399_);
    crate::leanh::lean_dec(v_s_2399_);
    crate::leanh::lean_dec(v_x_2398_);
    crate::leanh::lean_dec(v_n_2397_);
    return v_res_2400_;
}
pub unsafe fn l_BitVec_instHShiftRightNat(
    mut v_w_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = crate::leanh::lean_alloc_closure(
        l_BitVec_ushiftRight___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2402_, 0, v_w_2401_);
    return v___x_2402_;
}
pub unsafe fn l_BitVec_sshiftRight(
    mut v_n_2403_: *mut crate::leanh::LeanObject,
    mut v_x_2404_: *mut crate::leanh::LeanObject,
    mut v_s_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_BitVec_toInt(v_n_2403_, v_x_2404_);
    v___x_2407_ = l_Int_shiftRight(v___x_2406_, v_s_2405_);
    crate::leanh::lean_dec(v___x_2406_);
    v___x_2408_ = l_BitVec_ofInt(v_n_2403_, v___x_2407_);
    crate::leanh::lean_dec(v___x_2407_);
    return v___x_2408_;
}
pub unsafe fn l_BitVec_sshiftRight___boxed(
    mut v_n_2409_: *mut crate::leanh::LeanObject,
    mut v_x_2410_: *mut crate::leanh::LeanObject,
    mut v_s_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_BitVec_sshiftRight(v_n_2409_, v_x_2410_, v_s_2411_);
    crate::leanh::lean_dec(v_s_2411_);
    crate::leanh::lean_dec(v_n_2409_);
    return v_res_2412_;
}
pub unsafe fn l_BitVec_instHShiftLeft___redArg___lam__0(
    mut v_m_2413_: *mut crate::leanh::LeanObject,
    mut v_x_2414_: *mut crate::leanh::LeanObject,
    mut v_y_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_BitVec_shiftLeft(v_m_2413_, v_x_2414_, v_y_2415_);
    return v___x_2416_;
}
pub unsafe fn l_BitVec_instHShiftLeft___redArg___lam__0___boxed(
    mut v_m_2417_: *mut crate::leanh::LeanObject,
    mut v_x_2418_: *mut crate::leanh::LeanObject,
    mut v_y_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_2417_, v_x_2418_, v_y_2419_);
    crate::leanh::lean_dec(v_y_2419_);
    crate::leanh::lean_dec(v_x_2418_);
    crate::leanh::lean_dec(v_m_2417_);
    return v_res_2420_;
}
pub unsafe fn l_BitVec_instHShiftLeft___redArg(
    mut v_m_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2422_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instHShiftLeft___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2422_, 0, v_m_2421_);
    return v___f_2422_;
}
pub unsafe fn l_BitVec_instHShiftLeft(
    mut v_m_2423_: *mut crate::leanh::LeanObject,
    mut v_n_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2425_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instHShiftLeft___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2425_, 0, v_m_2423_);
    return v___f_2425_;
}
pub unsafe fn l_BitVec_instHShiftLeft___boxed(
    mut v_m_2426_: *mut crate::leanh::LeanObject,
    mut v_n_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_BitVec_instHShiftLeft(v_m_2426_, v_n_2427_);
    crate::leanh::lean_dec(v_n_2427_);
    return v_res_2428_;
}
pub unsafe fn l_BitVec_instHShiftRight(
    mut v_m_2430_: *mut crate::leanh::LeanObject,
    mut v_n_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2432_ = l_BitVec_instHShiftRight___closed__0;
    return v___f_2432_;
}
pub unsafe fn l_BitVec_instHShiftRight___boxed(
    mut v_m_2433_: *mut crate::leanh::LeanObject,
    mut v_n_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2435_ = l_BitVec_instHShiftRight(v_m_2433_, v_n_2434_);
    crate::leanh::lean_dec(v_n_2434_);
    crate::leanh::lean_dec(v_m_2433_);
    return v_res_2435_;
}
pub unsafe fn l_BitVec_sshiftRight_x27___redArg(
    mut v_n_2436_: *mut crate::leanh::LeanObject,
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_s_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2439_ = l_BitVec_sshiftRight(v_n_2436_, v_a_2437_, v_s_2438_);
    return v___x_2439_;
}
pub unsafe fn l_BitVec_sshiftRight_x27___redArg___boxed(
    mut v_n_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_s_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_BitVec_sshiftRight_x27___redArg(v_n_2440_, v_a_2441_, v_s_2442_);
    crate::leanh::lean_dec(v_s_2442_);
    crate::leanh::lean_dec(v_n_2440_);
    return v_res_2443_;
}
pub unsafe fn l_BitVec_sshiftRight_x27(
    mut v_n_2444_: *mut crate::leanh::LeanObject,
    mut v_m_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_s_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_BitVec_sshiftRight(v_n_2444_, v_a_2446_, v_s_2447_);
    return v___x_2448_;
}
pub unsafe fn l_BitVec_sshiftRight_x27___boxed(
    mut v_n_2449_: *mut crate::leanh::LeanObject,
    mut v_m_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_s_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_BitVec_sshiftRight_x27(v_n_2449_, v_m_2450_, v_a_2451_, v_s_2452_);
    crate::leanh::lean_dec(v_s_2452_);
    crate::leanh::lean_dec(v_m_2450_);
    crate::leanh::lean_dec(v_n_2449_);
    return v_res_2453_;
}
pub unsafe fn l_BitVec_rotateLeftAux(
    mut v_w_2454_: *mut crate::leanh::LeanObject,
    mut v_x_2455_: *mut crate::leanh::LeanObject,
    mut v_n_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_BitVec_shiftLeft(v_w_2454_, v_x_2455_, v_n_2456_);
    v___x_2458_ = lean_nat_sub(v_w_2454_, v_n_2456_);
    v___x_2459_ = lean_nat_shiftr(v_x_2455_, v___x_2458_);
    crate::leanh::lean_dec(v___x_2458_);
    v___x_2460_ = lean_nat_lor(v___x_2457_, v___x_2459_);
    crate::leanh::lean_dec(v___x_2459_);
    crate::leanh::lean_dec(v___x_2457_);
    return v___x_2460_;
}
pub unsafe fn l_BitVec_rotateLeftAux___boxed(
    mut v_w_2461_: *mut crate::leanh::LeanObject,
    mut v_x_2462_: *mut crate::leanh::LeanObject,
    mut v_n_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_BitVec_rotateLeftAux(v_w_2461_, v_x_2462_, v_n_2463_);
    crate::leanh::lean_dec(v_n_2463_);
    crate::leanh::lean_dec(v_x_2462_);
    crate::leanh::lean_dec(v_w_2461_);
    return v_res_2464_;
}
pub unsafe fn l_BitVec_rotateLeft(
    mut v_w_2465_: *mut crate::leanh::LeanObject,
    mut v_x_2466_: *mut crate::leanh::LeanObject,
    mut v_n_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_nat_mod(v_n_2467_, v_w_2465_);
    v___x_2469_ = l_BitVec_rotateLeftAux(v_w_2465_, v_x_2466_, v___x_2468_);
    crate::leanh::lean_dec(v___x_2468_);
    return v___x_2469_;
}
pub unsafe fn l_BitVec_rotateLeft___boxed(
    mut v_w_2470_: *mut crate::leanh::LeanObject,
    mut v_x_2471_: *mut crate::leanh::LeanObject,
    mut v_n_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_BitVec_rotateLeft(v_w_2470_, v_x_2471_, v_n_2472_);
    crate::leanh::lean_dec(v_n_2472_);
    crate::leanh::lean_dec(v_x_2471_);
    crate::leanh::lean_dec(v_w_2470_);
    return v_res_2473_;
}
pub unsafe fn l_BitVec_rotateRightAux(
    mut v_w_2474_: *mut crate::leanh::LeanObject,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v_n_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_nat_shiftr(v_x_2475_, v_n_2476_);
    v___x_2478_ = lean_nat_sub(v_w_2474_, v_n_2476_);
    v___x_2479_ = l_BitVec_shiftLeft(v_w_2474_, v_x_2475_, v___x_2478_);
    crate::leanh::lean_dec(v___x_2478_);
    v___x_2480_ = lean_nat_lor(v___x_2477_, v___x_2479_);
    crate::leanh::lean_dec(v___x_2479_);
    crate::leanh::lean_dec(v___x_2477_);
    return v___x_2480_;
}
pub unsafe fn l_BitVec_rotateRightAux___boxed(
    mut v_w_2481_: *mut crate::leanh::LeanObject,
    mut v_x_2482_: *mut crate::leanh::LeanObject,
    mut v_n_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_BitVec_rotateRightAux(v_w_2481_, v_x_2482_, v_n_2483_);
    crate::leanh::lean_dec(v_n_2483_);
    crate::leanh::lean_dec(v_x_2482_);
    crate::leanh::lean_dec(v_w_2481_);
    return v_res_2484_;
}
pub unsafe fn l_BitVec_rotateRight(
    mut v_w_2485_: *mut crate::leanh::LeanObject,
    mut v_x_2486_: *mut crate::leanh::LeanObject,
    mut v_n_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = lean_nat_mod(v_n_2487_, v_w_2485_);
    v___x_2489_ = l_BitVec_rotateRightAux(v_w_2485_, v_x_2486_, v___x_2488_);
    crate::leanh::lean_dec(v___x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_BitVec_rotateRight___boxed(
    mut v_w_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
    mut v_n_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_BitVec_rotateRight(v_w_2490_, v_x_2491_, v_n_2492_);
    crate::leanh::lean_dec(v_n_2492_);
    crate::leanh::lean_dec(v_x_2491_);
    crate::leanh::lean_dec(v_w_2490_);
    return v_res_2493_;
}
pub unsafe fn l_BitVec_append___redArg(
    mut v_m_2494_: *mut crate::leanh::LeanObject,
    mut v_msbs_2495_: *mut crate::leanh::LeanObject,
    mut v_lsbs_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = lean_nat_shiftl(v_msbs_2495_, v_m_2494_);
    v___x_2498_ = lean_nat_lor(v___x_2497_, v_lsbs_2496_);
    crate::leanh::lean_dec(v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn l_BitVec_append___redArg___boxed(
    mut v_m_2499_: *mut crate::leanh::LeanObject,
    mut v_msbs_2500_: *mut crate::leanh::LeanObject,
    mut v_lsbs_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_BitVec_append___redArg(v_m_2499_, v_msbs_2500_, v_lsbs_2501_);
    crate::leanh::lean_dec(v_lsbs_2501_);
    crate::leanh::lean_dec(v_msbs_2500_);
    crate::leanh::lean_dec(v_m_2499_);
    return v_res_2502_;
}
pub unsafe fn l_BitVec_append(
    mut v_n_2503_: *mut crate::leanh::LeanObject,
    mut v_m_2504_: *mut crate::leanh::LeanObject,
    mut v_msbs_2505_: *mut crate::leanh::LeanObject,
    mut v_lsbs_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = l_BitVec_append___redArg(v_m_2504_, v_msbs_2505_, v_lsbs_2506_);
    return v___x_2507_;
}
pub unsafe fn l_BitVec_append___boxed(
    mut v_n_2508_: *mut crate::leanh::LeanObject,
    mut v_m_2509_: *mut crate::leanh::LeanObject,
    mut v_msbs_2510_: *mut crate::leanh::LeanObject,
    mut v_lsbs_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_BitVec_append(v_n_2508_, v_m_2509_, v_msbs_2510_, v_lsbs_2511_);
    crate::leanh::lean_dec(v_lsbs_2511_);
    crate::leanh::lean_dec(v_msbs_2510_);
    crate::leanh::lean_dec(v_m_2509_);
    crate::leanh::lean_dec(v_n_2508_);
    return v_res_2512_;
}
pub unsafe fn l_BitVec_instHAppendHAddNat(
    mut v_w_2513_: *mut crate::leanh::LeanObject,
    mut v_v_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ =
        crate::leanh::lean_alloc_closure(l_BitVec_append___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2515_, 0, v_w_2513_);
    crate::leanh::lean_closure_set(v___x_2515_, 1, v_v_2514_);
    return v___x_2515_;
}
pub unsafe fn l_BitVec_replicate(
    mut v_w_2516_: *mut crate::leanh::LeanObject,
    mut v_x_2517_: *mut crate::leanh::LeanObject,
    mut v_x_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2520_: u8 = 0;
    v_zero_2519_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_2520_ = lean_nat_dec_eq(v_x_2517_, v_zero_2519_);
    if v_isZero_2520_ == 1 {
        let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2521_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0_once),
            _init_l_BitVec_nil___closed__0,
        );
        return v___x_2521_;
    } else {
        let mut v_one_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_2522_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_2523_ = lean_nat_sub(v_x_2517_, v_one_2522_);
        v___x_2524_ = lean_nat_mul(v_w_2516_, v_n_2523_);
        v___x_2525_ = l_BitVec_replicate(v_w_2516_, v_n_2523_, v_x_2518_);
        crate::leanh::lean_dec(v_n_2523_);
        v___x_2526_ = l_BitVec_append___redArg(v___x_2524_, v_x_2518_, v___x_2525_);
        crate::leanh::lean_dec(v___x_2525_);
        crate::leanh::lean_dec(v___x_2524_);
        return v___x_2526_;
    }
}
pub unsafe fn l_BitVec_replicate___boxed(
    mut v_w_2527_: *mut crate::leanh::LeanObject,
    mut v_x_2528_: *mut crate::leanh::LeanObject,
    mut v_x_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_BitVec_replicate(v_w_2527_, v_x_2528_, v_x_2529_);
    crate::leanh::lean_dec(v_x_2529_);
    crate::leanh::lean_dec(v_x_2528_);
    crate::leanh::lean_dec(v_w_2527_);
    return v_res_2530_;
}
pub unsafe fn l_BitVec_concat___redArg(
    mut v_msbs_2531_: *mut crate::leanh::LeanObject,
    mut v_lsb_2532_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2534_ = l_BitVec_ofBool(v_lsb_2532_);
    v___x_2535_ = l_BitVec_append___redArg(v___x_2533_, v_msbs_2531_, v___x_2534_);
    crate::leanh::lean_dec(v___x_2534_);
    return v___x_2535_;
}
pub unsafe fn l_BitVec_concat___redArg___boxed(
    mut v_msbs_2536_: *mut crate::leanh::LeanObject,
    mut v_lsb_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lsb_boxed_2538_: u8 = 0;
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lsb_boxed_2538_ = (crate::leanh::lean_unbox(v_lsb_2537_) as u8);
    v_res_2539_ = l_BitVec_concat___redArg(v_msbs_2536_, v_lsb_boxed_2538_);
    crate::leanh::lean_dec(v_msbs_2536_);
    return v_res_2539_;
}
pub unsafe fn l_BitVec_concat(
    mut v_n_2540_: *mut crate::leanh::LeanObject,
    mut v_msbs_2541_: *mut crate::leanh::LeanObject,
    mut v_lsb_2542_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2543_ = l_BitVec_concat___redArg(v_msbs_2541_, v_lsb_2542_);
    return v___x_2543_;
}
pub unsafe fn l_BitVec_concat___boxed(
    mut v_n_2544_: *mut crate::leanh::LeanObject,
    mut v_msbs_2545_: *mut crate::leanh::LeanObject,
    mut v_lsb_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lsb_boxed_2547_: u8 = 0;
    let mut v_res_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lsb_boxed_2547_ = (crate::leanh::lean_unbox(v_lsb_2546_) as u8);
    v_res_2548_ = l_BitVec_concat(v_n_2544_, v_msbs_2545_, v_lsb_boxed_2547_);
    crate::leanh::lean_dec(v_msbs_2545_);
    crate::leanh::lean_dec(v_n_2544_);
    return v_res_2548_;
}
pub unsafe fn l_BitVec_shiftConcat(
    mut v_n_2549_: *mut crate::leanh::LeanObject,
    mut v_x_2550_: *mut crate::leanh::LeanObject,
    mut v_b_2551_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2553_ = lean_nat_add(v_n_2549_, v___x_2552_);
    v___x_2554_ = l_BitVec_concat___redArg(v_x_2550_, v_b_2551_);
    v___x_2555_ = l_BitVec_setWidth(v___x_2553_, v_n_2549_, v___x_2554_);
    crate::leanh::lean_dec(v___x_2554_);
    crate::leanh::lean_dec(v___x_2553_);
    return v___x_2555_;
}
pub unsafe fn l_BitVec_shiftConcat___boxed(
    mut v_n_2556_: *mut crate::leanh::LeanObject,
    mut v_x_2557_: *mut crate::leanh::LeanObject,
    mut v_b_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2559_: u8 = 0;
    let mut v_res_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2559_ = (crate::leanh::lean_unbox(v_b_2558_) as u8);
    v_res_2560_ = l_BitVec_shiftConcat(v_n_2556_, v_x_2557_, v_b_boxed_2559_);
    crate::leanh::lean_dec(v_x_2557_);
    crate::leanh::lean_dec(v_n_2556_);
    return v_res_2560_;
}
pub unsafe fn l_BitVec_cons(
    mut v_n_2561_: *mut crate::leanh::LeanObject,
    mut v_msb_2562_: u8,
    mut v_lsbs_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_BitVec_ofBool(v_msb_2562_);
    v___x_2565_ = l_BitVec_append___redArg(v_n_2561_, v___x_2564_, v_lsbs_2563_);
    crate::leanh::lean_dec(v___x_2564_);
    return v___x_2565_;
}
pub unsafe fn l_BitVec_cons___boxed(
    mut v_n_2566_: *mut crate::leanh::LeanObject,
    mut v_msb_2567_: *mut crate::leanh::LeanObject,
    mut v_lsbs_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msb_boxed_2569_: u8 = 0;
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_msb_boxed_2569_ = (crate::leanh::lean_unbox(v_msb_2567_) as u8);
    v_res_2570_ = l_BitVec_cons(v_n_2566_, v_msb_boxed_2569_, v_lsbs_2568_);
    crate::leanh::lean_dec(v_lsbs_2568_);
    crate::leanh::lean_dec(v_n_2566_);
    return v_res_2570_;
}
pub unsafe fn l_BitVec_twoPow(
    mut v_w_2571_: *mut crate::leanh::LeanObject,
    mut v_i_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2574_ = l_BitVec_ofNat(v_w_2571_, v___x_2573_);
    v___x_2575_ = l_BitVec_shiftLeft(v_w_2571_, v___x_2574_, v_i_2572_);
    crate::leanh::lean_dec(v___x_2574_);
    return v___x_2575_;
}
pub unsafe fn l_BitVec_twoPow___boxed(
    mut v_w_2576_: *mut crate::leanh::LeanObject,
    mut v_i_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2578_ = l_BitVec_twoPow(v_w_2576_, v_i_2577_);
    crate::leanh::lean_dec(v_i_2577_);
    crate::leanh::lean_dec(v_w_2576_);
    return v_res_2578_;
}
pub unsafe fn l_BitVec_intMin(
    mut v_w_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2580_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2581_ = lean_nat_sub(v_w_2579_, v___x_2580_);
    v___x_2582_ = l_BitVec_twoPow(v_w_2579_, v___x_2581_);
    crate::leanh::lean_dec(v___x_2581_);
    return v___x_2582_;
}
pub unsafe fn l_BitVec_intMin___boxed(
    mut v_w_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_BitVec_intMin(v_w_2583_);
    crate::leanh::lean_dec(v_w_2583_);
    return v_res_2584_;
}
pub unsafe fn l_BitVec_intMax(
    mut v_w_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2587_ = lean_nat_sub(v_w_2585_, v___x_2586_);
    v___x_2588_ = l_BitVec_twoPow(v_w_2585_, v___x_2587_);
    crate::leanh::lean_dec(v___x_2587_);
    v___x_2589_ = l_BitVec_ofNat(v_w_2585_, v___x_2586_);
    v___x_2590_ = l_BitVec_sub(v_w_2585_, v___x_2588_, v___x_2589_);
    crate::leanh::lean_dec(v___x_2589_);
    crate::leanh::lean_dec(v___x_2588_);
    return v___x_2590_;
}
pub unsafe fn l_BitVec_intMax___boxed(
    mut v_w_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_BitVec_intMax(v_w_2591_);
    crate::leanh::lean_dec(v_w_2591_);
    return v_res_2592_;
}
pub unsafe fn l_BitVec_hash(
    mut v_n_2593_: *mut crate::leanh::LeanObject,
    mut v_bv_2594_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: u8 = 0;
    v___x_2595_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_2596_ = lean_nat_dec_le(v_n_2593_, v___x_2595_);
    if v___x_2596_ == 0 {
        let mut v___x_2597_: u64 = 0;
        let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2601_: u64 = 0;
        let mut v___x_2602_: u64 = 0;
        v___x_2597_ = lean_uint64_of_nat(v_bv_2594_);
        v___x_2598_ = lean_nat_sub(v_n_2593_, v___x_2595_);
        v___x_2599_ = lean_nat_shiftr(v_bv_2594_, v___x_2595_);
        v___x_2600_ = l_BitVec_setWidth(v_n_2593_, v___x_2598_, v___x_2599_);
        crate::leanh::lean_dec(v___x_2599_);
        v___x_2601_ = l_BitVec_hash(v___x_2598_, v___x_2600_);
        crate::leanh::lean_dec(v___x_2600_);
        crate::leanh::lean_dec(v___x_2598_);
        v___x_2602_ = lean_uint64_mix_hash(v___x_2597_, v___x_2601_);
        return v___x_2602_;
    } else {
        let mut v___x_2603_: u64 = 0;
        v___x_2603_ = lean_uint64_of_nat(v_bv_2594_);
        return v___x_2603_;
    }
}
pub unsafe fn l_BitVec_hash___boxed(
    mut v_n_2604_: *mut crate::leanh::LeanObject,
    mut v_bv_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2606_: u64 = 0;
    let mut v_r_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_BitVec_hash(v_n_2604_, v_bv_2605_);
    crate::leanh::lean_dec(v_bv_2605_);
    crate::leanh::lean_dec(v_n_2604_);
    v_r_2607_ = crate::leanh::lean_box_uint64(v_res_2606_);
    return v_r_2607_;
}
pub unsafe fn l_BitVec_instHashable(
    mut v_n_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ =
        crate::leanh::lean_alloc_closure(l_BitVec_hash___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_2609_, 0, v_n_2608_);
    return v___x_2609_;
}
pub unsafe fn l_BitVec_ofBoolListBE(
    mut v_x_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2610_) == 0 {
        let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2611_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0_once),
            _init_l_BitVec_nil___closed__0,
        );
        return v___x_2611_;
    } else {
        let mut v_head_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: u8 = 0;
        let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_2612_ = crate::leanh::lean_ctor_get(v_x_2610_, 0);
        v_tail_2613_ = crate::leanh::lean_ctor_get(v_x_2610_, 1);
        v___x_2614_ = l_List_lengthTR___redArg(v_tail_2613_);
        v___x_2615_ = l_BitVec_ofBoolListBE(v_tail_2613_);
        v___x_2616_ = (crate::leanh::lean_unbox(v_head_2612_) as u8);
        v___x_2617_ = l_BitVec_cons(v___x_2614_, v___x_2616_, v___x_2615_);
        crate::leanh::lean_dec(v___x_2615_);
        crate::leanh::lean_dec(v___x_2614_);
        return v___x_2617_;
    }
}
pub unsafe fn l_BitVec_ofBoolListBE___boxed(
    mut v_x_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_BitVec_ofBoolListBE(v_x_2618_);
    crate::leanh::lean_dec(v_x_2618_);
    return v_res_2619_;
}
pub unsafe fn l_BitVec_ofBoolListLE(
    mut v_x_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2620_) == 0 {
        let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2621_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_nil___closed__0_once),
            _init_l_BitVec_nil___closed__0,
        );
        return v___x_2621_;
    } else {
        let mut v_head_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: u8 = 0;
        let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_2622_ = crate::leanh::lean_ctor_get(v_x_2620_, 0);
        v_tail_2623_ = crate::leanh::lean_ctor_get(v_x_2620_, 1);
        v___x_2624_ = l_BitVec_ofBoolListLE(v_tail_2623_);
        v___x_2625_ = (crate::leanh::lean_unbox(v_head_2622_) as u8);
        v___x_2626_ = l_BitVec_concat___redArg(v___x_2624_, v___x_2625_);
        crate::leanh::lean_dec(v___x_2624_);
        return v___x_2626_;
    }
}
pub unsafe fn l_BitVec_ofBoolListLE___boxed(
    mut v_x_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2628_ = l_BitVec_ofBoolListLE(v_x_2627_);
    crate::leanh::lean_dec(v_x_2627_);
    return v_res_2628_;
}
pub unsafe fn l_BitVec_uaddOverflow(
    mut v_w_2629_: *mut crate::leanh::LeanObject,
    mut v_x_2630_: *mut crate::leanh::LeanObject,
    mut v_y_2631_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    v___x_2632_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2633_ = lean_nat_pow(v___x_2632_, v_w_2629_);
    v___x_2634_ = lean_nat_add(v_x_2630_, v_y_2631_);
    v___x_2635_ = lean_nat_dec_le(v___x_2633_, v___x_2634_);
    crate::leanh::lean_dec(v___x_2634_);
    crate::leanh::lean_dec(v___x_2633_);
    return v___x_2635_;
}
pub unsafe fn l_BitVec_uaddOverflow___boxed(
    mut v_w_2636_: *mut crate::leanh::LeanObject,
    mut v_x_2637_: *mut crate::leanh::LeanObject,
    mut v_y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2639_: u8 = 0;
    let mut v_r_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_BitVec_uaddOverflow(v_w_2636_, v_x_2637_, v_y_2638_);
    crate::leanh::lean_dec(v_y_2638_);
    crate::leanh::lean_dec(v_x_2637_);
    crate::leanh::lean_dec(v_w_2636_);
    v_r_2640_ = crate::leanh::lean_box((v_res_2639_) as usize);
    return v_r_2640_;
}
pub unsafe fn _init_l_BitVec_saddOverflow___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2642_ = lean_nat_to_int(v___x_2641_);
    return v___x_2642_;
}
pub unsafe fn l_BitVec_saddOverflow(
    mut v_w_2643_: *mut crate::leanh::LeanObject,
    mut v_x_2644_: *mut crate::leanh::LeanObject,
    mut v_y_2645_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: u8 = 0;
    v___x_2646_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0_once),
        _init_l_BitVec_saddOverflow___closed__0,
    );
    v___x_2647_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2648_ = lean_nat_sub(v_w_2643_, v___x_2647_);
    v___x_2649_ = l_Int_pow(v___x_2646_, v___x_2648_);
    crate::leanh::lean_dec(v___x_2648_);
    v___x_2650_ = l_BitVec_toInt(v_w_2643_, v_x_2644_);
    v___x_2651_ = l_BitVec_toInt(v_w_2643_, v_y_2645_);
    v___x_2652_ = lean_int_add(v___x_2650_, v___x_2651_);
    crate::leanh::lean_dec(v___x_2651_);
    crate::leanh::lean_dec(v___x_2650_);
    v___x_2653_ = lean_int_dec_le(v___x_2649_, v___x_2652_);
    if v___x_2653_ == 0 {
        let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: u8 = 0;
        v___x_2654_ = lean_int_neg(v___x_2649_);
        crate::leanh::lean_dec(v___x_2649_);
        v___x_2655_ = lean_int_dec_lt(v___x_2652_, v___x_2654_);
        crate::leanh::lean_dec(v___x_2654_);
        crate::leanh::lean_dec(v___x_2652_);
        return v___x_2655_;
    } else {
        crate::leanh::lean_dec(v___x_2652_);
        crate::leanh::lean_dec(v___x_2649_);
        return v___x_2653_;
    }
}
pub unsafe fn l_BitVec_saddOverflow___boxed(
    mut v_w_2656_: *mut crate::leanh::LeanObject,
    mut v_x_2657_: *mut crate::leanh::LeanObject,
    mut v_y_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2659_: u8 = 0;
    let mut v_r_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2659_ = l_BitVec_saddOverflow(v_w_2656_, v_x_2657_, v_y_2658_);
    crate::leanh::lean_dec(v_w_2656_);
    v_r_2660_ = crate::leanh::lean_box((v_res_2659_) as usize);
    return v_r_2660_;
}
pub unsafe fn l_BitVec_usubOverflow___redArg(
    mut v_x_2661_: *mut crate::leanh::LeanObject,
    mut v_y_2662_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2663_: u8 = 0;
    v___x_2663_ = lean_nat_dec_lt(v_x_2661_, v_y_2662_);
    return v___x_2663_;
}
pub unsafe fn l_BitVec_usubOverflow___redArg___boxed(
    mut v_x_2664_: *mut crate::leanh::LeanObject,
    mut v_y_2665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2666_: u8 = 0;
    let mut v_r_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2666_ = l_BitVec_usubOverflow___redArg(v_x_2664_, v_y_2665_);
    crate::leanh::lean_dec(v_y_2665_);
    crate::leanh::lean_dec(v_x_2664_);
    v_r_2667_ = crate::leanh::lean_box((v_res_2666_) as usize);
    return v_r_2667_;
}
pub unsafe fn l_BitVec_usubOverflow(
    mut v_w_2668_: *mut crate::leanh::LeanObject,
    mut v_x_2669_: *mut crate::leanh::LeanObject,
    mut v_y_2670_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2671_: u8 = 0;
    v___x_2671_ = lean_nat_dec_lt(v_x_2669_, v_y_2670_);
    return v___x_2671_;
}
pub unsafe fn l_BitVec_usubOverflow___boxed(
    mut v_w_2672_: *mut crate::leanh::LeanObject,
    mut v_x_2673_: *mut crate::leanh::LeanObject,
    mut v_y_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2675_: u8 = 0;
    let mut v_r_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_BitVec_usubOverflow(v_w_2672_, v_x_2673_, v_y_2674_);
    crate::leanh::lean_dec(v_y_2674_);
    crate::leanh::lean_dec(v_x_2673_);
    crate::leanh::lean_dec(v_w_2672_);
    v_r_2676_ = crate::leanh::lean_box((v_res_2675_) as usize);
    return v_r_2676_;
}
pub unsafe fn l_BitVec_ssubOverflow(
    mut v_w_2677_: *mut crate::leanh::LeanObject,
    mut v_x_2678_: *mut crate::leanh::LeanObject,
    mut v_y_2679_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    v___x_2680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0_once),
        _init_l_BitVec_saddOverflow___closed__0,
    );
    v___x_2681_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2682_ = lean_nat_sub(v_w_2677_, v___x_2681_);
    v___x_2683_ = l_Int_pow(v___x_2680_, v___x_2682_);
    crate::leanh::lean_dec(v___x_2682_);
    v___x_2684_ = l_BitVec_toInt(v_w_2677_, v_x_2678_);
    v___x_2685_ = l_BitVec_toInt(v_w_2677_, v_y_2679_);
    v___x_2686_ = lean_int_sub(v___x_2684_, v___x_2685_);
    crate::leanh::lean_dec(v___x_2685_);
    crate::leanh::lean_dec(v___x_2684_);
    v___x_2687_ = lean_int_dec_le(v___x_2683_, v___x_2686_);
    if v___x_2687_ == 0 {
        let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2689_: u8 = 0;
        v___x_2688_ = lean_int_neg(v___x_2683_);
        crate::leanh::lean_dec(v___x_2683_);
        v___x_2689_ = lean_int_dec_lt(v___x_2686_, v___x_2688_);
        crate::leanh::lean_dec(v___x_2688_);
        crate::leanh::lean_dec(v___x_2686_);
        return v___x_2689_;
    } else {
        crate::leanh::lean_dec(v___x_2686_);
        crate::leanh::lean_dec(v___x_2683_);
        return v___x_2687_;
    }
}
pub unsafe fn l_BitVec_ssubOverflow___boxed(
    mut v_w_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: *mut crate::leanh::LeanObject,
    mut v_y_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2693_: u8 = 0;
    let mut v_r_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2693_ = l_BitVec_ssubOverflow(v_w_2690_, v_x_2691_, v_y_2692_);
    crate::leanh::lean_dec(v_w_2690_);
    v_r_2694_ = crate::leanh::lean_box((v_res_2693_) as usize);
    return v_r_2694_;
}
pub unsafe fn l_BitVec_negOverflow(
    mut v_w_2695_: *mut crate::leanh::LeanObject,
    mut v_x_2696_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: u8 = 0;
    v___x_2697_ = l_BitVec_toInt(v_w_2695_, v_x_2696_);
    v___x_2698_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0_once),
        _init_l_BitVec_saddOverflow___closed__0,
    );
    v___x_2699_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2700_ = lean_nat_sub(v_w_2695_, v___x_2699_);
    v___x_2701_ = l_Int_pow(v___x_2698_, v___x_2700_);
    crate::leanh::lean_dec(v___x_2700_);
    v___x_2702_ = lean_int_neg(v___x_2701_);
    crate::leanh::lean_dec(v___x_2701_);
    v___x_2703_ = lean_int_dec_eq(v___x_2697_, v___x_2702_);
    crate::leanh::lean_dec(v___x_2702_);
    crate::leanh::lean_dec(v___x_2697_);
    return v___x_2703_;
}
pub unsafe fn l_BitVec_negOverflow___boxed(
    mut v_w_2704_: *mut crate::leanh::LeanObject,
    mut v_x_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2706_: u8 = 0;
    let mut v_r_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ = l_BitVec_negOverflow(v_w_2704_, v_x_2705_);
    crate::leanh::lean_dec(v_w_2704_);
    v_r_2707_ = crate::leanh::lean_box((v_res_2706_) as usize);
    return v_r_2707_;
}
pub unsafe fn l_BitVec_sdivOverflow(
    mut v_w_2708_: *mut crate::leanh::LeanObject,
    mut v_x_2709_: *mut crate::leanh::LeanObject,
    mut v_y_2710_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    v___x_2711_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0_once),
        _init_l_BitVec_saddOverflow___closed__0,
    );
    v___x_2712_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2713_ = lean_nat_sub(v_w_2708_, v___x_2712_);
    v___x_2714_ = l_Int_pow(v___x_2711_, v___x_2713_);
    crate::leanh::lean_dec(v___x_2713_);
    v___x_2715_ = l_BitVec_toInt(v_w_2708_, v_x_2709_);
    v___x_2716_ = l_BitVec_toInt(v_w_2708_, v_y_2710_);
    v___x_2717_ = lean_int_ediv(v___x_2715_, v___x_2716_);
    crate::leanh::lean_dec(v___x_2716_);
    crate::leanh::lean_dec(v___x_2715_);
    v___x_2718_ = lean_int_dec_le(v___x_2714_, v___x_2717_);
    if v___x_2718_ == 0 {
        let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2720_: u8 = 0;
        v___x_2719_ = lean_int_neg(v___x_2714_);
        crate::leanh::lean_dec(v___x_2714_);
        v___x_2720_ = lean_int_dec_lt(v___x_2717_, v___x_2719_);
        crate::leanh::lean_dec(v___x_2719_);
        crate::leanh::lean_dec(v___x_2717_);
        return v___x_2720_;
    } else {
        crate::leanh::lean_dec(v___x_2717_);
        crate::leanh::lean_dec(v___x_2714_);
        return v___x_2718_;
    }
}
pub unsafe fn l_BitVec_sdivOverflow___boxed(
    mut v_w_2721_: *mut crate::leanh::LeanObject,
    mut v_x_2722_: *mut crate::leanh::LeanObject,
    mut v_y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2724_: u8 = 0;
    let mut v_r_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_BitVec_sdivOverflow(v_w_2721_, v_x_2722_, v_y_2723_);
    crate::leanh::lean_dec(v_w_2721_);
    v_r_2725_ = crate::leanh::lean_box((v_res_2724_) as usize);
    return v_r_2725_;
}
pub unsafe fn l_BitVec_reverse(
    mut v_x_2726_: *mut crate::leanh::LeanObject,
    mut v_x_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2729_: u8 = 0;
    v_zero_2728_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_2729_ = lean_nat_dec_eq(v_x_2726_, v_zero_2728_);
    if v_isZero_2729_ == 1 {
        crate::leanh::lean_inc(v_x_2727_);
        return v_x_2727_;
    } else {
        let mut v_one_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2735_: u8 = 0;
        v_one_2730_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_2731_ = lean_nat_sub(v_x_2726_, v_one_2730_);
        v___x_2732_ = lean_nat_add(v_n_2731_, v_one_2730_);
        v___x_2733_ = l_BitVec_setWidth(v___x_2732_, v_n_2731_, v_x_2727_);
        v___x_2734_ = l_BitVec_reverse(v_n_2731_, v___x_2733_);
        crate::leanh::lean_dec(v___x_2733_);
        crate::leanh::lean_dec(v_n_2731_);
        v___x_2735_ = lean_nat_dec_lt(v_zero_2728_, v___x_2732_);
        if v___x_2735_ == 0 {
            let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2732_);
            v___x_2736_ = l_BitVec_concat___redArg(v___x_2734_, v___x_2735_);
            crate::leanh::lean_dec(v___x_2734_);
            return v___x_2736_;
        } else {
            let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2738_: u8 = 0;
            let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2737_ = lean_nat_sub(v___x_2732_, v_one_2730_);
            crate::leanh::lean_dec(v___x_2732_);
            v___x_2738_ = l_Nat_testBit(v_x_2727_, v___x_2737_);
            crate::leanh::lean_dec(v___x_2737_);
            v___x_2739_ = l_BitVec_concat___redArg(v___x_2734_, v___x_2738_);
            crate::leanh::lean_dec(v___x_2734_);
            return v___x_2739_;
        }
    }
}
pub unsafe fn l_BitVec_reverse___boxed(
    mut v_x_2740_: *mut crate::leanh::LeanObject,
    mut v_x_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2742_ = l_BitVec_reverse(v_x_2740_, v_x_2741_);
    crate::leanh::lean_dec(v_x_2741_);
    crate::leanh::lean_dec(v_x_2740_);
    return v_res_2742_;
}
pub unsafe fn l_BitVec_umulOverflow(
    mut v_w_2743_: *mut crate::leanh::LeanObject,
    mut v_x_2744_: *mut crate::leanh::LeanObject,
    mut v_y_2745_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u8 = 0;
    v___x_2746_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2747_ = lean_nat_pow(v___x_2746_, v_w_2743_);
    v___x_2748_ = lean_nat_mul(v_x_2744_, v_y_2745_);
    v___x_2749_ = lean_nat_dec_le(v___x_2747_, v___x_2748_);
    crate::leanh::lean_dec(v___x_2748_);
    crate::leanh::lean_dec(v___x_2747_);
    return v___x_2749_;
}
pub unsafe fn l_BitVec_umulOverflow___boxed(
    mut v_w_2750_: *mut crate::leanh::LeanObject,
    mut v_x_2751_: *mut crate::leanh::LeanObject,
    mut v_y_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2753_: u8 = 0;
    let mut v_r_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2753_ = l_BitVec_umulOverflow(v_w_2750_, v_x_2751_, v_y_2752_);
    crate::leanh::lean_dec(v_y_2752_);
    crate::leanh::lean_dec(v_x_2751_);
    crate::leanh::lean_dec(v_w_2750_);
    v_r_2754_ = crate::leanh::lean_box((v_res_2753_) as usize);
    return v_r_2754_;
}
pub unsafe fn l_BitVec_smulOverflow(
    mut v_w_2755_: *mut crate::leanh::LeanObject,
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_y_2757_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    v___x_2758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_saddOverflow___closed__0_once),
        _init_l_BitVec_saddOverflow___closed__0,
    );
    v___x_2759_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2760_ = lean_nat_sub(v_w_2755_, v___x_2759_);
    v___x_2761_ = l_Int_pow(v___x_2758_, v___x_2760_);
    crate::leanh::lean_dec(v___x_2760_);
    v___x_2762_ = l_BitVec_toInt(v_w_2755_, v_x_2756_);
    v___x_2763_ = l_BitVec_toInt(v_w_2755_, v_y_2757_);
    v___x_2764_ = lean_int_mul(v___x_2762_, v___x_2763_);
    crate::leanh::lean_dec(v___x_2763_);
    crate::leanh::lean_dec(v___x_2762_);
    v___x_2765_ = lean_int_dec_le(v___x_2761_, v___x_2764_);
    if v___x_2765_ == 0 {
        let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: u8 = 0;
        v___x_2766_ = lean_int_neg(v___x_2761_);
        crate::leanh::lean_dec(v___x_2761_);
        v___x_2767_ = lean_int_dec_lt(v___x_2764_, v___x_2766_);
        crate::leanh::lean_dec(v___x_2766_);
        crate::leanh::lean_dec(v___x_2764_);
        return v___x_2767_;
    } else {
        crate::leanh::lean_dec(v___x_2764_);
        crate::leanh::lean_dec(v___x_2761_);
        return v___x_2765_;
    }
}
pub unsafe fn l_BitVec_smulOverflow___boxed(
    mut v_w_2768_: *mut crate::leanh::LeanObject,
    mut v_x_2769_: *mut crate::leanh::LeanObject,
    mut v_y_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2771_: u8 = 0;
    let mut v_r_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2771_ = l_BitVec_smulOverflow(v_w_2768_, v_x_2769_, v_y_2770_);
    crate::leanh::lean_dec(v_w_2768_);
    v_r_2772_ = crate::leanh::lean_box((v_res_2771_) as usize);
    return v_r_2772_;
}
pub unsafe fn l_BitVec_clzAuxRec(
    mut v_w_2773_: *mut crate::leanh::LeanObject,
    mut v_x_2774_: *mut crate::leanh::LeanObject,
    mut v_n_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v_one_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2776_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2777_ = lean_nat_dec_eq(v_n_2775_, v_zero_2776_);
                if v_isZero_2777_ == 1 {
                    crate::leanh::lean_dec(v_n_2775_);
                    v___x_2778_ = l_Nat_testBit(v_x_2774_, v_zero_2776_);
                    if v___x_2778_ == 0 {
                        v___x_2779_ = l_BitVec_ofNat(v_w_2773_, v_w_2773_);
                        return v___x_2779_;
                    } else {
                        v___x_2780_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2781_ = lean_nat_sub(v_w_2773_, v___x_2780_);
                        v___x_2782_ = l_BitVec_ofNat(v_w_2773_, v___x_2781_);
                        crate::leanh::lean_dec(v___x_2781_);
                        return v___x_2782_;
                    }
                } else {
                    v___x_2783_ = l_Nat_testBit(v_x_2774_, v_n_2775_);
                    if v___x_2783_ == 0 {
                        v_one_2784_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2785_ = lean_nat_sub(v_n_2775_, v_one_2784_);
                        crate::leanh::lean_dec(v_n_2775_);
                        v_n_2775_ = v_n_2785_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2787_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2788_ = lean_nat_sub(v_w_2773_, v___x_2787_);
                        v___x_2789_ = lean_nat_sub(v___x_2788_, v_n_2775_);
                        crate::leanh::lean_dec(v_n_2775_);
                        crate::leanh::lean_dec(v___x_2788_);
                        v___x_2790_ = l_BitVec_ofNat(v_w_2773_, v___x_2789_);
                        crate::leanh::lean_dec(v___x_2789_);
                        return v___x_2790_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_clzAuxRec___boxed(
    mut v_w_2791_: *mut crate::leanh::LeanObject,
    mut v_x_2792_: *mut crate::leanh::LeanObject,
    mut v_n_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2794_ = l_BitVec_clzAuxRec(v_w_2791_, v_x_2792_, v_n_2793_);
    crate::leanh::lean_dec(v_x_2792_);
    crate::leanh::lean_dec(v_w_2791_);
    return v_res_2794_;
}
pub unsafe fn l_BitVec_clz(
    mut v_w_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2798_ = lean_nat_sub(v_w_2795_, v___x_2797_);
    v___x_2799_ = l_BitVec_clzAuxRec(v_w_2795_, v_x_2796_, v___x_2798_);
    return v___x_2799_;
}
pub unsafe fn l_BitVec_clz___boxed(
    mut v_w_2800_: *mut crate::leanh::LeanObject,
    mut v_x_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2802_ = l_BitVec_clz(v_w_2800_, v_x_2801_);
    crate::leanh::lean_dec(v_x_2801_);
    crate::leanh::lean_dec(v_w_2800_);
    return v_res_2802_;
}
pub unsafe fn l_BitVec_ctz(
    mut v_w_2803_: *mut crate::leanh::LeanObject,
    mut v_x_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_BitVec_reverse(v_w_2803_, v_x_2804_);
    v___x_2806_ = l_BitVec_clz(v_w_2803_, v___x_2805_);
    crate::leanh::lean_dec(v___x_2805_);
    return v___x_2806_;
}
pub unsafe fn l_BitVec_ctz___boxed(
    mut v_w_2807_: *mut crate::leanh::LeanObject,
    mut v_x_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_BitVec_ctz(v_w_2807_, v_x_2808_);
    crate::leanh::lean_dec(v_x_2808_);
    crate::leanh::lean_dec(v_w_2807_);
    return v_res_2809_;
}
pub unsafe fn l_BitVec_cpopNatRec___redArg(
    mut v_x_2810_: *mut crate::leanh::LeanObject,
    mut v_pos_2811_: *mut crate::leanh::LeanObject,
    mut v_acc_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2814_: u8 = 0;
    let mut v_one_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2813_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2814_ = lean_nat_dec_eq(v_pos_2811_, v_zero_2813_);
                if v_isZero_2814_ == 1 {
                    crate::leanh::lean_dec(v_pos_2811_);
                    return v_acc_2812_;
                } else {
                    v_one_2815_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2816_ = lean_nat_sub(v_pos_2811_, v_one_2815_);
                    crate::leanh::lean_dec(v_pos_2811_);
                    v___x_2817_ = l_Nat_testBit(v_x_2810_, v_n_2816_);
                    v___x_2818_ = l_Bool_toNat(v___x_2817_);
                    v___x_2819_ = lean_nat_add(v_acc_2812_, v___x_2818_);
                    crate::leanh::lean_dec(v___x_2818_);
                    crate::leanh::lean_dec(v_acc_2812_);
                    v_pos_2811_ = v_n_2816_;
                    v_acc_2812_ = v___x_2819_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_cpopNatRec___redArg___boxed(
    mut v_x_2821_: *mut crate::leanh::LeanObject,
    mut v_pos_2822_: *mut crate::leanh::LeanObject,
    mut v_acc_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_BitVec_cpopNatRec___redArg(v_x_2821_, v_pos_2822_, v_acc_2823_);
    crate::leanh::lean_dec(v_x_2821_);
    return v_res_2824_;
}
pub unsafe fn l_BitVec_cpopNatRec(
    mut v_w_2825_: *mut crate::leanh::LeanObject,
    mut v_x_2826_: *mut crate::leanh::LeanObject,
    mut v_pos_2827_: *mut crate::leanh::LeanObject,
    mut v_acc_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = l_BitVec_cpopNatRec___redArg(v_x_2826_, v_pos_2827_, v_acc_2828_);
    return v___x_2829_;
}
pub unsafe fn l_BitVec_cpopNatRec___boxed(
    mut v_w_2830_: *mut crate::leanh::LeanObject,
    mut v_x_2831_: *mut crate::leanh::LeanObject,
    mut v_pos_2832_: *mut crate::leanh::LeanObject,
    mut v_acc_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2834_ = l_BitVec_cpopNatRec(v_w_2830_, v_x_2831_, v_pos_2832_, v_acc_2833_);
    crate::leanh::lean_dec(v_x_2831_);
    crate::leanh::lean_dec(v_w_2830_);
    return v_res_2834_;
}
pub unsafe fn l_BitVec_cpop(
    mut v_w_2835_: *mut crate::leanh::LeanObject,
    mut v_x_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2837_ = crate::leanh::lean_unsigned_to_nat(0);
    crate::leanh::lean_inc(v_w_2835_);
    v___x_2838_ = l_BitVec_cpopNatRec___redArg(v_x_2836_, v_w_2835_, v___x_2837_);
    v___x_2839_ = l_BitVec_ofNat(v_w_2835_, v___x_2838_);
    crate::leanh::lean_dec(v___x_2838_);
    crate::leanh::lean_dec(v_w_2835_);
    return v___x_2839_;
}
pub unsafe fn l_BitVec_cpop___boxed(
    mut v_w_2840_: *mut crate::leanh::LeanObject,
    mut v_x_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ = l_BitVec_cpop(v_w_2840_, v_x_2841_);
    crate::leanh::lean_dec(v_x_2841_);
    return v_res_2842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_BitVec_nil = _init_l_BitVec_nil();
    crate::leanh::lean_mark_persistent(l_BitVec_nil);
    l_BitVec_toHex___boxed__const__1 = _init_l_BitVec_toHex___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_BitVec_toHex___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_BitVec_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Basic(builtin);
}

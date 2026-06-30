// Lean compiler output
// Module: Lake.Config.Glob
// Imports: Lean.Util.Path Init.Data.ToString.Name Lean.Data.Name
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_le,
    lean_nat_to_int, lean_string_append,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_singleton;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, l_Lean_Name_isPrefixOf, runtime_initialize_Lean_Data_Name,
};
use crate::r#gen::Lean::Util::Path::{
    initialize_Lean_Util_Path, l_Lean_forEachModuleInDir___redArg, l_Lean_modToFilePath,
    runtime_initialize_Lean_Util_Path,
};
pub static l_Lake_instInhabitedGlob_default___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_instInhabitedGlob_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedGlob_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedGlob: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [76, 97, 107, 101, 46, 71, 108, 111, 98, 46, 111, 110, 101, 0],
    };
static mut l_Lake_instReprGlob_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprGlob_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprGlob_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprGlob_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprGlob_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprGlob_repr___closed__5_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 71, 108, 111, 98, 46, 115, 117, 98, 109, 111, 100, 117, 108, 101,
            115, 0,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__8_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 97, 107, 101, 46, 71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100,
            117, 108, 101, 115, 0,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprGlob___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprGlob_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprGlob___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instReprGlob: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instCoeNameGlob___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instCoeNameGlob___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeNameGlob___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeNameGlob: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instCoeGlobArray___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_singleton as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_instCoeGlobArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeGlobArray: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 95, 46, 42, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value) as *mut leanh::LeanObject;
static l_Lake_term_____x2e_x2a___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_term_____x2e_x2a___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value)
                as *mut leanh::LeanObject,
            10150953148658318397 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__5_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value)
                as *mut leanh::LeanObject,
            5949480926448383572 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__8_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value)
                as *mut leanh::LeanObject,
            2214559063752339918 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__10_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value)
                as *mut leanh::LeanObject,
            1581446985683836252 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__12_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__15_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [46, 42, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__16_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_term_____x2e_x2a: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [71, 108, 111, 98, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject,9097109829436277786 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject,2906245839412892126 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject,12140512885907428830 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject,1477412787864469706 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut leanh::LeanObject,9368229134555052249 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 95, 46, 43, 0],
    };
static mut l_Lake_term_____x2e_x2b___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_term_____x2e_x2b___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_term_____x2e_x2b___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value)
                as *mut leanh::LeanObject,
            11289494576251685396 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [46, 43, 0],
    };
static mut l_Lake_term_____x2e_x2b___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_term_____x2e_x2b: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [71, 108, 111, 98, 46, 115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject,9097109829436277786 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut leanh::LeanObject,15076241754705399326 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject,12140512885907428830 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut leanh::LeanObject,11186284017425669258 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_Glob_instToString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Glob_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Glob_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Glob_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Glob_ctorIdx(
    mut v_x_434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_434_) {
        0 => {
            let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_435_ = leanh::lean_unsigned_to_nat(0);
            return v___x_435_;
        }
        1 => {
            let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_436_ = leanh::lean_unsigned_to_nat(1);
            return v___x_436_;
        }
        _ => {
            let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_437_ = leanh::lean_unsigned_to_nat(2);
            return v___x_437_;
        }
    }
}
pub unsafe fn l_Lake_Glob_ctorIdx___boxed(
    mut v_x_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lake_Glob_ctorIdx(v_x_438_);
    leanh::lean_dec_ref(v_x_438_);
    return v_res_439_;
}
pub unsafe fn l_Lake_Glob_ctorElim___redArg(
    mut v_t_440_: *mut leanh::LeanObject,
    mut v_k_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_442_ = leanh::lean_ctor_get(v_t_440_, 0);
    leanh::lean_inc(v_a_442_);
    leanh::lean_dec_ref(v_t_440_);
    v___x_443_ = leanh::lean_apply_1(v_k_441_, v_a_442_);
    return v___x_443_;
}
pub unsafe fn l_Lake_Glob_ctorElim(
    mut v_motive_444_: *mut leanh::LeanObject,
    mut v_ctorIdx_445_: *mut leanh::LeanObject,
    mut v_t_446_: *mut leanh::LeanObject,
    mut v_h_447_: *mut leanh::LeanObject,
    mut v_k_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lake_Glob_ctorElim___redArg(v_t_446_, v_k_448_);
    return v___x_449_;
}
pub unsafe fn l_Lake_Glob_ctorElim___boxed(
    mut v_motive_450_: *mut leanh::LeanObject,
    mut v_ctorIdx_451_: *mut leanh::LeanObject,
    mut v_t_452_: *mut leanh::LeanObject,
    mut v_h_453_: *mut leanh::LeanObject,
    mut v_k_454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Lake_Glob_ctorElim(v_motive_450_, v_ctorIdx_451_, v_t_452_, v_h_453_, v_k_454_);
    leanh::lean_dec(v_ctorIdx_451_);
    return v_res_455_;
}
pub unsafe fn l_Lake_Glob_one_elim___redArg(
    mut v_t_456_: *mut leanh::LeanObject,
    mut v_one_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Lake_Glob_ctorElim___redArg(v_t_456_, v_one_457_);
    return v___x_458_;
}
pub unsafe fn l_Lake_Glob_one_elim(
    mut v_motive_459_: *mut leanh::LeanObject,
    mut v_t_460_: *mut leanh::LeanObject,
    mut v_h_461_: *mut leanh::LeanObject,
    mut v_one_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = l_Lake_Glob_ctorElim___redArg(v_t_460_, v_one_462_);
    return v___x_463_;
}
pub unsafe fn l_Lake_Glob_submodules_elim___redArg(
    mut v_t_464_: *mut leanh::LeanObject,
    mut v_submodules_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = l_Lake_Glob_ctorElim___redArg(v_t_464_, v_submodules_465_);
    return v___x_466_;
}
pub unsafe fn l_Lake_Glob_submodules_elim(
    mut v_motive_467_: *mut leanh::LeanObject,
    mut v_t_468_: *mut leanh::LeanObject,
    mut v_h_469_: *mut leanh::LeanObject,
    mut v_submodules_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lake_Glob_ctorElim___redArg(v_t_468_, v_submodules_470_);
    return v___x_471_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim___redArg(
    mut v_t_472_: *mut leanh::LeanObject,
    mut v_andSubmodules_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Lake_Glob_ctorElim___redArg(v_t_472_, v_andSubmodules_473_);
    return v___x_474_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim(
    mut v_motive_475_: *mut leanh::LeanObject,
    mut v_t_476_: *mut leanh::LeanObject,
    mut v_h_477_: *mut leanh::LeanObject,
    mut v_andSubmodules_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Lake_Glob_ctorElim___redArg(v_t_476_, v_andSubmodules_478_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = leanh::lean_unsigned_to_nat(2);
    v___x_491_ = lean_nat_to_int(v___x_490_);
    return v___x_491_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = leanh::lean_unsigned_to_nat(1);
    v___x_493_ = lean_nat_to_int(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Lake_instReprGlob_repr(
    mut v_x_506_: *mut leanh::LeanObject,
    mut v_prec_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: u8 = 0;
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_506_) {
                0 => {
                    v_a_508_ = leanh::lean_ctor_get(v_x_506_, 0);
                    leanh::lean_inc(v_a_508_);
                    leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_519_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_520_ = lean_nat_dec_le(v___x_519_, v_prec_507_);
                    if v___x_520_ == 0 {
                        v___x_521_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_510_ = v___x_521_;
                        state = 1;
                        continue;
                    } else {
                        v___x_522_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4_once),
                            _init_l_Lake_instReprGlob_repr___closed__4,
                        );
                        v___y_510_ = v___x_522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_523_ = leanh::lean_ctor_get(v_x_506_, 0);
                    leanh::lean_inc(v_a_523_);
                    leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_534_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_535_ = lean_nat_dec_le(v___x_534_, v_prec_507_);
                    if v___x_535_ == 0 {
                        v___x_536_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_525_ = v___x_536_;
                        state = 2;
                        continue;
                    } else {
                        v___x_537_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4_once),
                            _init_l_Lake_instReprGlob_repr___closed__4,
                        );
                        v___y_525_ = v___x_537_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_a_538_ = leanh::lean_ctor_get(v_x_506_, 0);
                    leanh::lean_inc(v_a_538_);
                    leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_549_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_550_ = lean_nat_dec_le(v___x_549_, v_prec_507_);
                    if v___x_550_ == 0 {
                        v___x_551_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_540_ = v___x_551_;
                        state = 3;
                        continue;
                    } else {
                        v___x_552_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__4_once),
                            _init_l_Lake_instReprGlob_repr___closed__4,
                        );
                        v___y_540_ = v___x_552_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_511_ = l_Lake_instReprGlob_repr___closed__2;
                v___x_512_ = leanh::lean_unsigned_to_nat(1024);
                v___x_513_ = l_Lean_Name_reprPrec(v_a_508_, v___x_512_);
                v___x_514_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_514_, 0, v___x_511_);
                leanh::lean_ctor_set(v___x_514_, 1, v___x_513_);
                leanh::lean_inc(v___y_510_);
                v___x_515_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_515_, 0, v___y_510_);
                leanh::lean_ctor_set(v___x_515_, 1, v___x_514_);
                v___x_516_ = 0;
                v___x_517_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_517_, 0, v___x_515_);
                leanh::lean_ctor_set_uint8(
                    v___x_517_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_516_,
                );
                v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_507_);
                return v___x_518_;
            }
            2 => {
                v___x_526_ = l_Lake_instReprGlob_repr___closed__7;
                v___x_527_ = leanh::lean_unsigned_to_nat(1024);
                v___x_528_ = l_Lean_Name_reprPrec(v_a_523_, v___x_527_);
                v___x_529_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_529_, 0, v___x_526_);
                leanh::lean_ctor_set(v___x_529_, 1, v___x_528_);
                leanh::lean_inc(v___y_525_);
                v___x_530_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_530_, 0, v___y_525_);
                leanh::lean_ctor_set(v___x_530_, 1, v___x_529_);
                v___x_531_ = 0;
                v___x_532_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_532_, 0, v___x_530_);
                leanh::lean_ctor_set_uint8(
                    v___x_532_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_531_,
                );
                v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_507_);
                return v___x_533_;
            }
            3 => {
                v___x_541_ = l_Lake_instReprGlob_repr___closed__10;
                v___x_542_ = leanh::lean_unsigned_to_nat(1024);
                v___x_543_ = l_Lean_Name_reprPrec(v_a_538_, v___x_542_);
                v___x_544_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_544_, 0, v___x_541_);
                leanh::lean_ctor_set(v___x_544_, 1, v___x_543_);
                leanh::lean_inc(v___y_540_);
                v___x_545_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_545_, 0, v___y_540_);
                leanh::lean_ctor_set(v___x_545_, 1, v___x_544_);
                v___x_546_ = 0;
                v___x_547_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_547_, 0, v___x_545_);
                leanh::lean_ctor_set_uint8(
                    v___x_547_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_546_,
                );
                v___x_548_ = l_Repr_addAppParen(v___x_547_, v_prec_507_);
                return v___x_548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprGlob_repr___boxed(
    mut v_x_553_: *mut leanh::LeanObject,
    mut v_prec_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lake_instReprGlob_repr(v_x_553_, v_prec_554_);
    leanh::lean_dec(v_prec_554_);
    return v_res_555_;
}
pub unsafe fn l_Lake_instDecidableEqGlob_decEq(
    mut v_x_558_: *mut leanh::LeanObject,
    mut v_x_559_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_558_) {
        0 => {
            if leanh::lean_obj_tag(v_x_559_) == 0 {
                let mut v_a_560_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_561_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_562_: u8 = 0;
                v_a_560_ = leanh::lean_ctor_get(v_x_558_, 0);
                v_a_561_ = leanh::lean_ctor_get(v_x_559_, 0);
                v___x_562_ = lean_name_eq(v_a_560_, v_a_561_);
                return v___x_562_;
            } else {
                let mut v___x_563_: u8 = 0;
                v___x_563_ = 0;
                return v___x_563_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_559_) == 1 {
                let mut v_a_564_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_565_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v_a_564_ = leanh::lean_ctor_get(v_x_558_, 0);
                v_a_565_ = leanh::lean_ctor_get(v_x_559_, 0);
                v___x_566_ = lean_name_eq(v_a_564_, v_a_565_);
                return v___x_566_;
            } else {
                let mut v___x_567_: u8 = 0;
                v___x_567_ = 0;
                return v___x_567_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_559_) == 2 {
                let mut v_a_568_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_569_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_570_: u8 = 0;
                v_a_568_ = leanh::lean_ctor_get(v_x_558_, 0);
                v_a_569_ = leanh::lean_ctor_get(v_x_559_, 0);
                v___x_570_ = lean_name_eq(v_a_568_, v_a_569_);
                return v___x_570_;
            } else {
                let mut v___x_571_: u8 = 0;
                v___x_571_ = 0;
                return v___x_571_;
            }
        }
    }
}
pub unsafe fn l_Lake_instDecidableEqGlob_decEq___boxed(
    mut v_x_572_: *mut leanh::LeanObject,
    mut v_x_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lake_instDecidableEqGlob_decEq(v_x_572_, v_x_573_);
    leanh::lean_dec_ref(v_x_573_);
    leanh::lean_dec_ref(v_x_572_);
    v_r_575_ = leanh::lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Lake_instDecidableEqGlob(
    mut v_x_576_: *mut leanh::LeanObject,
    mut v_x_577_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_578_: u8 = 0;
    v___x_578_ = l_Lake_instDecidableEqGlob_decEq(v_x_576_, v_x_577_);
    return v___x_578_;
}
pub unsafe fn l_Lake_instDecidableEqGlob___boxed(
    mut v_x_579_: *mut leanh::LeanObject,
    mut v_x_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_581_: u8 = 0;
    let mut v_r_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lake_instDecidableEqGlob(v_x_579_, v_x_580_);
    leanh::lean_dec_ref(v_x_580_);
    leanh::lean_dec_ref(v_x_579_);
    v_r_582_ = leanh::lean_box((v_res_581_) as usize);
    return v_r_582_;
}
pub unsafe fn l_Lake_instCoeNameGlob___lam__0(
    mut v_a_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_584_, 0, v_a_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5;
    v___x_640_ = l_String_toRawSubstring_x27(v___x_639_);
    return v___x_640_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
    mut v_x_670_: *mut leanh::LeanObject,
    mut v_a_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    v___x_673_ = l_Lake_term_____x2e_x2a___closed__2;
    leanh::lean_inc(v_x_670_);
    v___x_674_ = l_Lean_Syntax_isOfKind(v_x_670_, v___x_673_);
    if v___x_674_ == 0 {
        let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_670_);
        v___x_675_ = leanh::lean_box(1);
        v___x_676_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_676_, 0, v___x_675_);
        leanh::lean_ctor_set(v___x_676_, 1, v_a_672_);
        return v___x_676_;
    } else {
        let mut v_quotContext_677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_682_: u8 = 0;
        let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_677_ = leanh::lean_ctor_get(v_a_671_, 1);
        v_currMacroScope_678_ = leanh::lean_ctor_get(v_a_671_, 2);
        v_ref_679_ = leanh::lean_ctor_get(v_a_671_, 5);
        v___x_680_ = leanh::lean_unsigned_to_nat(0);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_670_, v___x_680_);
        leanh::lean_dec(v_x_670_);
        v___x_682_ = 0;
        v___x_683_ = l_Lean_SourceInfo_fromRef(v_ref_679_, v___x_682_);
        v___x_684_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6);
        v___x_686_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9;
        leanh::lean_inc(v_currMacroScope_678_);
        leanh::lean_inc(v_quotContext_677_);
        v___x_687_ = l_Lean_addMacroScope(v_quotContext_677_, v___x_686_, v_currMacroScope_678_);
        v___x_688_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14;
        leanh::lean_inc_n(v___x_683_, 2);
        v___x_689_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_689_, 0, v___x_683_);
        leanh::lean_ctor_set(v___x_689_, 1, v___x_685_);
        leanh::lean_ctor_set(v___x_689_, 2, v___x_687_);
        leanh::lean_ctor_set(v___x_689_, 3, v___x_688_);
        v___x_690_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_691_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_692_ = leanh::lean_unsigned_to_nat(1);
        v___x_693_ = lean_mk_empty_array_with_capacity(v___x_692_);
        v___x_694_ = lean_array_push(v___x_693_, v___x_681_);
        v___x_695_ = leanh::lean_box(2);
        v___x_696_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_696_, 0, v___x_695_);
        leanh::lean_ctor_set(v___x_696_, 1, v___x_691_);
        leanh::lean_ctor_set(v___x_696_, 2, v___x_694_);
        v___x_697_ = l_Lean_Syntax_node1(v___x_683_, v___x_690_, v___x_696_);
        v___x_698_ = l_Lean_Syntax_node2(v___x_683_, v___x_684_, v___x_689_, v___x_697_);
        v___x_699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_699_, 0, v___x_698_);
        leanh::lean_ctor_set(v___x_699_, 1, v_a_672_);
        return v___x_699_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___boxed(
    mut v_x_700_: *mut leanh::LeanObject,
    mut v_a_701_: *mut leanh::LeanObject,
    mut v_a_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
        v_x_700_, v_a_701_, v_a_702_,
    );
    leanh::lean_dec_ref(v_a_701_);
    return v_res_703_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0;
    v___x_722_ = l_String_toRawSubstring_x27(v___x_721_);
    return v___x_722_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
    mut v_x_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
    mut v_a_744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    v___x_745_ = l_Lake_term_____x2e_x2b___closed__1;
    leanh::lean_inc(v_x_742_);
    v___x_746_ = l_Lean_Syntax_isOfKind(v_x_742_, v___x_745_);
    if v___x_746_ == 0 {
        let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_742_);
        v___x_747_ = leanh::lean_box(1);
        v___x_748_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_748_, 0, v___x_747_);
        leanh::lean_ctor_set(v___x_748_, 1, v_a_744_);
        return v___x_748_;
    } else {
        let mut v_quotContext_749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: u8 = 0;
        let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_749_ = leanh::lean_ctor_get(v_a_743_, 1);
        v_currMacroScope_750_ = leanh::lean_ctor_get(v_a_743_, 2);
        v_ref_751_ = leanh::lean_ctor_get(v_a_743_, 5);
        v___x_752_ = leanh::lean_unsigned_to_nat(0);
        v___x_753_ = l_Lean_Syntax_getArg(v_x_742_, v___x_752_);
        leanh::lean_dec(v_x_742_);
        v___x_754_ = 0;
        v___x_755_ = l_Lean_SourceInfo_fromRef(v_ref_751_, v___x_754_);
        v___x_756_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1);
        v___x_758_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3;
        leanh::lean_inc(v_currMacroScope_750_);
        leanh::lean_inc(v_quotContext_749_);
        v___x_759_ = l_Lean_addMacroScope(v_quotContext_749_, v___x_758_, v_currMacroScope_750_);
        v___x_760_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8;
        leanh::lean_inc_n(v___x_755_, 2);
        v___x_761_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_761_, 0, v___x_755_);
        leanh::lean_ctor_set(v___x_761_, 1, v___x_757_);
        leanh::lean_ctor_set(v___x_761_, 2, v___x_759_);
        leanh::lean_ctor_set(v___x_761_, 3, v___x_760_);
        v___x_762_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_763_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_764_ = leanh::lean_unsigned_to_nat(1);
        v___x_765_ = lean_mk_empty_array_with_capacity(v___x_764_);
        v___x_766_ = lean_array_push(v___x_765_, v___x_753_);
        v___x_767_ = leanh::lean_box(2);
        v___x_768_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_768_, 0, v___x_767_);
        leanh::lean_ctor_set(v___x_768_, 1, v___x_763_);
        leanh::lean_ctor_set(v___x_768_, 2, v___x_766_);
        v___x_769_ = l_Lean_Syntax_node1(v___x_755_, v___x_762_, v___x_768_);
        v___x_770_ = l_Lean_Syntax_node2(v___x_755_, v___x_756_, v___x_761_, v___x_769_);
        v___x_771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_771_, 0, v___x_770_);
        leanh::lean_ctor_set(v___x_771_, 1, v_a_744_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___boxed(
    mut v_x_772_: *mut leanh::LeanObject,
    mut v_a_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
        v_x_772_, v_a_773_, v_a_774_,
    );
    leanh::lean_dec_ref(v_a_773_);
    return v_res_775_;
}
pub unsafe fn l_Lake_Glob_toString(
    mut v_x_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_776_) {
        0 => {
            let mut v_a_777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: u8 = 0;
            let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_777_ = leanh::lean_ctor_get(v_x_776_, 0);
            leanh::lean_inc(v_a_777_);
            leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_778_ = 1;
            v___x_779_ = l_Lean_Name_toString(v_a_777_, v___x_778_);
            return v___x_779_;
        }
        1 => {
            let mut v_a_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: u8 = 0;
            let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_780_ = leanh::lean_ctor_get(v_x_776_, 0);
            leanh::lean_inc(v_a_780_);
            leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_781_ = 1;
            v___x_782_ = l_Lean_Name_toString(v_a_780_, v___x_781_);
            v___x_783_ = l_Lake_term_____x2e_x2b___closed__2;
            v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
            return v___x_784_;
        }
        _ => {
            let mut v_a_785_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: u8 = 0;
            let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_785_ = leanh::lean_ctor_get(v_x_776_, 0);
            leanh::lean_inc(v_a_785_);
            leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_786_ = 1;
            v___x_787_ = l_Lean_Name_toString(v_a_785_, v___x_786_);
            v___x_788_ = l_Lake_term_____x2e_x2a___closed__15;
            v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
            return v___x_789_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches(
    mut v_m_792_: *mut leanh::LeanObject,
    mut v_x_793_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_793_) {
        0 => {
            let mut v_a_794_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v_a_794_ = leanh::lean_ctor_get(v_x_793_, 0);
            v___x_795_ = lean_name_eq(v_a_794_, v_m_792_);
            return v___x_795_;
        }
        1 => {
            let mut v_a_796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_a_796_ = leanh::lean_ctor_get(v_x_793_, 0);
            v___x_797_ = l_Lean_Name_isPrefixOf(v_a_796_, v_m_792_);
            if v___x_797_ == 0 {
                return v___x_797_;
            } else {
                let mut v___x_798_: u8 = 0;
                v___x_798_ = lean_name_eq(v_a_796_, v_m_792_);
                if v___x_798_ == 0 {
                    return v___x_797_;
                } else {
                    let mut v___x_799_: u8 = 0;
                    v___x_799_ = 0;
                    return v___x_799_;
                }
            }
        }
        _ => {
            let mut v_a_800_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            v_a_800_ = leanh::lean_ctor_get(v_x_793_, 0);
            v___x_801_ = l_Lean_Name_isPrefixOf(v_a_800_, v_m_792_);
            return v___x_801_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches___boxed(
    mut v_m_802_: *mut leanh::LeanObject,
    mut v_x_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_804_: u8 = 0;
    let mut v_r_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_Glob_matches(v_m_802_, v_x_803_);
    leanh::lean_dec_ref(v_x_803_);
    leanh::lean_dec(v_m_802_);
    v_r_805_ = leanh::lean_box((v_res_804_) as usize);
    return v_r_805_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__0(
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_f_807_: *mut leanh::LeanObject,
    mut v_x_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lean_Name_append(v_a_806_, v_x_808_);
    v___x_810_ = leanh::lean_apply_1(v_f_807_, v___x_809_);
    return v___x_810_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2(
    mut v_dir_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_inst_814_: *mut leanh::LeanObject,
    mut v_inst_815_: *mut leanh::LeanObject,
    mut v___f_816_: *mut leanh::LeanObject,
    mut v_x_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
    v___x_819_ = l_Lean_modToFilePath(v_dir_812_, v_a_813_, v___x_818_);
    v___x_820_ =
        l_Lean_forEachModuleInDir___redArg(v_inst_814_, v_inst_815_, v___x_819_, v___f_816_);
    return v___x_820_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(
    mut v_dir_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_inst_823_: *mut leanh::LeanObject,
    mut v_inst_824_: *mut leanh::LeanObject,
    mut v___f_825_: *mut leanh::LeanObject,
    mut v_x_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2(
        v_dir_821_,
        v_a_822_,
        v_inst_823_,
        v_inst_824_,
        v___f_825_,
        v_x_826_,
    );
    leanh::lean_dec_ref(v_dir_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg(
    mut v_inst_828_: *mut leanh::LeanObject,
    mut v_inst_829_: *mut leanh::LeanObject,
    mut v_dir_830_: *mut leanh::LeanObject,
    mut v_f_831_: *mut leanh::LeanObject,
    mut v_x_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_832_) {
        0 => {
            let mut v_a_833_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_dir_830_);
            leanh::lean_dec(v_inst_829_);
            leanh::lean_dec_ref(v_inst_828_);
            v_a_833_ = leanh::lean_ctor_get(v_x_832_, 0);
            leanh::lean_inc(v_a_833_);
            leanh::lean_dec_ref_known(v_x_832_, 1);
            v___x_834_ = leanh::lean_apply_1(v_f_831_, v_a_833_);
            return v___x_834_;
        }
        1 => {
            let mut v_a_835_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_836_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_835_ = leanh::lean_ctor_get(v_x_832_, 0);
            leanh::lean_inc_n(v_a_835_, 2);
            leanh::lean_dec_ref_known(v_x_832_, 1);
            v___f_836_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_836_, 0, v_a_835_);
            leanh::lean_closure_set(v___f_836_, 1, v_f_831_);
            v___x_837_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_838_ = l_Lean_modToFilePath(v_dir_830_, v_a_835_, v___x_837_);
            leanh::lean_dec_ref(v_dir_830_);
            v___x_839_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_828_,
                v_inst_829_,
                v___x_838_,
                v___f_836_,
            );
            return v___x_839_;
        }
        _ => {
            let mut v_toApplicative_840_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_841_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_842_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_843_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_844_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_840_ = leanh::lean_ctor_get(v_inst_828_, 0);
            v_toSeqRight_841_ = leanh::lean_ctor_get(v_toApplicative_840_, 4);
            leanh::lean_inc(v_toSeqRight_841_);
            v_a_842_ = leanh::lean_ctor_get(v_x_832_, 0);
            leanh::lean_inc_n(v_a_842_, 3);
            leanh::lean_dec_ref_known(v_x_832_, 1);
            leanh::lean_inc(v_f_831_);
            v___f_843_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_843_, 0, v_a_842_);
            leanh::lean_closure_set(v___f_843_, 1, v_f_831_);
            v___f_844_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            leanh::lean_closure_set(v___f_844_, 0, v_dir_830_);
            leanh::lean_closure_set(v___f_844_, 1, v_a_842_);
            leanh::lean_closure_set(v___f_844_, 2, v_inst_828_);
            leanh::lean_closure_set(v___f_844_, 3, v_inst_829_);
            leanh::lean_closure_set(v___f_844_, 4, v___f_843_);
            v___x_845_ = leanh::lean_apply_1(v_f_831_, v_a_842_);
            v___x_846_ = leanh::lean_apply_4(
                v_toSeqRight_841_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_845_,
                v___f_844_,
            );
            return v___x_846_;
        }
    }
}
pub unsafe fn l_Lake_Glob_forEachModuleIn(
    mut v_m_847_: *mut leanh::LeanObject,
    mut v_inst_848_: *mut leanh::LeanObject,
    mut v_inst_849_: *mut leanh::LeanObject,
    mut v_dir_850_: *mut leanh::LeanObject,
    mut v_f_851_: *mut leanh::LeanObject,
    mut v_x_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_852_) {
        0 => {
            let mut v_a_853_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_dir_850_);
            leanh::lean_dec(v_inst_849_);
            leanh::lean_dec_ref(v_inst_848_);
            v_a_853_ = leanh::lean_ctor_get(v_x_852_, 0);
            leanh::lean_inc(v_a_853_);
            leanh::lean_dec_ref_known(v_x_852_, 1);
            v___x_854_ = leanh::lean_apply_1(v_f_851_, v_a_853_);
            return v___x_854_;
        }
        1 => {
            let mut v_a_855_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_856_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_855_ = leanh::lean_ctor_get(v_x_852_, 0);
            leanh::lean_inc_n(v_a_855_, 2);
            leanh::lean_dec_ref_known(v_x_852_, 1);
            v___f_856_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_856_, 0, v_a_855_);
            leanh::lean_closure_set(v___f_856_, 1, v_f_851_);
            v___x_857_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_858_ = l_Lean_modToFilePath(v_dir_850_, v_a_855_, v___x_857_);
            leanh::lean_dec_ref(v_dir_850_);
            v___x_859_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_848_,
                v_inst_849_,
                v___x_858_,
                v___f_856_,
            );
            return v___x_859_;
        }
        _ => {
            let mut v_toApplicative_860_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_860_ = leanh::lean_ctor_get(v_inst_848_, 0);
            v_toSeqRight_861_ = leanh::lean_ctor_get(v_toApplicative_860_, 4);
            leanh::lean_inc(v_toSeqRight_861_);
            v_a_862_ = leanh::lean_ctor_get(v_x_852_, 0);
            leanh::lean_inc_n(v_a_862_, 3);
            leanh::lean_dec_ref_known(v_x_852_, 1);
            leanh::lean_inc(v_f_851_);
            v___f_863_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_863_, 0, v_a_862_);
            leanh::lean_closure_set(v___f_863_, 1, v_f_851_);
            v___f_864_ = leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            leanh::lean_closure_set(v___f_864_, 0, v_dir_850_);
            leanh::lean_closure_set(v___f_864_, 1, v_a_862_);
            leanh::lean_closure_set(v___f_864_, 2, v_inst_848_);
            leanh::lean_closure_set(v___f_864_, 3, v_inst_849_);
            leanh::lean_closure_set(v___f_864_, 4, v___f_863_);
            v___x_865_ = leanh::lean_apply_1(v_f_851_, v_a_862_);
            v___x_866_ = leanh::lean_apply_4(
                v_toSeqRight_861_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_865_,
                v___f_864_,
            );
            return v___x_866_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Glob(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Path(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Glob(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Glob(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Path(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Glob(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Glob(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Glob(builtin);
}
// Lean compiler output
// Module: Lake.Config.Glob
// Imports: Lean.Util.Path Init.Data.ToString.Name Lean.Data.Name
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
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_le,
};
pub static l_Lake_instInhabitedGlob_default___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instInhabitedGlob_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedGlob_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedGlob: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instReprGlob_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprGlob_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprGlob_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprGlob_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprGlob_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprGlob_repr___closed__5_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instReprGlob_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__8_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100,
            117, 108, 101, 115, 0,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob_repr___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprGlob_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprGlob___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprGlob_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprGlob___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprGlob: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeNameGlob___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeNameGlob___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeNameGlob___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeNameGlob: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeGlobArray___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_singleton as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instCoeGlobArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeGlobArray: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 101, 114, 109, 95, 95, 46, 42, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lake_term_____x2e_x2a___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_term_____x2e_x2a___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value)
                as *mut crate::leanh::LeanObject,
            10150953148658318397 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_term_____x2e_x2a___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value)
                as *mut crate::leanh::LeanObject,
            5949480926448383572 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__8_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__10_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_term_____x2e_x2a___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1581446985683836252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__15_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [46, 42, 0],
    };
static mut l_Lake_term_____x2e_x2a___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__16_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2a___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_term_____x2e_x2a: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [71, 108, 111, 98, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject,9097109829436277786 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject,2906245839412892126 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject,12140512885907428830 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject,1477412787864469706 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut crate::leanh::LeanObject,9368229134555052249 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 101, 114, 109, 95, 95, 46, 43, 0],
    };
static mut l_Lake_term_____x2e_x2b___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_term_____x2e_x2b___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_term_____x2e_x2b___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11289494576251685396 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [46, 43, 0],
    };
static mut l_Lake_term_____x2e_x2b___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term_____x2e_x2b___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_term_____x2e_x2b: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [71, 108, 111, 98, 46, 115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject,9097109829436277786 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut crate::leanh::LeanObject,15076241754705399326 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject,12140512885907428830 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut crate::leanh::LeanObject,11186284017425669258 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Glob_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Glob_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Glob_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Glob_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_Glob_ctorIdx(
    mut v_x_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_434_) {
        0 => {
            let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_435_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_435_;
        }
        1 => {
            let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_436_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_436_;
        }
        _ => {
            let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_437_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_437_;
        }
    }
}
pub unsafe fn l_Lake_Glob_ctorIdx___boxed(
    mut v_x_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lake_Glob_ctorIdx(v_x_438_);
    crate::leanh::lean_dec_ref(v_x_438_);
    return v_res_439_;
}
pub unsafe fn l_Lake_Glob_ctorElim___redArg(
    mut v_t_440_: *mut crate::leanh::LeanObject,
    mut v_k_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_442_ = crate::leanh::lean_ctor_get(v_t_440_, 0);
    crate::leanh::lean_inc(v_a_442_);
    crate::leanh::lean_dec_ref(v_t_440_);
    v___x_443_ = crate::leanh::lean_apply_1(v_k_441_, v_a_442_);
    return v___x_443_;
}
pub unsafe fn l_Lake_Glob_ctorElim(
    mut v_motive_444_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_445_: *mut crate::leanh::LeanObject,
    mut v_t_446_: *mut crate::leanh::LeanObject,
    mut v_h_447_: *mut crate::leanh::LeanObject,
    mut v_k_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lake_Glob_ctorElim___redArg(v_t_446_, v_k_448_);
    return v___x_449_;
}
pub unsafe fn l_Lake_Glob_ctorElim___boxed(
    mut v_motive_450_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_451_: *mut crate::leanh::LeanObject,
    mut v_t_452_: *mut crate::leanh::LeanObject,
    mut v_h_453_: *mut crate::leanh::LeanObject,
    mut v_k_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Lake_Glob_ctorElim(v_motive_450_, v_ctorIdx_451_, v_t_452_, v_h_453_, v_k_454_);
    crate::leanh::lean_dec(v_ctorIdx_451_);
    return v_res_455_;
}
pub unsafe fn l_Lake_Glob_one_elim___redArg(
    mut v_t_456_: *mut crate::leanh::LeanObject,
    mut v_one_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Lake_Glob_ctorElim___redArg(v_t_456_, v_one_457_);
    return v___x_458_;
}
pub unsafe fn l_Lake_Glob_one_elim(
    mut v_motive_459_: *mut crate::leanh::LeanObject,
    mut v_t_460_: *mut crate::leanh::LeanObject,
    mut v_h_461_: *mut crate::leanh::LeanObject,
    mut v_one_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = l_Lake_Glob_ctorElim___redArg(v_t_460_, v_one_462_);
    return v___x_463_;
}
pub unsafe fn l_Lake_Glob_submodules_elim___redArg(
    mut v_t_464_: *mut crate::leanh::LeanObject,
    mut v_submodules_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = l_Lake_Glob_ctorElim___redArg(v_t_464_, v_submodules_465_);
    return v___x_466_;
}
pub unsafe fn l_Lake_Glob_submodules_elim(
    mut v_motive_467_: *mut crate::leanh::LeanObject,
    mut v_t_468_: *mut crate::leanh::LeanObject,
    mut v_h_469_: *mut crate::leanh::LeanObject,
    mut v_submodules_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lake_Glob_ctorElim___redArg(v_t_468_, v_submodules_470_);
    return v___x_471_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim___redArg(
    mut v_t_472_: *mut crate::leanh::LeanObject,
    mut v_andSubmodules_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Lake_Glob_ctorElim___redArg(v_t_472_, v_andSubmodules_473_);
    return v___x_474_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim(
    mut v_motive_475_: *mut crate::leanh::LeanObject,
    mut v_t_476_: *mut crate::leanh::LeanObject,
    mut v_h_477_: *mut crate::leanh::LeanObject,
    mut v_andSubmodules_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Lake_Glob_ctorElim___redArg(v_t_476_, v_andSubmodules_478_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_491_ = lean_nat_to_int(v___x_490_);
    return v___x_491_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_493_ = lean_nat_to_int(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Lake_instReprGlob_repr(
    mut v_x_506_: *mut crate::leanh::LeanObject,
    mut v_prec_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: u8 = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_506_) {
                0 => {
                    v_a_508_ = crate::leanh::lean_ctor_get(v_x_506_, 0);
                    crate::leanh::lean_inc(v_a_508_);
                    crate::leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_519_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_520_ = lean_nat_dec_le(v___x_519_, v_prec_507_);
                    if v___x_520_ == 0 {
                        v___x_521_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_510_ = v___x_521_;
                        state = 1;
                        continue;
                    } else {
                        v___x_522_ = crate::leanh::lean_obj_once(
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
                    v_a_523_ = crate::leanh::lean_ctor_get(v_x_506_, 0);
                    crate::leanh::lean_inc(v_a_523_);
                    crate::leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_534_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_535_ = lean_nat_dec_le(v___x_534_, v_prec_507_);
                    if v___x_535_ == 0 {
                        v___x_536_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_525_ = v___x_536_;
                        state = 2;
                        continue;
                    } else {
                        v___x_537_ = crate::leanh::lean_obj_once(
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
                    v_a_538_ = crate::leanh::lean_ctor_get(v_x_506_, 0);
                    crate::leanh::lean_inc(v_a_538_);
                    crate::leanh::lean_dec_ref_known(v_x_506_, 1);
                    v___x_549_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_550_ = lean_nat_dec_le(v___x_549_, v_prec_507_);
                    if v___x_550_ == 0 {
                        v___x_551_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_540_ = v___x_551_;
                        state = 3;
                        continue;
                    } else {
                        v___x_552_ = crate::leanh::lean_obj_once(
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
                v___x_512_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_513_ = l_Lean_Name_reprPrec(v_a_508_, v___x_512_);
                v___x_514_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_514_, 0, v___x_511_);
                crate::leanh::lean_ctor_set(v___x_514_, 1, v___x_513_);
                crate::leanh::lean_inc(v___y_510_);
                v___x_515_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_515_, 0, v___y_510_);
                crate::leanh::lean_ctor_set(v___x_515_, 1, v___x_514_);
                v___x_516_ = 0;
                v___x_517_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_517_, 0, v___x_515_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_517_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_516_,
                );
                v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_507_);
                return v___x_518_;
            }
            2 => {
                v___x_526_ = l_Lake_instReprGlob_repr___closed__7;
                v___x_527_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_528_ = l_Lean_Name_reprPrec(v_a_523_, v___x_527_);
                v___x_529_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_529_, 0, v___x_526_);
                crate::leanh::lean_ctor_set(v___x_529_, 1, v___x_528_);
                crate::leanh::lean_inc(v___y_525_);
                v___x_530_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_530_, 0, v___y_525_);
                crate::leanh::lean_ctor_set(v___x_530_, 1, v___x_529_);
                v___x_531_ = 0;
                v___x_532_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_530_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_532_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_531_,
                );
                v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_507_);
                return v___x_533_;
            }
            3 => {
                v___x_541_ = l_Lake_instReprGlob_repr___closed__10;
                v___x_542_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_543_ = l_Lean_Name_reprPrec(v_a_538_, v___x_542_);
                v___x_544_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_544_, 0, v___x_541_);
                crate::leanh::lean_ctor_set(v___x_544_, 1, v___x_543_);
                crate::leanh::lean_inc(v___y_540_);
                v___x_545_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_545_, 0, v___y_540_);
                crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_544_);
                v___x_546_ = 0;
                v___x_547_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_547_, 0, v___x_545_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_553_: *mut crate::leanh::LeanObject,
    mut v_prec_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lake_instReprGlob_repr(v_x_553_, v_prec_554_);
    crate::leanh::lean_dec(v_prec_554_);
    return v_res_555_;
}
pub unsafe fn l_Lake_instDecidableEqGlob_decEq(
    mut v_x_558_: *mut crate::leanh::LeanObject,
    mut v_x_559_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_558_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_559_) == 0 {
                let mut v_a_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_562_: u8 = 0;
                v_a_560_ = crate::leanh::lean_ctor_get(v_x_558_, 0);
                v_a_561_ = crate::leanh::lean_ctor_get(v_x_559_, 0);
                v___x_562_ = lean_name_eq(v_a_560_, v_a_561_);
                return v___x_562_;
            } else {
                let mut v___x_563_: u8 = 0;
                v___x_563_ = 0;
                return v___x_563_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_559_) == 1 {
                let mut v_a_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v_a_564_ = crate::leanh::lean_ctor_get(v_x_558_, 0);
                v_a_565_ = crate::leanh::lean_ctor_get(v_x_559_, 0);
                v___x_566_ = lean_name_eq(v_a_564_, v_a_565_);
                return v___x_566_;
            } else {
                let mut v___x_567_: u8 = 0;
                v___x_567_ = 0;
                return v___x_567_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_559_) == 2 {
                let mut v_a_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_570_: u8 = 0;
                v_a_568_ = crate::leanh::lean_ctor_get(v_x_558_, 0);
                v_a_569_ = crate::leanh::lean_ctor_get(v_x_559_, 0);
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
    mut v_x_572_: *mut crate::leanh::LeanObject,
    mut v_x_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lake_instDecidableEqGlob_decEq(v_x_572_, v_x_573_);
    crate::leanh::lean_dec_ref(v_x_573_);
    crate::leanh::lean_dec_ref(v_x_572_);
    v_r_575_ = crate::leanh::lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Lake_instDecidableEqGlob(
    mut v_x_576_: *mut crate::leanh::LeanObject,
    mut v_x_577_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_578_: u8 = 0;
    v___x_578_ = l_Lake_instDecidableEqGlob_decEq(v_x_576_, v_x_577_);
    return v___x_578_;
}
pub unsafe fn l_Lake_instDecidableEqGlob___boxed(
    mut v_x_579_: *mut crate::leanh::LeanObject,
    mut v_x_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_581_: u8 = 0;
    let mut v_r_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lake_instDecidableEqGlob(v_x_579_, v_x_580_);
    crate::leanh::lean_dec_ref(v_x_580_);
    crate::leanh::lean_dec_ref(v_x_579_);
    v_r_582_ = crate::leanh::lean_box((v_res_581_) as usize);
    return v_r_582_;
}
pub unsafe fn l_Lake_instCoeNameGlob___lam__0(
    mut v_a_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_584_, 0, v_a_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5;
    v___x_640_ = l_String_toRawSubstring_x27(v___x_639_);
    return v___x_640_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
    mut v_x_670_: *mut crate::leanh::LeanObject,
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_a_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    v___x_673_ = l_Lake_term_____x2e_x2a___closed__2;
    crate::leanh::lean_inc(v_x_670_);
    v___x_674_ = l_Lean_Syntax_isOfKind(v_x_670_, v___x_673_);
    if v___x_674_ == 0 {
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_670_);
        v___x_675_ = crate::leanh::lean_box(1);
        v___x_676_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_675_);
        crate::leanh::lean_ctor_set(v___x_676_, 1, v_a_672_);
        return v___x_676_;
    } else {
        let mut v_quotContext_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_682_: u8 = 0;
        let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_677_ = crate::leanh::lean_ctor_get(v_a_671_, 1);
        v_currMacroScope_678_ = crate::leanh::lean_ctor_get(v_a_671_, 2);
        v_ref_679_ = crate::leanh::lean_ctor_get(v_a_671_, 5);
        v___x_680_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_670_, v___x_680_);
        crate::leanh::lean_dec(v_x_670_);
        v___x_682_ = 0;
        v___x_683_ = l_Lean_SourceInfo_fromRef(v_ref_679_, v___x_682_);
        v___x_684_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_685_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6);
        v___x_686_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9;
        crate::leanh::lean_inc(v_currMacroScope_678_);
        crate::leanh::lean_inc(v_quotContext_677_);
        v___x_687_ = l_Lean_addMacroScope(v_quotContext_677_, v___x_686_, v_currMacroScope_678_);
        v___x_688_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14;
        crate::leanh::lean_inc_n(v___x_683_, 2);
        v___x_689_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_683_);
        crate::leanh::lean_ctor_set(v___x_689_, 1, v___x_685_);
        crate::leanh::lean_ctor_set(v___x_689_, 2, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_689_, 3, v___x_688_);
        v___x_690_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_691_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_692_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_693_ = lean_mk_empty_array_with_capacity(v___x_692_);
        v___x_694_ = lean_array_push(v___x_693_, v___x_681_);
        v___x_695_ = crate::leanh::lean_box(2);
        v___x_696_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_696_, 0, v___x_695_);
        crate::leanh::lean_ctor_set(v___x_696_, 1, v___x_691_);
        crate::leanh::lean_ctor_set(v___x_696_, 2, v___x_694_);
        v___x_697_ = l_Lean_Syntax_node1(v___x_683_, v___x_690_, v___x_696_);
        v___x_698_ = l_Lean_Syntax_node2(v___x_683_, v___x_684_, v___x_689_, v___x_697_);
        v___x_699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_699_, 0, v___x_698_);
        crate::leanh::lean_ctor_set(v___x_699_, 1, v_a_672_);
        return v___x_699_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___boxed(
    mut v_x_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
        v_x_700_, v_a_701_, v_a_702_,
    );
    crate::leanh::lean_dec_ref(v_a_701_);
    return v_res_703_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0;
    v___x_722_ = l_String_toRawSubstring_x27(v___x_721_);
    return v___x_722_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
    mut v_x_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    v___x_745_ = l_Lake_term_____x2e_x2b___closed__1;
    crate::leanh::lean_inc(v_x_742_);
    v___x_746_ = l_Lean_Syntax_isOfKind(v_x_742_, v___x_745_);
    if v___x_746_ == 0 {
        let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_742_);
        v___x_747_ = crate::leanh::lean_box(1);
        v___x_748_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_748_, 0, v___x_747_);
        crate::leanh::lean_ctor_set(v___x_748_, 1, v_a_744_);
        return v___x_748_;
    } else {
        let mut v_quotContext_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: u8 = 0;
        let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_749_ = crate::leanh::lean_ctor_get(v_a_743_, 1);
        v_currMacroScope_750_ = crate::leanh::lean_ctor_get(v_a_743_, 2);
        v_ref_751_ = crate::leanh::lean_ctor_get(v_a_743_, 5);
        v___x_752_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_753_ = l_Lean_Syntax_getArg(v_x_742_, v___x_752_);
        crate::leanh::lean_dec(v_x_742_);
        v___x_754_ = 0;
        v___x_755_ = l_Lean_SourceInfo_fromRef(v_ref_751_, v___x_754_);
        v___x_756_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1);
        v___x_758_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_750_);
        crate::leanh::lean_inc(v_quotContext_749_);
        v___x_759_ = l_Lean_addMacroScope(v_quotContext_749_, v___x_758_, v_currMacroScope_750_);
        v___x_760_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8;
        crate::leanh::lean_inc_n(v___x_755_, 2);
        v___x_761_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_755_);
        crate::leanh::lean_ctor_set(v___x_761_, 1, v___x_757_);
        crate::leanh::lean_ctor_set(v___x_761_, 2, v___x_759_);
        crate::leanh::lean_ctor_set(v___x_761_, 3, v___x_760_);
        v___x_762_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_763_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_764_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_765_ = lean_mk_empty_array_with_capacity(v___x_764_);
        v___x_766_ = lean_array_push(v___x_765_, v___x_753_);
        v___x_767_ = crate::leanh::lean_box(2);
        v___x_768_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_767_);
        crate::leanh::lean_ctor_set(v___x_768_, 1, v___x_763_);
        crate::leanh::lean_ctor_set(v___x_768_, 2, v___x_766_);
        v___x_769_ = l_Lean_Syntax_node1(v___x_755_, v___x_762_, v___x_768_);
        v___x_770_ = l_Lean_Syntax_node2(v___x_755_, v___x_756_, v___x_761_, v___x_769_);
        v___x_771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_771_, 0, v___x_770_);
        crate::leanh::lean_ctor_set(v___x_771_, 1, v_a_744_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___boxed(
    mut v_x_772_: *mut crate::leanh::LeanObject,
    mut v_a_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
        v_x_772_, v_a_773_, v_a_774_,
    );
    crate::leanh::lean_dec_ref(v_a_773_);
    return v_res_775_;
}
pub unsafe fn l_Lake_Glob_toString(
    mut v_x_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_776_) {
        0 => {
            let mut v_a_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: u8 = 0;
            let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_777_ = crate::leanh::lean_ctor_get(v_x_776_, 0);
            crate::leanh::lean_inc(v_a_777_);
            crate::leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_778_ = 1;
            v___x_779_ = l_Lean_Name_toString(v_a_777_, v___x_778_);
            return v___x_779_;
        }
        1 => {
            let mut v_a_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: u8 = 0;
            let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_780_ = crate::leanh::lean_ctor_get(v_x_776_, 0);
            crate::leanh::lean_inc(v_a_780_);
            crate::leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_781_ = 1;
            v___x_782_ = l_Lean_Name_toString(v_a_780_, v___x_781_);
            v___x_783_ = l_Lake_term_____x2e_x2b___closed__2;
            v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
            return v___x_784_;
        }
        _ => {
            let mut v_a_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: u8 = 0;
            let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_785_ = crate::leanh::lean_ctor_get(v_x_776_, 0);
            crate::leanh::lean_inc(v_a_785_);
            crate::leanh::lean_dec_ref_known(v_x_776_, 1);
            v___x_786_ = 1;
            v___x_787_ = l_Lean_Name_toString(v_a_785_, v___x_786_);
            v___x_788_ = l_Lake_term_____x2e_x2a___closed__15;
            v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
            return v___x_789_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches(
    mut v_m_792_: *mut crate::leanh::LeanObject,
    mut v_x_793_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_793_) {
        0 => {
            let mut v_a_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v_a_794_ = crate::leanh::lean_ctor_get(v_x_793_, 0);
            v___x_795_ = lean_name_eq(v_a_794_, v_m_792_);
            return v___x_795_;
        }
        1 => {
            let mut v_a_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_a_796_ = crate::leanh::lean_ctor_get(v_x_793_, 0);
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
            let mut v_a_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            v_a_800_ = crate::leanh::lean_ctor_get(v_x_793_, 0);
            v___x_801_ = l_Lean_Name_isPrefixOf(v_a_800_, v_m_792_);
            return v___x_801_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches___boxed(
    mut v_m_802_: *mut crate::leanh::LeanObject,
    mut v_x_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_804_: u8 = 0;
    let mut v_r_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_Glob_matches(v_m_802_, v_x_803_);
    crate::leanh::lean_dec_ref(v_x_803_);
    crate::leanh::lean_dec(v_m_802_);
    v_r_805_ = crate::leanh::lean_box((v_res_804_) as usize);
    return v_r_805_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__0(
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_f_807_: *mut crate::leanh::LeanObject,
    mut v_x_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lean_Name_append(v_a_806_, v_x_808_);
    v___x_810_ = crate::leanh::lean_apply_1(v_f_807_, v___x_809_);
    return v___x_810_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2(
    mut v_dir_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_inst_814_: *mut crate::leanh::LeanObject,
    mut v_inst_815_: *mut crate::leanh::LeanObject,
    mut v___f_816_: *mut crate::leanh::LeanObject,
    mut v_x_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
    v___x_819_ = l_Lean_modToFilePath(v_dir_812_, v_a_813_, v___x_818_);
    v___x_820_ =
        l_Lean_forEachModuleInDir___redArg(v_inst_814_, v_inst_815_, v___x_819_, v___f_816_);
    return v___x_820_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(
    mut v_dir_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_inst_823_: *mut crate::leanh::LeanObject,
    mut v_inst_824_: *mut crate::leanh::LeanObject,
    mut v___f_825_: *mut crate::leanh::LeanObject,
    mut v_x_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2(
        v_dir_821_,
        v_a_822_,
        v_inst_823_,
        v_inst_824_,
        v___f_825_,
        v_x_826_,
    );
    crate::leanh::lean_dec_ref(v_dir_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg(
    mut v_inst_828_: *mut crate::leanh::LeanObject,
    mut v_inst_829_: *mut crate::leanh::LeanObject,
    mut v_dir_830_: *mut crate::leanh::LeanObject,
    mut v_f_831_: *mut crate::leanh::LeanObject,
    mut v_x_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_832_) {
        0 => {
            let mut v_a_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_dir_830_);
            crate::leanh::lean_dec(v_inst_829_);
            crate::leanh::lean_dec_ref(v_inst_828_);
            v_a_833_ = crate::leanh::lean_ctor_get(v_x_832_, 0);
            crate::leanh::lean_inc(v_a_833_);
            crate::leanh::lean_dec_ref_known(v_x_832_, 1);
            v___x_834_ = crate::leanh::lean_apply_1(v_f_831_, v_a_833_);
            return v___x_834_;
        }
        1 => {
            let mut v_a_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_835_ = crate::leanh::lean_ctor_get(v_x_832_, 0);
            crate::leanh::lean_inc_n(v_a_835_, 2);
            crate::leanh::lean_dec_ref_known(v_x_832_, 1);
            v___f_836_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_836_, 0, v_a_835_);
            crate::leanh::lean_closure_set(v___f_836_, 1, v_f_831_);
            v___x_837_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_838_ = l_Lean_modToFilePath(v_dir_830_, v_a_835_, v___x_837_);
            crate::leanh::lean_dec_ref(v_dir_830_);
            v___x_839_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_828_,
                v_inst_829_,
                v___x_838_,
                v___f_836_,
            );
            return v___x_839_;
        }
        _ => {
            let mut v_toApplicative_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_840_ = crate::leanh::lean_ctor_get(v_inst_828_, 0);
            v_toSeqRight_841_ = crate::leanh::lean_ctor_get(v_toApplicative_840_, 4);
            crate::leanh::lean_inc(v_toSeqRight_841_);
            v_a_842_ = crate::leanh::lean_ctor_get(v_x_832_, 0);
            crate::leanh::lean_inc_n(v_a_842_, 3);
            crate::leanh::lean_dec_ref_known(v_x_832_, 1);
            crate::leanh::lean_inc(v_f_831_);
            v___f_843_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_843_, 0, v_a_842_);
            crate::leanh::lean_closure_set(v___f_843_, 1, v_f_831_);
            v___f_844_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_844_, 0, v_dir_830_);
            crate::leanh::lean_closure_set(v___f_844_, 1, v_a_842_);
            crate::leanh::lean_closure_set(v___f_844_, 2, v_inst_828_);
            crate::leanh::lean_closure_set(v___f_844_, 3, v_inst_829_);
            crate::leanh::lean_closure_set(v___f_844_, 4, v___f_843_);
            v___x_845_ = crate::leanh::lean_apply_1(v_f_831_, v_a_842_);
            v___x_846_ = crate::leanh::lean_apply_4(
                v_toSeqRight_841_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_845_,
                v___f_844_,
            );
            return v___x_846_;
        }
    }
}
pub unsafe fn l_Lake_Glob_forEachModuleIn(
    mut v_m_847_: *mut crate::leanh::LeanObject,
    mut v_inst_848_: *mut crate::leanh::LeanObject,
    mut v_inst_849_: *mut crate::leanh::LeanObject,
    mut v_dir_850_: *mut crate::leanh::LeanObject,
    mut v_f_851_: *mut crate::leanh::LeanObject,
    mut v_x_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_852_) {
        0 => {
            let mut v_a_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_dir_850_);
            crate::leanh::lean_dec(v_inst_849_);
            crate::leanh::lean_dec_ref(v_inst_848_);
            v_a_853_ = crate::leanh::lean_ctor_get(v_x_852_, 0);
            crate::leanh::lean_inc(v_a_853_);
            crate::leanh::lean_dec_ref_known(v_x_852_, 1);
            v___x_854_ = crate::leanh::lean_apply_1(v_f_851_, v_a_853_);
            return v___x_854_;
        }
        1 => {
            let mut v_a_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_855_ = crate::leanh::lean_ctor_get(v_x_852_, 0);
            crate::leanh::lean_inc_n(v_a_855_, 2);
            crate::leanh::lean_dec_ref_known(v_x_852_, 1);
            v___f_856_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_856_, 0, v_a_855_);
            crate::leanh::lean_closure_set(v___f_856_, 1, v_f_851_);
            v___x_857_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_858_ = l_Lean_modToFilePath(v_dir_850_, v_a_855_, v___x_857_);
            crate::leanh::lean_dec_ref(v_dir_850_);
            v___x_859_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_848_,
                v_inst_849_,
                v___x_858_,
                v___f_856_,
            );
            return v___x_859_;
        }
        _ => {
            let mut v_toApplicative_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_860_ = crate::leanh::lean_ctor_get(v_inst_848_, 0);
            v_toSeqRight_861_ = crate::leanh::lean_ctor_get(v_toApplicative_860_, 4);
            crate::leanh::lean_inc(v_toSeqRight_861_);
            v_a_862_ = crate::leanh::lean_ctor_get(v_x_852_, 0);
            crate::leanh::lean_inc_n(v_a_862_, 3);
            crate::leanh::lean_dec_ref_known(v_x_852_, 1);
            crate::leanh::lean_inc(v_f_851_);
            v___f_863_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_863_, 0, v_a_862_);
            crate::leanh::lean_closure_set(v___f_863_, 1, v_f_851_);
            v___f_864_ = crate::leanh::lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_864_, 0, v_dir_850_);
            crate::leanh::lean_closure_set(v___f_864_, 1, v_a_862_);
            crate::leanh::lean_closure_set(v___f_864_, 2, v_inst_848_);
            crate::leanh::lean_closure_set(v___f_864_, 3, v_inst_849_);
            crate::leanh::lean_closure_set(v___f_864_, 4, v___f_863_);
            v___x_865_ = crate::leanh::lean_apply_1(v_f_851_, v_a_862_);
            v___x_866_ = crate::leanh::lean_apply_4(
                v_toSeqRight_861_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_865_,
                v___f_864_,
            );
            return v___x_866_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Glob(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Path(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Glob(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Glob(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Path(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Glob(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Glob(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Glob(builtin);
}

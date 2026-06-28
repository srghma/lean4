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
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_instInhabitedGlob_default___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_instInhabitedGlob_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedGlob_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedGlob: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedGlob_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instReprGlob_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_instReprGlob_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprGlob_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__2_value) as *mut LeanObject;
static mut l_Lake_instReprGlob_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprGlob_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprGlob_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprGlob_repr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprGlob_repr___closed__5_value: LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instReprGlob_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_instReprGlob_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__6_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprGlob_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__8_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        76, 97, 107, 101, 46, 71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100, 117,
        108, 101, 115, 0,
    ],
};
static mut l_Lake_instReprGlob_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__8_value) as *mut LeanObject],
};
static mut l_Lake_instReprGlob_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value) as *mut LeanObject;
pub static l_Lake_instReprGlob_repr___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__9_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprGlob_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob_repr___closed__10_value) as *mut LeanObject;
pub static l_Lake_instReprGlob___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprGlob_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprGlob___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprGlob: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprGlob___closed__0_value) as *mut LeanObject;
pub static l_Lake_instCoeNameGlob___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instCoeNameGlob___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instCoeNameGlob___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCoeNameGlob: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeNameGlob___closed__0_value) as *mut LeanObject;
pub static l_Lake_instCoeGlobArray___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_singleton as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_instCoeGlobArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCoeGlobArray: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeGlobArray___closed__0_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__1_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value) as *mut LeanObject;
static l_Lake_term_____x2e_x2a___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_term_____x2e_x2a___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__1_value) as *mut LeanObject,
        10150953148658318397 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__3_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__5_value) as *mut LeanObject,
        5949480926448383572 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__6_value) as *mut LeanObject],
};
static mut l_Lake_term_____x2e_x2a___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__8_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__8_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__10_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__10_value) as *mut LeanObject,
        1581446985683836252 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__11_value) as *mut LeanObject],
};
static mut l_Lake_term_____x2e_x2a___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__15_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2a___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__15_value) as *mut LeanObject],
};
static mut l_Lake_term_____x2e_x2a___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2a___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__2_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__17_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2a___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value) as *mut LeanObject;
pub static mut l_Lake_term_____x2e_x2a: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__18_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [71, 108, 111, 98, 46, 97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [71, 108, 111, 98, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 100, 83, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut LeanObject,9097109829436277786 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut LeanObject,2906245839412892126 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut LeanObject,12140512885907428830 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value) as *mut LeanObject,1477412787864469706 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2b___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value) as *mut LeanObject;
static l_Lake_term_____x2e_x2b___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_term_____x2e_x2b___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__0_value) as *mut LeanObject,
        11289494576251685396 as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2b___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_term_____x2e_x2b___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_term_____x2e_x2b___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2b___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value) as *mut LeanObject;
pub static l_Lake_term_____x2e_x2b___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_term_____x2e_x2b___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut LeanObject;
pub static mut l_Lake_term_____x2e_x2b: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_term_____x2e_x2b___closed__5_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [71, 108, 111, 98, 46, 115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut LeanObject,9097109829436277786 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut LeanObject,15076241754705399326 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value) as *mut LeanObject;
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_term_____x2e_x2a___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value) as *mut LeanObject,12140512885907428830 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value) as *mut LeanObject,11186284017425669258 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value) as *mut LeanObject;
pub static l_Lake_Glob_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Glob_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Glob_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Glob_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_Glob_ctorIdx(mut v_x_434_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_434_) {
        0 => {
            let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
            v___x_435_ = lean_unsigned_to_nat(0);
            return v___x_435_;
        }
        1 => {
            let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
            v___x_436_ = lean_unsigned_to_nat(1);
            return v___x_436_;
        }
        _ => {
            let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
            v___x_437_ = lean_unsigned_to_nat(2);
            return v___x_437_;
        }
    }
}
pub unsafe fn l_Lake_Glob_ctorIdx___boxed(mut v_x_438_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_439_: *mut LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lake_Glob_ctorIdx(v_x_438_);
    lean_dec_ref(v_x_438_);
    return v_res_439_;
}
pub unsafe fn l_Lake_Glob_ctorElim___redArg(
    mut v_t_440_: *mut LeanObject,
    mut v_k_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v_a_442_ = lean_ctor_get(v_t_440_, 0);
    lean_inc(v_a_442_);
    lean_dec_ref(v_t_440_);
    v___x_443_ = lean_apply_1(v_k_441_, v_a_442_);
    return v___x_443_;
}
pub unsafe fn l_Lake_Glob_ctorElim(
    mut v_motive_444_: *mut LeanObject,
    mut v_ctorIdx_445_: *mut LeanObject,
    mut v_t_446_: *mut LeanObject,
    mut v_h_447_: *mut LeanObject,
    mut v_k_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lake_Glob_ctorElim___redArg(v_t_446_, v_k_448_);
    return v___x_449_;
}
pub unsafe fn l_Lake_Glob_ctorElim___boxed(
    mut v_motive_450_: *mut LeanObject,
    mut v_ctorIdx_451_: *mut LeanObject,
    mut v_t_452_: *mut LeanObject,
    mut v_h_453_: *mut LeanObject,
    mut v_k_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_455_: *mut LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Lake_Glob_ctorElim(v_motive_450_, v_ctorIdx_451_, v_t_452_, v_h_453_, v_k_454_);
    lean_dec(v_ctorIdx_451_);
    return v_res_455_;
}
pub unsafe fn l_Lake_Glob_one_elim___redArg(
    mut v_t_456_: *mut LeanObject,
    mut v_one_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Lake_Glob_ctorElim___redArg(v_t_456_, v_one_457_);
    return v___x_458_;
}
pub unsafe fn l_Lake_Glob_one_elim(
    mut v_motive_459_: *mut LeanObject,
    mut v_t_460_: *mut LeanObject,
    mut v_h_461_: *mut LeanObject,
    mut v_one_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    v___x_463_ = l_Lake_Glob_ctorElim___redArg(v_t_460_, v_one_462_);
    return v___x_463_;
}
pub unsafe fn l_Lake_Glob_submodules_elim___redArg(
    mut v_t_464_: *mut LeanObject,
    mut v_submodules_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = l_Lake_Glob_ctorElim___redArg(v_t_464_, v_submodules_465_);
    return v___x_466_;
}
pub unsafe fn l_Lake_Glob_submodules_elim(
    mut v_motive_467_: *mut LeanObject,
    mut v_t_468_: *mut LeanObject,
    mut v_h_469_: *mut LeanObject,
    mut v_submodules_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lake_Glob_ctorElim___redArg(v_t_468_, v_submodules_470_);
    return v___x_471_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim___redArg(
    mut v_t_472_: *mut LeanObject,
    mut v_andSubmodules_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Lake_Glob_ctorElim___redArg(v_t_472_, v_andSubmodules_473_);
    return v___x_474_;
}
pub unsafe fn l_Lake_Glob_andSubmodules_elim(
    mut v_motive_475_: *mut LeanObject,
    mut v_t_476_: *mut LeanObject,
    mut v_h_477_: *mut LeanObject,
    mut v_andSubmodules_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Lake_Glob_ctorElim___redArg(v_t_476_, v_andSubmodules_478_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__3() -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = lean_unsigned_to_nat(2);
    v___x_491_ = lean_nat_to_int(v___x_490_);
    return v___x_491_;
}
pub unsafe fn _init_l_Lake_instReprGlob_repr___closed__4() -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_unsigned_to_nat(1);
    v___x_493_ = lean_nat_to_int(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Lake_instReprGlob_repr(
    mut v_x_506_: *mut LeanObject,
    mut v_prec_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: u8 = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_506_) {
                0 => {
                    v_a_508_ = lean_ctor_get(v_x_506_, 0);
                    lean_inc(v_a_508_);
                    lean_dec_ref_known(v_x_506_, 1);
                    v___x_519_ = lean_unsigned_to_nat(1024);
                    v___x_520_ = lean_nat_dec_le(v___x_519_, v_prec_507_);
                    if v___x_520_ == 0 {
                        v___x_521_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_510_ = v___x_521_;
                        state = 1;
                        continue;
                    } else {
                        v___x_522_ = lean_obj_once(
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
                    v_a_523_ = lean_ctor_get(v_x_506_, 0);
                    lean_inc(v_a_523_);
                    lean_dec_ref_known(v_x_506_, 1);
                    v___x_534_ = lean_unsigned_to_nat(1024);
                    v___x_535_ = lean_nat_dec_le(v___x_534_, v_prec_507_);
                    if v___x_535_ == 0 {
                        v___x_536_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_525_ = v___x_536_;
                        state = 2;
                        continue;
                    } else {
                        v___x_537_ = lean_obj_once(
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
                    v_a_538_ = lean_ctor_get(v_x_506_, 0);
                    lean_inc(v_a_538_);
                    lean_dec_ref_known(v_x_506_, 1);
                    v___x_549_ = lean_unsigned_to_nat(1024);
                    v___x_550_ = lean_nat_dec_le(v___x_549_, v_prec_507_);
                    if v___x_550_ == 0 {
                        v___x_551_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprGlob_repr___closed__3_once),
                            _init_l_Lake_instReprGlob_repr___closed__3,
                        );
                        v___y_540_ = v___x_551_;
                        state = 3;
                        continue;
                    } else {
                        v___x_552_ = lean_obj_once(
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
                v___x_512_ = lean_unsigned_to_nat(1024);
                v___x_513_ = l_Lean_Name_reprPrec(v_a_508_, v___x_512_);
                v___x_514_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_514_, 0, v___x_511_);
                lean_ctor_set(v___x_514_, 1, v___x_513_);
                lean_inc(v___y_510_);
                v___x_515_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_515_, 0, v___y_510_);
                lean_ctor_set(v___x_515_, 1, v___x_514_);
                v___x_516_ = 0;
                v___x_517_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_517_, 0, v___x_515_);
                lean_ctor_set_uint8(
                    v___x_517_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_516_,
                );
                v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_507_);
                return v___x_518_;
            }
            2 => {
                v___x_526_ = l_Lake_instReprGlob_repr___closed__7;
                v___x_527_ = lean_unsigned_to_nat(1024);
                v___x_528_ = l_Lean_Name_reprPrec(v_a_523_, v___x_527_);
                v___x_529_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_529_, 0, v___x_526_);
                lean_ctor_set(v___x_529_, 1, v___x_528_);
                lean_inc(v___y_525_);
                v___x_530_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_530_, 0, v___y_525_);
                lean_ctor_set(v___x_530_, 1, v___x_529_);
                v___x_531_ = 0;
                v___x_532_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_532_, 0, v___x_530_);
                lean_ctor_set_uint8(
                    v___x_532_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_531_,
                );
                v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_507_);
                return v___x_533_;
            }
            3 => {
                v___x_541_ = l_Lake_instReprGlob_repr___closed__10;
                v___x_542_ = lean_unsigned_to_nat(1024);
                v___x_543_ = l_Lean_Name_reprPrec(v_a_538_, v___x_542_);
                v___x_544_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_544_, 0, v___x_541_);
                lean_ctor_set(v___x_544_, 1, v___x_543_);
                lean_inc(v___y_540_);
                v___x_545_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_545_, 0, v___y_540_);
                lean_ctor_set(v___x_545_, 1, v___x_544_);
                v___x_546_ = 0;
                v___x_547_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_547_, 0, v___x_545_);
                lean_ctor_set_uint8(
                    v___x_547_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_553_: *mut LeanObject,
    mut v_prec_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lake_instReprGlob_repr(v_x_553_, v_prec_554_);
    lean_dec(v_prec_554_);
    return v_res_555_;
}
pub unsafe fn l_Lake_instDecidableEqGlob_decEq(
    mut v_x_558_: *mut LeanObject,
    mut v_x_559_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_558_) {
        0 => {
            if lean_obj_tag(v_x_559_) == 0 {
                let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_561_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_562_: u8 = 0;
                v_a_560_ = lean_ctor_get(v_x_558_, 0);
                v_a_561_ = lean_ctor_get(v_x_559_, 0);
                v___x_562_ = lean_name_eq(v_a_560_, v_a_561_);
                return v___x_562_;
            } else {
                let mut v___x_563_: u8 = 0;
                v___x_563_ = 0;
                return v___x_563_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_559_) == 1 {
                let mut v_a_564_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_565_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v_a_564_ = lean_ctor_get(v_x_558_, 0);
                v_a_565_ = lean_ctor_get(v_x_559_, 0);
                v___x_566_ = lean_name_eq(v_a_564_, v_a_565_);
                return v___x_566_;
            } else {
                let mut v___x_567_: u8 = 0;
                v___x_567_ = 0;
                return v___x_567_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_559_) == 2 {
                let mut v_a_568_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_569_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_570_: u8 = 0;
                v_a_568_ = lean_ctor_get(v_x_558_, 0);
                v_a_569_ = lean_ctor_get(v_x_559_, 0);
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
    mut v_x_572_: *mut LeanObject,
    mut v_x_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lake_instDecidableEqGlob_decEq(v_x_572_, v_x_573_);
    lean_dec_ref(v_x_573_);
    lean_dec_ref(v_x_572_);
    v_r_575_ = lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Lake_instDecidableEqGlob(
    mut v_x_576_: *mut LeanObject,
    mut v_x_577_: *mut LeanObject,
) -> u8 {
    let mut v___x_578_: u8 = 0;
    v___x_578_ = l_Lake_instDecidableEqGlob_decEq(v_x_576_, v_x_577_);
    return v___x_578_;
}
pub unsafe fn l_Lake_instDecidableEqGlob___boxed(
    mut v_x_579_: *mut LeanObject,
    mut v_x_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_581_: u8 = 0;
    let mut v_r_582_: *mut LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lake_instDecidableEqGlob(v_x_579_, v_x_580_);
    lean_dec_ref(v_x_580_);
    lean_dec_ref(v_x_579_);
    v_r_582_ = lean_box((v_res_581_) as usize);
    return v_r_582_;
}
pub unsafe fn l_Lake_instCoeNameGlob___lam__0(mut v_a_583_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_584_, 0, v_a_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6()
-> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5;
    v___x_640_ = l_String_toRawSubstring_x27(v___x_639_);
    return v___x_640_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
    mut v_x_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    v___x_673_ = l_Lake_term_____x2e_x2a___closed__2;
    lean_inc(v_x_670_);
    v___x_674_ = l_Lean_Syntax_isOfKind(v_x_670_, v___x_673_);
    if v___x_674_ == 0 {
        let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_670_);
        v___x_675_ = lean_box(1);
        v___x_676_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_676_, 0, v___x_675_);
        lean_ctor_set(v___x_676_, 1, v_a_672_);
        return v___x_676_;
    } else {
        let mut v_quotContext_677_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_678_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_682_: u8 = 0;
        let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_677_ = lean_ctor_get(v_a_671_, 1);
        v_currMacroScope_678_ = lean_ctor_get(v_a_671_, 2);
        v_ref_679_ = lean_ctor_get(v_a_671_, 5);
        v___x_680_ = lean_unsigned_to_nat(0);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_670_, v___x_680_);
        lean_dec(v_x_670_);
        v___x_682_ = 0;
        v___x_683_ = l_Lean_SourceInfo_fromRef(v_ref_679_, v___x_682_);
        v___x_684_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_685_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6);
        v___x_686_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9;
        lean_inc(v_currMacroScope_678_);
        lean_inc(v_quotContext_677_);
        v___x_687_ = l_Lean_addMacroScope(v_quotContext_677_, v___x_686_, v_currMacroScope_678_);
        v___x_688_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14;
        lean_inc_n(v___x_683_, 2);
        v___x_689_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_689_, 0, v___x_683_);
        lean_ctor_set(v___x_689_, 1, v___x_685_);
        lean_ctor_set(v___x_689_, 2, v___x_687_);
        lean_ctor_set(v___x_689_, 3, v___x_688_);
        v___x_690_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_691_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_692_ = lean_unsigned_to_nat(1);
        v___x_693_ = lean_mk_empty_array_with_capacity(v___x_692_);
        v___x_694_ = lean_array_push(v___x_693_, v___x_681_);
        v___x_695_ = lean_box(2);
        v___x_696_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_696_, 0, v___x_695_);
        lean_ctor_set(v___x_696_, 1, v___x_691_);
        lean_ctor_set(v___x_696_, 2, v___x_694_);
        v___x_697_ = l_Lean_Syntax_node1(v___x_683_, v___x_690_, v___x_696_);
        v___x_698_ = l_Lean_Syntax_node2(v___x_683_, v___x_684_, v___x_689_, v___x_697_);
        v___x_699_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_699_, 0, v___x_698_);
        lean_ctor_set(v___x_699_, 1, v_a_672_);
        return v___x_699_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___boxed(
    mut v_x_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(
        v_x_700_, v_a_701_, v_a_702_,
    );
    lean_dec_ref(v_a_701_);
    return v_res_703_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1()
-> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ =
        l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0;
    v___x_722_ = l_String_toRawSubstring_x27(v___x_721_);
    return v___x_722_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
    mut v_x_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    v___x_745_ = l_Lake_term_____x2e_x2b___closed__1;
    lean_inc(v_x_742_);
    v___x_746_ = l_Lean_Syntax_isOfKind(v_x_742_, v___x_745_);
    if v___x_746_ == 0 {
        let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_742_);
        v___x_747_ = lean_box(1);
        v___x_748_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_748_, 0, v___x_747_);
        lean_ctor_set(v___x_748_, 1, v_a_744_);
        return v___x_748_;
    } else {
        let mut v_quotContext_749_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_750_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_754_: u8 = 0;
        let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_749_ = lean_ctor_get(v_a_743_, 1);
        v_currMacroScope_750_ = lean_ctor_get(v_a_743_, 2);
        v_ref_751_ = lean_ctor_get(v_a_743_, 5);
        v___x_752_ = lean_unsigned_to_nat(0);
        v___x_753_ = l_Lean_Syntax_getArg(v_x_742_, v___x_752_);
        lean_dec(v_x_742_);
        v___x_754_ = 0;
        v___x_755_ = l_Lean_SourceInfo_fromRef(v_ref_751_, v___x_754_);
        v___x_756_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4;
        v___x_757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once), _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1);
        v___x_758_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3;
        lean_inc(v_currMacroScope_750_);
        lean_inc(v_quotContext_749_);
        v___x_759_ = l_Lean_addMacroScope(v_quotContext_749_, v___x_758_, v_currMacroScope_750_);
        v___x_760_ =
            l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8;
        lean_inc_n(v___x_755_, 2);
        v___x_761_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_761_, 0, v___x_755_);
        lean_ctor_set(v___x_761_, 1, v___x_757_);
        lean_ctor_set(v___x_761_, 2, v___x_759_);
        lean_ctor_set(v___x_761_, 3, v___x_760_);
        v___x_762_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16;
        v___x_763_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18;
        v___x_764_ = lean_unsigned_to_nat(1);
        v___x_765_ = lean_mk_empty_array_with_capacity(v___x_764_);
        v___x_766_ = lean_array_push(v___x_765_, v___x_753_);
        v___x_767_ = lean_box(2);
        v___x_768_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_768_, 0, v___x_767_);
        lean_ctor_set(v___x_768_, 1, v___x_763_);
        lean_ctor_set(v___x_768_, 2, v___x_766_);
        v___x_769_ = l_Lean_Syntax_node1(v___x_755_, v___x_762_, v___x_768_);
        v___x_770_ = l_Lean_Syntax_node2(v___x_755_, v___x_756_, v___x_761_, v___x_769_);
        v___x_771_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_771_, 0, v___x_770_);
        lean_ctor_set(v___x_771_, 1, v_a_744_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___boxed(
    mut v_x_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_775_: *mut LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(
        v_x_772_, v_a_773_, v_a_774_,
    );
    lean_dec_ref(v_a_773_);
    return v_res_775_;
}
pub unsafe fn l_Lake_Glob_toString(mut v_x_776_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_776_) {
        0 => {
            let mut v_a_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_778_: u8 = 0;
            let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
            v_a_777_ = lean_ctor_get(v_x_776_, 0);
            lean_inc(v_a_777_);
            lean_dec_ref_known(v_x_776_, 1);
            v___x_778_ = 1;
            v___x_779_ = l_Lean_Name_toString(v_a_777_, v___x_778_);
            return v___x_779_;
        }
        1 => {
            let mut v_a_780_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_781_: u8 = 0;
            let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
            v_a_780_ = lean_ctor_get(v_x_776_, 0);
            lean_inc(v_a_780_);
            lean_dec_ref_known(v_x_776_, 1);
            v___x_781_ = 1;
            v___x_782_ = l_Lean_Name_toString(v_a_780_, v___x_781_);
            v___x_783_ = l_Lake_term_____x2e_x2b___closed__2;
            v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
            return v___x_784_;
        }
        _ => {
            let mut v_a_785_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_786_: u8 = 0;
            let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
            v_a_785_ = lean_ctor_get(v_x_776_, 0);
            lean_inc(v_a_785_);
            lean_dec_ref_known(v_x_776_, 1);
            v___x_786_ = 1;
            v___x_787_ = l_Lean_Name_toString(v_a_785_, v___x_786_);
            v___x_788_ = l_Lake_term_____x2e_x2a___closed__15;
            v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
            return v___x_789_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches(
    mut v_m_792_: *mut LeanObject,
    mut v_x_793_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_793_) {
        0 => {
            let mut v_a_794_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_795_: u8 = 0;
            v_a_794_ = lean_ctor_get(v_x_793_, 0);
            v___x_795_ = lean_name_eq(v_a_794_, v_m_792_);
            return v___x_795_;
        }
        1 => {
            let mut v_a_796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_a_796_ = lean_ctor_get(v_x_793_, 0);
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
            let mut v_a_800_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            v_a_800_ = lean_ctor_get(v_x_793_, 0);
            v___x_801_ = l_Lean_Name_isPrefixOf(v_a_800_, v_m_792_);
            return v___x_801_;
        }
    }
}
pub unsafe fn l_Lake_Glob_matches___boxed(
    mut v_m_802_: *mut LeanObject,
    mut v_x_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: u8 = 0;
    let mut v_r_805_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_Glob_matches(v_m_802_, v_x_803_);
    lean_dec_ref(v_x_803_);
    lean_dec(v_m_802_);
    v_r_805_ = lean_box((v_res_804_) as usize);
    return v_r_805_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__0(
    mut v_a_806_: *mut LeanObject,
    mut v_f_807_: *mut LeanObject,
    mut v_x_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lean_Name_append(v_a_806_, v_x_808_);
    v___x_810_ = lean_apply_1(v_f_807_, v___x_809_);
    return v___x_810_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2(
    mut v_dir_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_inst_814_: *mut LeanObject,
    mut v_inst_815_: *mut LeanObject,
    mut v___f_816_: *mut LeanObject,
    mut v_x_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
    v___x_819_ = l_Lean_modToFilePath(v_dir_812_, v_a_813_, v___x_818_);
    v___x_820_ =
        l_Lean_forEachModuleInDir___redArg(v_inst_814_, v_inst_815_, v___x_819_, v___f_816_);
    return v___x_820_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(
    mut v_dir_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_inst_823_: *mut LeanObject,
    mut v_inst_824_: *mut LeanObject,
    mut v___f_825_: *mut LeanObject,
    mut v_x_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_827_: *mut LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2(
        v_dir_821_,
        v_a_822_,
        v_inst_823_,
        v_inst_824_,
        v___f_825_,
        v_x_826_,
    );
    lean_dec_ref(v_dir_821_);
    return v_res_827_;
}
pub unsafe fn l_Lake_Glob_forEachModuleIn___redArg(
    mut v_inst_828_: *mut LeanObject,
    mut v_inst_829_: *mut LeanObject,
    mut v_dir_830_: *mut LeanObject,
    mut v_f_831_: *mut LeanObject,
    mut v_x_832_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_832_) {
        0 => {
            let mut v_a_833_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_dir_830_);
            lean_dec(v_inst_829_);
            lean_dec_ref(v_inst_828_);
            v_a_833_ = lean_ctor_get(v_x_832_, 0);
            lean_inc(v_a_833_);
            lean_dec_ref_known(v_x_832_, 1);
            v___x_834_ = lean_apply_1(v_f_831_, v_a_833_);
            return v___x_834_;
        }
        1 => {
            let mut v_a_835_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_836_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
            v_a_835_ = lean_ctor_get(v_x_832_, 0);
            lean_inc_n(v_a_835_, 2);
            lean_dec_ref_known(v_x_832_, 1);
            v___f_836_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_836_, 0, v_a_835_);
            lean_closure_set(v___f_836_, 1, v_f_831_);
            v___x_837_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_838_ = l_Lean_modToFilePath(v_dir_830_, v_a_835_, v___x_837_);
            lean_dec_ref(v_dir_830_);
            v___x_839_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_828_,
                v_inst_829_,
                v___x_838_,
                v___f_836_,
            );
            return v___x_839_;
        }
        _ => {
            let mut v_toApplicative_840_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_841_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_842_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_843_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_840_ = lean_ctor_get(v_inst_828_, 0);
            v_toSeqRight_841_ = lean_ctor_get(v_toApplicative_840_, 4);
            lean_inc(v_toSeqRight_841_);
            v_a_842_ = lean_ctor_get(v_x_832_, 0);
            lean_inc_n(v_a_842_, 3);
            lean_dec_ref_known(v_x_832_, 1);
            lean_inc(v_f_831_);
            v___f_843_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_843_, 0, v_a_842_);
            lean_closure_set(v___f_843_, 1, v_f_831_);
            v___f_844_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_844_, 0, v_dir_830_);
            lean_closure_set(v___f_844_, 1, v_a_842_);
            lean_closure_set(v___f_844_, 2, v_inst_828_);
            lean_closure_set(v___f_844_, 3, v_inst_829_);
            lean_closure_set(v___f_844_, 4, v___f_843_);
            v___x_845_ = lean_apply_1(v_f_831_, v_a_842_);
            v___x_846_ = lean_apply_4(
                v_toSeqRight_841_,
                lean_box(0),
                lean_box(0),
                v___x_845_,
                v___f_844_,
            );
            return v___x_846_;
        }
    }
}
pub unsafe fn l_Lake_Glob_forEachModuleIn(
    mut v_m_847_: *mut LeanObject,
    mut v_inst_848_: *mut LeanObject,
    mut v_inst_849_: *mut LeanObject,
    mut v_dir_850_: *mut LeanObject,
    mut v_f_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_852_) {
        0 => {
            let mut v_a_853_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_dir_850_);
            lean_dec(v_inst_849_);
            lean_dec_ref(v_inst_848_);
            v_a_853_ = lean_ctor_get(v_x_852_, 0);
            lean_inc(v_a_853_);
            lean_dec_ref_known(v_x_852_, 1);
            v___x_854_ = lean_apply_1(v_f_851_, v_a_853_);
            return v___x_854_;
        }
        1 => {
            let mut v_a_855_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
            v_a_855_ = lean_ctor_get(v_x_852_, 0);
            lean_inc_n(v_a_855_, 2);
            lean_dec_ref_known(v_x_852_, 1);
            v___f_856_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_856_, 0, v_a_855_);
            lean_closure_set(v___f_856_, 1, v_f_851_);
            v___x_857_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0;
            v___x_858_ = l_Lean_modToFilePath(v_dir_850_, v_a_855_, v___x_857_);
            lean_dec_ref(v_dir_850_);
            v___x_859_ = l_Lean_forEachModuleInDir___redArg(
                v_inst_848_,
                v_inst_849_,
                v___x_858_,
                v___f_856_,
            );
            return v___x_859_;
        }
        _ => {
            let mut v_toApplicative_860_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toSeqRight_861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_860_ = lean_ctor_get(v_inst_848_, 0);
            v_toSeqRight_861_ = lean_ctor_get(v_toApplicative_860_, 4);
            lean_inc(v_toSeqRight_861_);
            v_a_862_ = lean_ctor_get(v_x_852_, 0);
            lean_inc_n(v_a_862_, 3);
            lean_dec_ref_known(v_x_852_, 1);
            lean_inc(v_f_851_);
            v___f_863_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_863_, 0, v_a_862_);
            lean_closure_set(v___f_863_, 1, v_f_851_);
            v___f_864_ = lean_alloc_closure(
                l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_864_, 0, v_dir_850_);
            lean_closure_set(v___f_864_, 1, v_a_862_);
            lean_closure_set(v___f_864_, 2, v_inst_848_);
            lean_closure_set(v___f_864_, 3, v_inst_849_);
            lean_closure_set(v___f_864_, 4, v___f_863_);
            v___x_865_ = lean_apply_1(v_f_851_, v_a_862_);
            v___x_866_ = lean_apply_4(
                v_toSeqRight_861_,
                lean_box(0),
                lean_box(0),
                v___x_865_,
                v___f_864_,
            );
            return v___x_866_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Glob(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Glob(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Glob(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Glob(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Glob(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Glob(builtin);
}

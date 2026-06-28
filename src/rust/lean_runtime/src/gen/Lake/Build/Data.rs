// Lean compiler output
// Module: Lake.Build.Data
// Imports: Lake.Build.Key Lake.Util.Family Lake.Config.Dynlib Lake.Config.Kinds Lake.Config.Kinds Lake.Util.Name Lake.Config.Kinds Lake.Util.Name
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_TSyntax_getId, l_Lean_mkCIdentFrom, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_resolveNamespace,
    l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getId, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_Syntax_node8, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::Build::Key::{
    initialize_Lake_Build_Key, runtime_initialize_Lake_Build_Key,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Config::Kinds::{
    initialize_Lake_Config_Kinds, l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace,
    l_Lake_Module_keyword, l_Lake_Package_keyword, meta_initialize_Lake_Config_Kinds,
    runtime_initialize_Lake_Config_Kinds,
};
use crate::r#gen::Lake::Util::Family::{
    initialize_Lake_Util_Family, runtime_initialize_Lake_Util_Family,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_quoteFrom, meta_initialize_Lake_Util_Name,
    runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lake_OptDataKind_instCoeOutName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_OptDataKind_instCoeOutName___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OptDataKind_instCoeOutName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OptDataKind_instCoeOutName___closed__0_value) as *mut LeanObject;
pub static l_Lake_OptDataKind_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_OptDataKind_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OptDataKind_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OptDataKind_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_dataTypeDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__1_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 97, 116, 97, 84, 121, 112, 101, 68, 101, 99, 108, 0],
};
static mut l_Lake_dataTypeDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__1_value) as *mut LeanObject;
static l_Lake_dataTypeDecl___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_dataTypeDecl___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__1_value) as *mut LeanObject,
        1881956779838328975 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__3_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lake_dataTypeDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__5_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lake_dataTypeDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__5_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__7_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lake_dataTypeDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__7_value) as *mut LeanObject,
        3961966953292576997 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__8_value) as *mut LeanObject],
};
static mut l_Lake_dataTypeDecl___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__9_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__11_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 97, 116, 97, 95, 116, 121, 112, 101, 32, 0],
};
static mut l_Lake_dataTypeDecl___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__11_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__11_value) as *mut LeanObject],
};
static mut l_Lake_dataTypeDecl___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__12_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__13_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__14_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_dataTypeDecl___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__14_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__14_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__15_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__15_value) as *mut LeanObject],
};
static mut l_Lake_dataTypeDecl___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__17_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__18_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l_Lake_dataTypeDecl___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__18_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__18_value) as *mut LeanObject],
};
static mut l_Lake_dataTypeDecl___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__17_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__20_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__21_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_dataTypeDecl___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__21_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__21_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__22_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__23_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__22_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__20_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__24_value) as *mut LeanObject;
pub static l_Lake_dataTypeDecl___closed__25_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__24_value) as *mut LeanObject,
    ],
};
static mut l_Lake_dataTypeDecl___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__25_value) as *mut LeanObject;
pub static mut l_Lake_dataTypeDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__25_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 97, 109, 105, 108, 121, 95, 100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value) as *mut LeanObject,10411423847645546083 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value) as *mut LeanObject,11064845058293668901 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value) as *mut LeanObject,5940551064397964566 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value
) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value) as *mut LeanObject,16416955358139906133 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value) as *mut LeanObject,2323862020472801593 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value) as *mut LeanObject,13585030837571646948 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value) as *mut LeanObject,12783917532758215986 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value) as *mut LeanObject,7383208167966365478 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [78, 97, 109, 101, 46, 105, 115, 65, 110, 111, 110, 121, 109, 111, 117, 115, 95, 105, 102, 102, 95, 101, 113, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value
) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [78, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [105, 115, 65, 110, 111, 110, 121, 109, 111, 117, 115, 95, 105, 102, 102, 95, 101, 113, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value) as *mut LeanObject,7623807776322335386 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value) as *mut LeanObject,18384533828395609354 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value) as *mut LeanObject,4969359694978789214 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value) as *mut LeanObject,15756887508575660446 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value) as *mut LeanObject,10991155264597083169 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 97, 109, 105, 108, 121, 68, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value) as *mut LeanObject,11046805638130364475 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value
) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value
) as *mut LeanObject;
pub static l_Lake_instDataKindUnit___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [117, 110, 105, 116, 0],
};
static mut l_Lake_instDataKindUnit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindUnit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__0_value) as *mut LeanObject,
        10978858759480610910 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindUnit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindUnit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindBool___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [98, 111, 111, 108, 0],
};
static mut l_Lake_instDataKindBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindBool___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindBool___closed__0_value) as *mut LeanObject,
        11722710492834003908 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindBool___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindFilePath___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 105, 108, 101, 112, 97, 116, 104, 0],
};
static mut l_Lake_instDataKindFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindFilePath___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__0_value) as *mut LeanObject,
        18237634648366862254 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindFilePath___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindDynlib___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 121, 110, 108, 105, 98, 0],
};
static mut l_Lake_instDataKindDynlib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindDynlib___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__0_value) as *mut LeanObject,
        14454008108361683552 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindDynlib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindDynlib: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__1_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__0_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 70, 97, 99, 101, 116, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__0_value) as *mut LeanObject;
static l_Lake_builtinFacetCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_builtinFacetCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__0_value) as *mut LeanObject,
        4395217195902989964 as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__2_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 102, 97, 99, 101, 116, 32, 0,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_builtinFacetCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__4_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__5_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 116, 111, 109, 105, 99, 0],
};
static mut l_Lake_builtinFacetCommand___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__5_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__5_value) as *mut LeanObject,
        4024150434455327032 as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__6_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__7_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lake_builtinFacetCommand___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__7_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__7_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__8_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__9_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 64, 32, 0],
};
static mut l_Lake_builtinFacetCommand___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__9_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__9_value) as *mut LeanObject],
};
static mut l_Lake_builtinFacetCommand___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__10_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__11_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__12_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__13_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__14_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__15_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__16_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__17_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__17_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__18_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__19_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Lake_builtinFacetCommand___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__19_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__20_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__19_value) as *mut LeanObject],
};
static mut l_Lake_builtinFacetCommand___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__20_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__21_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__18_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__20_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__21_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__21_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__22_value) as *mut LeanObject;
pub static l_Lake_builtinFacetCommand___closed__23_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lake_builtinFacetCommand___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__23_value) as *mut LeanObject;
pub static mut l_Lake_builtinFacetCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__23_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value) as *mut LeanObject,7045040058828669725 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 115, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value) as *mut LeanObject,9363914857124557226 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 97, 109, 105, 108, 121, 68, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut LeanObject,14062987408811487381 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value) as *mut LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 43, 43, 95, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value) as *mut LeanObject,1718176677342102874 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [43, 43, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 102, 101, 114, 73, 110, 115, 116, 97, 110, 99, 101, 65, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [99, 97, 110, 110, 111, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 102, 97, 99, 101, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 114, 111, 109, 32, 102, 97, 99, 101, 116, 32, 110, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 99, 101, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 97, 99, 101, 116, 79, 117, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value) as *mut LeanObject,18435903728707736368 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 116, 97, 114, 103, 101, 116, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 111, 114, 32, 97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 116, 97, 114, 103, 101, 116, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [102, 97, 99, 101, 116, 68, 97, 116, 97, 68, 101, 99, 108, 0],
};
static mut l_Lake_facetDataDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__0_value) as *mut LeanObject;
static l_Lake_facetDataDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_facetDataDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__0_value) as *mut LeanObject,
        6050667296239256698 as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__2_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [102, 97, 99, 101, 116, 95, 100, 97, 116, 97, 32, 0],
};
static mut l_Lake_facetDataDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_facetDataDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_facetDataDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake_facetDataDecl___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_facetDataDecl___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_facetDataDecl___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__9_value) as *mut LeanObject;
pub static mut l_Lake_facetDataDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__9_value) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut LeanObject,13678286827328889081 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value) as *mut LeanObject,5279388724434323336 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value
) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__0_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 68, 97, 116, 97, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_packageDataDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__0_value) as *mut LeanObject;
static l_Lake_packageDataDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_packageDataDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__0_value) as *mut LeanObject,
        2082768154632822931 as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__2_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [112, 97, 99, 107, 97, 103, 101, 95, 100, 97, 116, 97, 32, 0],
};
static mut l_Lake_packageDataDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_packageDataDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_packageDataDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_packageDataDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_packageDataDecl___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_packageDataDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__8_value) as *mut LeanObject;
pub static mut l_Lake_packageDataDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 97, 99, 101, 116, 95, 100, 97, 116, 97, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value
) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        109, 111, 100, 117, 108, 101, 68, 97, 116, 97, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_moduleDataDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__0_value) as *mut LeanObject;
static l_Lake_moduleDataDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_moduleDataDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__0_value) as *mut LeanObject,
        13351734753328622778 as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__2_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 111, 100, 117, 108, 101, 95, 100, 97, 116, 97, 32, 0],
};
static mut l_Lake_moduleDataDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_moduleDataDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_moduleDataDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_moduleDataDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__8_value) as *mut LeanObject;
pub static mut l_Lake_moduleDataDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__0_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        108, 105, 98, 114, 97, 114, 121, 68, 97, 116, 97, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_libraryDataDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__0_value) as *mut LeanObject;
static l_Lake_libraryDataDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_libraryDataDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__0_value) as *mut LeanObject,
        13678170361092144735 as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__2_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [108, 105, 98, 114, 97, 114, 121, 95, 100, 97, 116, 97, 32, 0],
};
static mut l_Lake_libraryDataDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_libraryDataDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_libraryDataDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_libraryDataDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__8_value) as *mut LeanObject;
pub static mut l_Lake_libraryDataDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value) as *mut LeanObject,12295998048739818339 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value
) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 117, 115, 116, 111, 109, 68, 97, 116, 97, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_customDataDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__0_value) as *mut LeanObject;
static l_Lake_customDataDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
pub static l_Lake_customDataDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__0_value) as *mut LeanObject,
        4714469286443954978 as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__2_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 117, 115, 116, 111, 109, 95, 100, 97, 116, 97, 32, 0],
};
static mut l_Lake_customDataDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_customDataDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_customDataDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__7_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__8_value) as *mut LeanObject;
pub static l_Lake_customDataDecl___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_customDataDecl___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_customDataDecl___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__9_value) as *mut LeanObject;
pub static mut l_Lake_customDataDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__9_value) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value) as *mut LeanObject,15644373471618144447 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value) as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value
) as *mut LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 117, 115, 116, 111, 109, 79, 117, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value
) as *mut LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value) as *mut LeanObject,10715840225401224552 as *mut LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value
) as *mut LeanObject;
pub unsafe fn l_Lake_OptDataKind_anonymous(
    mut v_00_u03b1_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = lean_box(0);
    return v___x_1528_;
}
pub unsafe fn l_Lake_OptDataKind_instInhabited(
    mut v_00_u03b1_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = lean_box(0);
    return v___x_1530_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___redArg(mut v_self_1531_: *mut LeanObject) -> u8 {
    let mut v___x_1532_: u8 = 0;
    v___x_1532_ = l_Lean_Name_isAnonymous(v_self_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___redArg___boxed(
    mut v_self_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1534_: u8 = 0;
    let mut v_r_1535_: *mut LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lake_OptDataKind_isAnonymous___redArg(v_self_1533_);
    lean_dec(v_self_1533_);
    v_r_1535_ = lean_box((v_res_1534_) as usize);
    return v_r_1535_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous(
    mut v_00_u03b1_1536_: *mut LeanObject,
    mut v_self_1537_: *mut LeanObject,
) -> u8 {
    let mut v___x_1538_: u8 = 0;
    v___x_1538_ = l_Lean_Name_isAnonymous(v_self_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___boxed(
    mut v_00_u03b1_1539_: *mut LeanObject,
    mut v_self_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: u8 = 0;
    let mut v_r_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lake_OptDataKind_isAnonymous(v_00_u03b1_1539_, v_self_1540_);
    lean_dec(v_self_1540_);
    v_r_1542_ = lean_box((v_res_1541_) as usize);
    return v_r_1542_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___redArg(
    mut v_inst_1543_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1543_);
    return v_inst_1543_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___redArg___boxed(
    mut v_inst_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1545_: *mut LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Lake_OptDataKind_instOfDataKind___redArg(v_inst_1544_);
    lean_dec(v_inst_1544_);
    return v_res_1545_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind(
    mut v_00_u03b1_1546_: *mut LeanObject,
    mut v_inst_1547_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1547_);
    return v_inst_1547_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___boxed(
    mut v_00_u03b1_1548_: *mut LeanObject,
    mut v_inst_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_OptDataKind_instOfDataKind(v_00_u03b1_1548_, v_inst_1549_);
    lean_dec(v_inst_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName___lam__0(
    mut v_x_1551_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1551_);
    return v_x_1551_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName___lam__0___boxed(
    mut v_x_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Lake_OptDataKind_instCoeOutName___lam__0(v_x_1552_);
    lean_dec(v_x_1552_);
    return v_res_1553_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName(
    mut v_00_u03b1_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1556_: *mut LeanObject = core::ptr::null_mut();
    v___f_1556_ = l_Lake_OptDataKind_instCoeOutName___closed__0;
    return v___f_1556_;
}
pub unsafe fn l_Lake_OptDataKind_instToString___lam__0(
    mut v_x_1557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1558_ = 1;
    v___x_1559_ = l_Lean_Name_toString(v_x_1557_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_OptDataKind_instToString(
    mut v_00_u03b1_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1562_: *mut LeanObject = core::ptr::null_mut();
    v___f_1562_ = l_Lake_OptDataKind_instToString___closed__0;
    return v___f_1562_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24()
-> *mut LeanObject {
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    v___x_1676_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23;
    v___x_1677_ = l_String_toRawSubstring_x27(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53()
-> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52;
    v___x_1749_ = l_String_toRawSubstring_x27(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71()
-> *mut LeanObject {
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Array_mkArray0(lean_box(0));
    return v___x_1785_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(
    mut v_x_1788_: *mut LeanObject,
    mut v_a_1789_: *mut LeanObject,
    mut v_a_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1791_ = l_Lake_dataTypeDecl___closed__2;
                lean_inc(v_x_1788_);
                v___x_1792_ = l_Lean_Syntax_isOfKind(v_x_1788_, v___x_1791_);
                if v___x_1792_ == 0 {
                    lean_dec(v_x_1788_);
                    v___x_1793_ = lean_box(1);
                    v___x_1794_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1794_, 0, v___x_1793_);
                    lean_ctor_set(v___x_1794_, 1, v_a_1790_);
                    return v___x_1794_;
                } else {
                    v___x_1795_ = lean_unsigned_to_nat(0);
                    v___x_1796_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1795_);
                    v___x_1797_ = lean_unsigned_to_nat(2);
                    v_kind_1798_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1797_);
                    v___x_1799_ = lean_unsigned_to_nat(4);
                    v___x_1800_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1799_);
                    lean_dec(v_x_1788_);
                    v___x_1908_ = l_Lean_Syntax_getOptional_x3f(v___x_1796_);
                    lean_dec(v___x_1796_);
                    if lean_obj_tag(v___x_1908_) == 0 {
                        v___x_1909_ = lean_box(0);
                        v___y_1892_ = v___x_1909_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1910_ = lean_ctor_get(v___x_1908_, 0);
                        v_isSharedCheck_1917_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                        if v_isSharedCheck_1917_ == 0 {
                            v___x_1912_ = v___x_1908_;
                            v_isShared_1913_ = v_isSharedCheck_1917_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1910_);
                            lean_dec(v___x_1908_);
                            v___x_1912_ = lean_box(0);
                            v_isShared_1913_ = v_isSharedCheck_1917_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_1806_, 2);
                v___x_1811_ = l_Array_append___redArg(v___y_1806_, v___y_1810_);
                lean_dec_ref(v___y_1810_);
                lean_inc_n(v___y_1808_, 9);
                lean_inc_n(v___y_1805_, 40);
                v___x_1812_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1812_, 0, v___y_1805_);
                lean_ctor_set(v___x_1812_, 1, v___y_1808_);
                lean_ctor_set(v___x_1812_, 2, v___x_1811_);
                v___x_1813_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_1814_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1814_, 0, v___y_1805_);
                lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                v___x_1815_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_1816_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1816_, 0, v___y_1805_);
                lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                v___x_1817_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_1818_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1818_, 0, v___y_1805_);
                lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                lean_inc(v___x_1800_);
                lean_inc_ref(v___x_1818_);
                lean_inc(v___y_1803_);
                lean_inc_ref(v___x_1816_);
                lean_inc(v___y_1804_);
                v___x_1819_ = l_Lean_Syntax_node8(
                    v___y_1805_,
                    v___y_1804_,
                    v___x_1812_,
                    v___x_1814_,
                    v_kind_1798_,
                    v___x_1816_,
                    v___y_1807_,
                    v___y_1803_,
                    v___x_1818_,
                    v___x_1800_,
                );
                v___x_1820_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_1821_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_1822_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1822_, 0, v___y_1805_);
                lean_ctor_set(v___x_1822_, 1, v___y_1808_);
                lean_ctor_set(v___x_1822_, 2, v___y_1806_);
                v___x_1823_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                v___x_1824_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11;
                v___x_1825_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1825_, 0, v___y_1805_);
                lean_ctor_set(v___x_1825_, 1, v___x_1823_);
                v___x_1826_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1824_, v___x_1825_);
                v___x_1827_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1826_);
                lean_inc_ref_n(v___x_1822_, 18);
                v___x_1828_ = l_Lean_Syntax_node7(
                    v___y_1805_,
                    v___x_1821_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1827_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1822_,
                );
                v___x_1829_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_1830_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13;
                v___x_1831_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16;
                v___x_1832_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1831_, v___x_1822_);
                v___x_1833_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1833_, 0, v___y_1805_);
                lean_ctor_set(v___x_1833_, 1, v___x_1829_);
                v___x_1834_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18;
                v___x_1835_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20;
                v___x_1836_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22;
                v___x_1837_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24);
                v___x_1838_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25;
                lean_inc_n(v___y_1802_, 2);
                lean_inc_n(v___y_1809_, 2);
                v___x_1839_ = l_Lean_addMacroScope(v___y_1809_, v___x_1838_, v___y_1802_);
                v___x_1840_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30;
                v___x_1841_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1841_, 0, v___y_1805_);
                lean_ctor_set(v___x_1841_, 1, v___x_1837_);
                lean_ctor_set(v___x_1841_, 2, v___x_1839_);
                lean_ctor_set(v___x_1841_, 3, v___x_1840_);
                v___x_1842_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1800_);
                v___x_1843_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1836_, v___x_1841_, v___x_1842_);
                v___x_1844_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1835_, v___x_1816_, v___x_1843_);
                v___x_1845_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1834_, v___x_1822_, v___x_1844_);
                v___x_1846_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32;
                v___x_1847_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34;
                v___x_1848_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35;
                v___x_1849_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1849_, 0, v___y_1805_);
                lean_ctor_set(v___x_1849_, 1, v___x_1848_);
                v___x_1850_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_1851_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1851_, 0, v___y_1805_);
                lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                v___x_1852_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38;
                v___x_1853_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39;
                v___x_1854_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1854_, 0, v___y_1805_);
                lean_ctor_set(v___x_1854_, 1, v___x_1853_);
                v___x_1855_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42;
                v___x_1856_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44;
                v___x_1857_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45;
                v___x_1858_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46;
                v___x_1859_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1859_, 0, v___y_1805_);
                lean_ctor_set(v___x_1859_, 1, v___x_1857_);
                v___x_1860_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48;
                v___x_1861_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1860_, v___x_1822_);
                v___x_1862_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49;
                v___x_1863_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1863_, 0, v___y_1805_);
                lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51;
                v___x_1865_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53);
                v___x_1866_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56;
                v___x_1867_ = l_Lean_addMacroScope(v___y_1809_, v___x_1866_, v___y_1802_);
                v___x_1868_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59;
                v___x_1869_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___y_1805_);
                lean_ctor_set(v___x_1869_, 1, v___x_1865_);
                lean_ctor_set(v___x_1869_, 2, v___x_1867_);
                lean_ctor_set(v___x_1869_, 3, v___x_1868_);
                v___x_1870_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___x_1864_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1869_,
                );
                v___x_1871_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1870_);
                v___x_1872_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60;
                v___x_1873_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1873_, 0, v___y_1805_);
                lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                v___x_1874_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___y_1808_,
                    v___x_1863_,
                    v___x_1871_,
                    v___x_1873_,
                );
                v___x_1875_ = l_Lean_Syntax_node6(
                    v___y_1805_,
                    v___x_1858_,
                    v___x_1859_,
                    v___x_1861_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1874_,
                    v___x_1822_,
                );
                v___x_1876_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1875_);
                v___x_1877_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1856_, v___x_1876_);
                v___x_1878_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1855_, v___x_1877_);
                v___x_1879_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1852_, v___x_1854_, v___x_1878_);
                v___x_1880_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___y_1808_,
                    v___y_1803_,
                    v___x_1851_,
                    v___x_1879_,
                );
                v___x_1881_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61;
                v___x_1882_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1882_, 0, v___y_1805_);
                lean_ctor_set(v___x_1882_, 1, v___x_1881_);
                v___x_1883_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___x_1847_,
                    v___x_1849_,
                    v___x_1880_,
                    v___x_1882_,
                );
                v___x_1884_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64;
                v___x_1885_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1884_, v___x_1822_, v___x_1822_);
                v___x_1886_ = l_Lean_Syntax_node4(
                    v___y_1805_,
                    v___x_1846_,
                    v___x_1818_,
                    v___x_1883_,
                    v___x_1885_,
                    v___x_1822_,
                );
                v___x_1887_ = l_Lean_Syntax_node6(
                    v___y_1805_,
                    v___x_1830_,
                    v___x_1832_,
                    v___x_1833_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1845_,
                    v___x_1886_,
                );
                v___x_1888_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1820_, v___x_1828_, v___x_1887_);
                v___x_1889_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___y_1808_, v___x_1819_, v___x_1888_);
                v___x_1890_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1890_, 0, v___x_1889_);
                lean_ctor_set(v___x_1890_, 1, v_a_1790_);
                return v___x_1890_;
            }
            2 => {
                v_quotContext_1893_ = lean_ctor_get(v_a_1789_, 1);
                v_currMacroScope_1894_ = lean_ctor_get(v_a_1789_, 2);
                v_ref_1895_ = lean_ctor_get(v_a_1789_, 5);
                v___x_1896_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66;
                v___x_1897_ = 0;
                v___x_1898_ = l_Lean_mkCIdentFrom(v_ref_1895_, v___x_1896_, v___x_1897_);
                v___x_1899_ = l_Lean_TSyntax_getId(v_kind_1798_);
                lean_inc(v_kind_1798_);
                v___x_1900_ = l_Lake_Name_quoteFrom(v_kind_1798_, v___x_1899_, v___x_1897_);
                v___x_1901_ = l_Lean_SourceInfo_fromRef(v_ref_1895_, v___x_1897_);
                v___x_1902_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_1903_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_1904_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_1892_) == 1 {
                    v_val_1905_ = lean_ctor_get(v___y_1892_, 0);
                    lean_inc(v_val_1905_);
                    lean_dec_ref_known(v___y_1892_, 1);
                    v___x_1906_ = l_Array_mkArray1___redArg(v_val_1905_);
                    v___y_1802_ = v_currMacroScope_1894_;
                    v___y_1803_ = v___x_1900_;
                    v___y_1804_ = v___x_1903_;
                    v___y_1805_ = v___x_1901_;
                    v___y_1806_ = v___x_1904_;
                    v___y_1807_ = v___x_1898_;
                    v___y_1808_ = v___x_1902_;
                    v___y_1809_ = v_quotContext_1893_;
                    v___y_1810_ = v___x_1906_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1892_);
                    v___x_1907_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_1802_ = v_currMacroScope_1894_;
                    v___y_1803_ = v___x_1900_;
                    v___y_1804_ = v___x_1903_;
                    v___y_1805_ = v___x_1901_;
                    v___y_1806_ = v___x_1904_;
                    v___y_1807_ = v___x_1898_;
                    v___y_1808_ = v___x_1902_;
                    v___y_1809_ = v_quotContext_1893_;
                    v___y_1810_ = v___x_1907_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1913_ == 0 {
                    v___x_1915_ = v___x_1912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_val_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1892_ = v___x_1915_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___boxed(
    mut v_x_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1921_: *mut LeanObject = core::ptr::null_mut();
    v_res_1921_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(
        v_x_1918_, v_a_1919_, v_a_1920_,
    );
    lean_dec_ref(v_a_1919_);
    return v_res_1921_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5;
    v___x_2010_ = l_String_toRawSubstring_x27(v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8;
    v___x_2015_ = l_String_toRawSubstring_x27(v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16()
-> *mut LeanObject {
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    v___x_2023_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15;
    v___x_2024_ = l_String_toRawSubstring_x27(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24()
-> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23;
    v___x_2035_ = l_String_toRawSubstring_x27(v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(
    mut v___x_2044_: *mut LeanObject,
    mut v___x_2045_: *mut LeanObject,
    mut v___x_2046_: *mut LeanObject,
    mut v_fam_2047_: *mut LeanObject,
    mut v___x_2048_: *mut LeanObject,
    mut v___x_2049_: *mut LeanObject,
    mut v___x_2050_: *mut LeanObject,
    mut v___x_2051_: u8,
    mut v___y_2052_: *mut LeanObject,
    mut v_name_2053_: *mut LeanObject,
    mut v_ns_2054_: *mut LeanObject,
    mut v___x_2055_: *mut LeanObject,
    mut v___x_2056_: u8,
    mut v_tk_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___x_2059_: *mut LeanObject,
    mut v_____r_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: u8 = 0;
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2256_ = l_Lean_TSyntax_getId(v_name_2053_);
                if lean_obj_tag(v___y_2058_) == 0 {
                    v___y_2258_ = v___x_2051_;
                    state = 4;
                    continue;
                } else {
                    v___y_2258_ = v___x_2056_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                lean_inc_ref_n(v___y_2078_, 2);
                v___x_2081_ = l_Array_append___redArg(v___y_2078_, v___y_2080_);
                lean_dec_ref(v___y_2080_);
                lean_inc_n(v___y_2072_, 9);
                lean_inc_n(v___y_2065_, 53);
                v___x_2082_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2082_, 0, v___y_2065_);
                lean_ctor_set(v___x_2082_, 1, v___y_2072_);
                lean_ctor_set(v___x_2082_, 2, v___x_2081_);
                v___x_2083_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14;
                v___x_2084_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0;
                lean_inc_ref_n(v___y_2066_, 17);
                lean_inc_ref_n(v___y_2075_, 18);
                v___x_2085_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2084_);
                v___x_2086_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1;
                v___x_2087_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2087_, 0, v___y_2065_);
                lean_ctor_set(v___x_2087_, 1, v___x_2086_);
                v___x_2088_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2;
                v___x_2089_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2088_);
                v___x_2090_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15;
                v___x_2091_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2090_);
                v___x_2092_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2092_, 0, v___y_2065_);
                lean_ctor_set(v___x_2092_, 1, v___y_2072_);
                lean_ctor_set(v___x_2092_, 2, v___y_2078_);
                lean_inc_ref_n(v___x_2092_, 23);
                v___x_2093_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2091_, v___x_2092_);
                v___x_2094_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3;
                v___x_2095_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4;
                v___x_2096_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2094_, v___x_2095_);
                v___x_2097_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6);
                v___x_2098_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7;
                lean_inc_n(v___y_2064_, 5);
                lean_inc_n(v___y_2068_, 5);
                v___x_2099_ = l_Lean_addMacroScope(v___y_2068_, v___x_2098_, v___y_2064_);
                v___x_2100_ = lean_box(0);
                v___x_2101_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2101_, 0, v___y_2065_);
                lean_ctor_set(v___x_2101_, 1, v___x_2097_);
                lean_ctor_set(v___x_2101_, 2, v___x_2099_);
                lean_ctor_set(v___x_2101_, 3, v___x_2100_);
                lean_inc(v___x_2096_);
                v___x_2102_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2096_, v___x_2101_, v___x_2092_);
                lean_inc_n(v___x_2093_, 2);
                lean_inc(v___x_2089_);
                v___x_2103_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2089_, v___x_2093_, v___x_2102_);
                v___x_2104_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_2105_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2105_, 0, v___y_2065_);
                lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                v___x_2106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9);
                v___x_2107_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10;
                v___x_2108_ = l_Lean_addMacroScope(v___y_2068_, v___x_2107_, v___y_2064_);
                v___x_2109_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2109_, 0, v___y_2065_);
                lean_ctor_set(v___x_2109_, 1, v___x_2106_);
                lean_ctor_set(v___x_2109_, 2, v___x_2108_);
                lean_ctor_set(v___x_2109_, 3, v___x_2100_);
                v___x_2110_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2096_, v___x_2109_, v___x_2092_);
                v___x_2111_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2089_, v___x_2093_, v___x_2110_);
                v___x_2112_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2103_,
                    v___x_2105_,
                    v___x_2111_,
                );
                v___x_2113_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60;
                v___x_2114_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___y_2065_);
                lean_ctor_set(v___x_2114_, 1, v___x_2113_);
                v___x_2115_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2085_,
                    v___x_2087_,
                    v___x_2112_,
                    v___x_2114_,
                );
                v___x_2116_ = l_Lean_Syntax_node1(v___y_2065_, v___y_2072_, v___x_2115_);
                v___x_2117_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                lean_inc_ref_n(v___y_2076_, 7);
                v___x_2118_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2117_);
                v___x_2119_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2119_, 0, v___y_2065_);
                lean_ctor_set(v___x_2119_, 1, v___x_2117_);
                v___x_2120_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2118_, v___x_2119_);
                v___x_2121_ = l_Lean_Syntax_node1(v___y_2065_, v___y_2072_, v___x_2120_);
                lean_inc(v___x_2121_);
                lean_inc_n(v___y_2074_, 2);
                v___x_2122_ = l_Lean_Syntax_node7(
                    v___y_2065_,
                    v___y_2074_,
                    v___x_2082_,
                    v___x_2116_,
                    v___x_2121_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                );
                v___x_2123_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11;
                v___x_2124_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2123_);
                v___x_2125_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12;
                v___x_2126_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2126_, 0, v___y_2065_);
                lean_ctor_set(v___x_2126_, 1, v___x_2125_);
                v___x_2127_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13;
                v___x_2128_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2127_);
                v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2044_);
                v___x_2130_ = lean_box(2);
                v___x_2131_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2131_, 0, v___x_2130_);
                lean_ctor_set(v___x_2131_, 1, v___y_2072_);
                lean_ctor_set(v___x_2131_, 2, v___x_2129_);
                v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2045_);
                v___x_2133_ = lean_array_push(v___x_2132_, v___y_2070_);
                v___x_2134_ = lean_array_push(v___x_2133_, v___x_2131_);
                v___x_2135_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2135_, 0, v___x_2130_);
                lean_ctor_set(v___x_2135_, 1, v___x_2128_);
                lean_ctor_set(v___x_2135_, 2, v___x_2134_);
                v___x_2136_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14;
                v___x_2137_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2136_);
                v___x_2138_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2137_, v___x_2092_, v___x_2092_);
                v___x_2139_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31;
                v___x_2140_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2139_);
                v___x_2141_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_2142_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2142_, 0, v___y_2065_);
                lean_ctor_set(v___x_2142_, 1, v___x_2141_);
                v___x_2143_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62;
                v___x_2144_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63;
                v___x_2145_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2143_, v___x_2144_);
                v___x_2146_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2145_, v___x_2092_, v___x_2092_);
                lean_inc(v___x_2146_);
                lean_inc_n(v___y_2079_, 2);
                lean_inc_ref_n(v___x_2142_, 2);
                lean_inc(v___x_2140_);
                v___x_2147_ = l_Lean_Syntax_node4(
                    v___y_2065_,
                    v___x_2140_,
                    v___x_2142_,
                    v___y_2079_,
                    v___x_2146_,
                    v___x_2092_,
                );
                v___x_2148_ = l_Lean_Syntax_node5(
                    v___y_2065_,
                    v___x_2124_,
                    v___x_2126_,
                    v___x_2135_,
                    v___x_2138_,
                    v___x_2147_,
                    v___x_2092_,
                );
                lean_inc_n(v___y_2069_, 2);
                v___x_2149_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___y_2069_, v___x_2122_, v___x_2148_);
                v___x_2150_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69;
                lean_inc_ref_n(v___x_2046_, 2);
                v___x_2151_ = l_Lean_Name_mkStr2(v___x_2046_, v___x_2150_);
                v___x_2152_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2153_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2153_, 0, v___y_2065_);
                lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                v___x_2154_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2155_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2155_, 0, v___y_2065_);
                lean_ctor_set(v___x_2155_, 1, v___x_2154_);
                lean_inc_n(v___x_2048_, 2);
                lean_inc_ref(v___x_2155_);
                v___x_2156_ = l_Lean_Syntax_node8(
                    v___y_2065_,
                    v___x_2151_,
                    v___x_2092_,
                    v___x_2153_,
                    v___y_2073_,
                    v___x_2155_,
                    v_fam_2047_,
                    v___y_2079_,
                    v___x_2142_,
                    v___x_2048_,
                );
                v___x_2157_ = l_Lean_Syntax_node7(
                    v___y_2065_,
                    v___y_2074_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2121_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                );
                v___x_2158_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_2159_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2158_);
                v___x_2160_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2160_, 0, v___y_2065_);
                lean_ctor_set(v___x_2160_, 1, v___x_2158_);
                v___x_2161_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17;
                v___x_2162_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2161_);
                v___x_2163_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19;
                v___x_2164_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2163_);
                v___x_2165_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21;
                v___x_2166_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2165_);
                v___x_2167_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15;
                v___x_2168_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
                v___x_2169_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17;
                v___x_2170_ = l_Lean_addMacroScope(v___y_2068_, v___x_2169_, v___y_2064_);
                v___x_2171_ = l_Lean_Name_mkStr2(v___x_2046_, v___x_2167_);
                lean_inc(v___x_2171_);
                v___x_2172_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2172_, 0, v___x_2171_);
                lean_ctor_set(v___x_2172_, 1, v___x_2100_);
                v___x_2173_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2173_, 0, v___x_2171_);
                v___x_2174_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2174_, 0, v___x_2173_);
                lean_ctor_set(v___x_2174_, 1, v___x_2100_);
                v___x_2175_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v___x_2172_);
                lean_ctor_set(v___x_2175_, 1, v___x_2174_);
                v___x_2176_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2176_, 0, v___y_2065_);
                lean_ctor_set(v___x_2176_, 1, v___x_2168_);
                lean_ctor_set(v___x_2176_, 2, v___x_2170_);
                lean_ctor_set(v___x_2176_, 3, v___x_2175_);
                lean_inc_ref(v___x_2049_);
                v___x_2177_ = l_String_toRawSubstring_x27(v___x_2049_);
                v___x_2178_ = l_Lean_Name_mkStr1(v___x_2049_);
                v___x_2179_ = l_Lean_addMacroScope(v___y_2068_, v___x_2178_, v___y_2064_);
                v___x_2180_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2180_, 0, v___x_2050_);
                lean_ctor_set(v___x_2180_, 1, v___x_2100_);
                v___x_2181_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2181_, 0, v___x_2180_);
                lean_ctor_set(v___x_2181_, 1, v___x_2100_);
                v___x_2182_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2182_, 0, v___y_2065_);
                lean_ctor_set(v___x_2182_, 1, v___x_2177_);
                lean_ctor_set(v___x_2182_, 2, v___x_2179_);
                lean_ctor_set(v___x_2182_, 3, v___x_2181_);
                v___x_2183_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18;
                v___x_2184_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2183_);
                v___x_2185_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19;
                v___x_2186_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2185_);
                v___x_2187_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2188_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2188_, 0, v___y_2065_);
                lean_ctor_set(v___x_2188_, 1, v___x_2187_);
                v___x_2189_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2190_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_2191_ = lean_box(0);
                v___x_2192_ = l_Lean_addMacroScope(v___y_2068_, v___x_2191_, v___y_2064_);
                v___x_2193_ = l_Lean_Name_mkStr1(v___x_2046_);
                v___x_2194_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2194_, 0, v___x_2193_);
                v___x_2195_ = l_Lean_Name_mkStr1(v___y_2075_);
                v___x_2196_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2196_, 0, v___x_2195_);
                v___x_2197_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2197_, 0, v___x_2196_);
                lean_ctor_set(v___x_2197_, 1, v___x_2100_);
                v___x_2198_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2198_, 0, v___x_2194_);
                lean_ctor_set(v___x_2198_, 1, v___x_2197_);
                v___x_2199_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2199_, 0, v___y_2065_);
                lean_ctor_set(v___x_2199_, 1, v___x_2190_);
                lean_ctor_set(v___x_2199_, 2, v___x_2192_);
                lean_ctor_set(v___x_2199_, 3, v___x_2198_);
                v___x_2200_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2189_, v___x_2199_);
                v___x_2201_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2186_, v___x_2188_, v___x_2200_);
                v___x_2202_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26;
                v___x_2203_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27;
                v___x_2204_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2204_, 0, v___y_2065_);
                lean_ctor_set(v___x_2204_, 1, v___x_2203_);
                v___x_2205_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2202_,
                    v___y_2077_,
                    v___x_2204_,
                    v___y_2071_,
                );
                v___x_2206_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_2207_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2207_, 0, v___y_2065_);
                lean_ctor_set(v___x_2207_, 1, v___x_2206_);
                lean_inc_ref(v___x_2207_);
                lean_inc(v___x_2201_);
                lean_inc(v___x_2184_);
                v___x_2208_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2184_,
                    v___x_2201_,
                    v___x_2205_,
                    v___x_2207_,
                );
                lean_inc_ref(v___x_2182_);
                v___x_2209_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2182_,
                    v___x_2208_,
                    v___x_2048_,
                );
                lean_inc_ref(v___x_2176_);
                lean_inc(v___x_2166_);
                v___x_2210_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2166_, v___x_2176_, v___x_2209_);
                v___x_2211_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2164_, v___x_2155_, v___x_2210_);
                v___x_2212_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2162_, v___x_2092_, v___x_2211_);
                v___x_2213_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29;
                v___x_2214_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2213_);
                v___x_2215_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2215_, 0, v___y_2065_);
                lean_ctor_set(v___x_2215_, 1, v___x_2213_);
                v___x_2216_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2182_,
                    v___y_2079_,
                    v___x_2048_,
                );
                v___x_2217_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2166_, v___x_2176_, v___x_2216_);
                v___x_2218_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2184_,
                    v___x_2201_,
                    v___x_2217_,
                    v___x_2207_,
                );
                v___x_2219_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2214_, v___x_2215_, v___x_2218_);
                v___x_2220_ = l_Lean_Syntax_node4(
                    v___y_2065_,
                    v___x_2140_,
                    v___x_2142_,
                    v___x_2219_,
                    v___x_2146_,
                    v___x_2092_,
                );
                v___x_2221_ = l_Lean_Syntax_node6(
                    v___y_2065_,
                    v___x_2159_,
                    v___x_2093_,
                    v___x_2160_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2212_,
                    v___x_2220_,
                );
                v___x_2222_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___y_2069_, v___x_2157_, v___x_2221_);
                v___x_2223_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2149_,
                    v___x_2156_,
                    v___x_2222_,
                );
                v___x_2224_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2224_, 0, v___x_2223_);
                lean_ctor_set(v___x_2224_, 1, v___y_2067_);
                return v___x_2224_;
            }
            2 => {
                v_quotContext_2233_ = lean_ctor_get(v___y_2231_, 1);
                v_currMacroScope_2234_ = lean_ctor_get(v___y_2231_, 2);
                v_ref_2235_ = lean_ctor_get(v___y_2231_, 5);
                v___x_2236_ = l_Lean_SourceInfo_fromRef(v_ref_2235_, v___x_2051_);
                v___x_2237_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2238_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3;
                v___x_2239_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4;
                v___x_2240_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5;
                v___x_2241_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_2242_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_2243_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_2052_) == 1 {
                    v_val_2244_ = lean_ctor_get(v___y_2052_, 0);
                    lean_inc(v_val_2244_);
                    lean_dec_ref_known(v___y_2052_, 1);
                    v___x_2245_ = l_Array_mkArray1___redArg(v_val_2244_);
                    v___y_2064_ = v_currMacroScope_2234_;
                    v___y_2065_ = v___x_2236_;
                    v___y_2066_ = v___x_2239_;
                    v___y_2067_ = v___y_2232_;
                    v___y_2068_ = v_quotContext_2233_;
                    v___y_2069_ = v___x_2241_;
                    v___y_2070_ = v_id_2230_;
                    v___y_2071_ = v___y_2226_;
                    v___y_2072_ = v___x_2237_;
                    v___y_2073_ = v___y_2227_;
                    v___y_2074_ = v___x_2242_;
                    v___y_2075_ = v___x_2238_;
                    v___y_2076_ = v___x_2240_;
                    v___y_2077_ = v___y_2228_;
                    v___y_2078_ = v___x_2243_;
                    v___y_2079_ = v___y_2229_;
                    v___y_2080_ = v___x_2245_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2052_);
                    v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2044_);
                    v___y_2064_ = v_currMacroScope_2234_;
                    v___y_2065_ = v___x_2236_;
                    v___y_2066_ = v___x_2239_;
                    v___y_2067_ = v___y_2232_;
                    v___y_2068_ = v_quotContext_2233_;
                    v___y_2069_ = v___x_2241_;
                    v___y_2070_ = v_id_2230_;
                    v___y_2071_ = v___y_2226_;
                    v___y_2072_ = v___x_2237_;
                    v___y_2073_ = v___y_2227_;
                    v___y_2074_ = v___x_2242_;
                    v___y_2075_ = v___x_2238_;
                    v___y_2076_ = v___x_2240_;
                    v___y_2077_ = v___y_2228_;
                    v___y_2078_ = v___x_2243_;
                    v___y_2079_ = v___y_2229_;
                    v___y_2080_ = v___x_2246_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2252_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30;
                v___x_2253_ = l_Lean_Macro_throwErrorAt___redArg(
                    v_name_2053_,
                    v___x_2252_,
                    v___y_2061_,
                    v___y_2062_,
                );
                lean_dec(v_name_2053_);
                if lean_obj_tag(v___x_2253_) == 0 {
                    v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
                    lean_inc(v_a_2254_);
                    v_a_2255_ = lean_ctor_get(v___x_2253_, 1);
                    lean_inc(v_a_2255_);
                    lean_dec_ref_known(v___x_2253_, 2);
                    v___y_2226_ = v___y_2248_;
                    v___y_2227_ = v___y_2249_;
                    v___y_2228_ = v___y_2250_;
                    v___y_2229_ = v___y_2251_;
                    v_id_2230_ = v_a_2254_;
                    v___y_2231_ = v___y_2061_;
                    v___y_2232_ = v_a_2255_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_2251_);
                    lean_dec(v___y_2250_);
                    lean_dec(v___y_2249_);
                    lean_dec(v___y_2248_);
                    lean_dec(v___y_2052_);
                    lean_dec(v___x_2050_);
                    lean_dec_ref(v___x_2049_);
                    lean_dec(v___x_2048_);
                    lean_dec(v_fam_2047_);
                    lean_dec_ref(v___x_2046_);
                    return v___x_2253_;
                }
            }
            4 => {
                lean_inc_n(v___x_2256_, 2);
                lean_inc(v_name_2053_);
                v___x_2259_ = l_Lake_Name_quoteFrom(v_name_2053_, v___x_2256_, v___y_2258_);
                lean_inc(v___x_2055_);
                v___x_2260_ = l_Lake_Name_quoteFrom(v_ns_2054_, v___x_2055_, v___x_2056_);
                v___x_2261_ = l_Lean_Name_append(v___x_2055_, v___x_2256_);
                lean_inc(v___x_2261_);
                v___x_2262_ = l_Lean_mkIdentFrom(v_tk_2057_, v___x_2261_, v___x_2056_);
                v___x_2263_ = l_Lake_Name_quoteFrom(v_tk_2057_, v___x_2261_, v___x_2051_);
                if lean_obj_tag(v___y_2058_) == 1 {
                    lean_dec(v___x_2256_);
                    lean_dec(v_name_2053_);
                    v_val_2264_ = lean_ctor_get(v___y_2058_, 0);
                    v___x_2265_ = l_Lean_Syntax_getArg(v_val_2264_, v___x_2044_);
                    v___x_2266_ = l_Lean_Syntax_getId(v___x_2265_);
                    v___x_2267_ = l_Lean_Name_append(v___x_2059_, v___x_2266_);
                    v___x_2268_ = l_Lean_mkIdentFrom(v___x_2265_, v___x_2267_, v___x_2056_);
                    lean_dec(v___x_2265_);
                    v___y_2226_ = v___x_2259_;
                    v___y_2227_ = v___x_2262_;
                    v___y_2228_ = v___x_2260_;
                    v___y_2229_ = v___x_2263_;
                    v_id_2230_ = v___x_2268_;
                    v___y_2231_ = v___y_2061_;
                    v___y_2232_ = v___y_2062_;
                    state = 2;
                    continue;
                } else {
                    if lean_obj_tag(v___x_2256_) == 1 {
                        v_pre_2269_ = lean_ctor_get(v___x_2256_, 0);
                        lean_inc(v_pre_2269_);
                        if lean_obj_tag(v_pre_2269_) == 0 {
                            v_str_2270_ = lean_ctor_get(v___x_2256_, 1);
                            lean_inc_ref(v_str_2270_);
                            lean_dec_ref_known(v___x_2256_, 2);
                            v___x_2271_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31;
                            v___x_2272_ = lean_string_append(v_str_2270_, v___x_2271_);
                            v___x_2273_ = l_Lean_Name_str___override(v___x_2059_, v___x_2272_);
                            v___x_2274_ =
                                l_Lean_mkIdentFrom(v_name_2053_, v___x_2273_, v___x_2056_);
                            lean_dec(v_name_2053_);
                            v___y_2226_ = v___x_2259_;
                            v___y_2227_ = v___x_2262_;
                            v___y_2228_ = v___x_2260_;
                            v___y_2229_ = v___x_2263_;
                            v_id_2230_ = v___x_2274_;
                            v___y_2231_ = v___y_2061_;
                            v___y_2232_ = v___y_2062_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_2256_, 2);
                            lean_dec(v_pre_2269_);
                            lean_dec(v___x_2059_);
                            v___y_2248_ = v___x_2259_;
                            v___y_2249_ = v___x_2262_;
                            v___y_2250_ = v___x_2260_;
                            v___y_2251_ = v___x_2263_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2256_);
                        lean_dec(v___x_2059_);
                        v___y_2248_ = v___x_2259_;
                        v___y_2249_ = v___x_2262_;
                        v___y_2250_ = v___x_2260_;
                        v___y_2251_ = v___x_2263_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = *_args.add(0);
    let mut v___x_2276_: *mut LeanObject = *_args.add(1);
    let mut v___x_2277_: *mut LeanObject = *_args.add(2);
    let mut v_fam_2278_: *mut LeanObject = *_args.add(3);
    let mut v___x_2279_: *mut LeanObject = *_args.add(4);
    let mut v___x_2280_: *mut LeanObject = *_args.add(5);
    let mut v___x_2281_: *mut LeanObject = *_args.add(6);
    let mut v___x_2282_: *mut LeanObject = *_args.add(7);
    let mut v___y_2283_: *mut LeanObject = *_args.add(8);
    let mut v_name_2284_: *mut LeanObject = *_args.add(9);
    let mut v_ns_2285_: *mut LeanObject = *_args.add(10);
    let mut v___x_2286_: *mut LeanObject = *_args.add(11);
    let mut v___x_2287_: *mut LeanObject = *_args.add(12);
    let mut v_tk_2288_: *mut LeanObject = *_args.add(13);
    let mut v___y_2289_: *mut LeanObject = *_args.add(14);
    let mut v___x_2290_: *mut LeanObject = *_args.add(15);
    let mut v_____r_2291_: *mut LeanObject = *_args.add(16);
    let mut v___y_2292_: *mut LeanObject = *_args.add(17);
    let mut v___y_2293_: *mut LeanObject = *_args.add(18);
    let mut v___x_12982__boxed_2294_: u8 = 0;
    let mut v___x_12985__boxed_2295_: u8 = 0;
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_12982__boxed_2294_ = (lean_unbox(v___x_2282_) as u8);
    v___x_12985__boxed_2295_ = (lean_unbox(v___x_2287_) as u8);
    v_res_2296_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(
            v___x_2275_,
            v___x_2276_,
            v___x_2277_,
            v_fam_2278_,
            v___x_2279_,
            v___x_2280_,
            v___x_2281_,
            v___x_12982__boxed_2294_,
            v___y_2283_,
            v_name_2284_,
            v_ns_2285_,
            v___x_2286_,
            v___x_12985__boxed_2295_,
            v_tk_2288_,
            v___y_2289_,
            v___x_2290_,
            v_____r_2291_,
            v___y_2292_,
            v___y_2293_,
        );
    lean_dec_ref(v___y_2292_);
    lean_dec(v___y_2289_);
    lean_dec(v___x_2276_);
    lean_dec(v___x_2275_);
    return v_res_2296_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(
    mut v_x_2304_: *mut LeanObject,
    mut v_a_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut v_a_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ns_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v_fam_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2381_: u8 = 0;
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_a_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v___y_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2327_ = l_Lake_dataTypeDecl___closed__0;
                v___x_2328_ = l_Lake_builtinFacetCommand___closed__1;
                lean_inc(v_x_2304_);
                v___x_2329_ = l_Lean_Syntax_isOfKind(v_x_2304_, v___x_2328_);
                if v___x_2329_ == 0 {
                    lean_dec(v_x_2304_);
                    v___x_2330_ = lean_box(1);
                    v___x_2331_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2331_, 0, v___x_2330_);
                    lean_ctor_set(v___x_2331_, 1, v_a_2306_);
                    return v___x_2331_;
                } else {
                    v___x_2332_ = lean_unsigned_to_nat(0);
                    v___x_2333_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2332_);
                    v___x_2334_ = lean_unsigned_to_nat(1);
                    v_tk_2335_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2334_);
                    v___x_2336_ = lean_unsigned_to_nat(2);
                    v___x_2337_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2336_);
                    v___x_2338_ = lean_unsigned_to_nat(3);
                    v_name_2339_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2338_);
                    v___x_2340_ = lean_unsigned_to_nat(5);
                    v_ns_2341_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2340_);
                    v___x_2342_ = lean_unsigned_to_nat(7);
                    v___x_2343_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2342_);
                    lean_dec(v_x_2304_);
                    v___x_2414_ = l_Lean_Syntax_getOptional_x3f(v___x_2337_);
                    lean_dec(v___x_2337_);
                    if lean_obj_tag(v___x_2414_) == 0 {
                        v___x_2415_ = lean_box(0);
                        v___y_2403_ = v___x_2415_;
                        state = 11;
                        continue;
                    } else {
                        v_val_2416_ = lean_ctor_get(v___x_2414_, 0);
                        v_isSharedCheck_2423_ = (!lean_is_exclusive(v___x_2414_)) as u8;
                        if v_isSharedCheck_2423_ == 0 {
                            v___x_2418_ = v___x_2414_;
                            v_isShared_2419_ = v_isSharedCheck_2423_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_val_2416_);
                            lean_dec(v___x_2414_);
                            v___x_2418_ = lean_box(0);
                            v_isShared_2419_ = v_isSharedCheck_2423_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2308_) == 0 {
                    v_a_2309_ = lean_ctor_get(v___y_2308_, 0);
                    v_a_2310_ = lean_ctor_get(v___y_2308_, 1);
                    v_isSharedCheck_2317_ = (!lean_is_exclusive(v___y_2308_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2312_ = v___y_2308_;
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2310_);
                        lean_inc(v_a_2309_);
                        lean_dec(v___y_2308_);
                        v___x_2312_ = lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2318_ = lean_ctor_get(v___y_2308_, 0);
                    v_a_2319_ = lean_ctor_get(v___y_2308_, 1);
                    v_isSharedCheck_2326_ = (!lean_is_exclusive(v___y_2308_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___y_2308_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2319_);
                        lean_inc(v_a_2318_);
                        lean_dec(v___y_2308_);
                        v___x_2321_ = lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2313_ == 0 {
                    v___x_2315_ = v___x_2312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2309_);
                    lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2315_;
            }
            4 => {
                if v_isShared_2322_ == 0 {
                    v___x_2324_ = v___x_2321_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2318_);
                    lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_a_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2324_;
            }
            6 => {
                v_methods_2347_ = lean_ctor_get(v_a_2305_, 0);
                v_quotContext_2348_ = lean_ctor_get(v_a_2305_, 1);
                v_currMacroScope_2349_ = lean_ctor_get(v_a_2305_, 2);
                v_currRecDepth_2350_ = lean_ctor_get(v_a_2305_, 3);
                v_maxRecDepth_2351_ = lean_ctor_get(v_a_2305_, 4);
                v_ref_2352_ = lean_ctor_get(v_a_2305_, 5);
                v___x_2353_ = l_Lean_TSyntax_getId(v_ns_2341_);
                v_ref_2354_ = l_Lean_replaceRef(v_tk_2335_, v_ref_2352_);
                lean_inc(v_maxRecDepth_2351_);
                lean_inc(v_currRecDepth_2350_);
                lean_inc(v_currMacroScope_2349_);
                lean_inc(v_quotContext_2348_);
                lean_inc(v_methods_2347_);
                v___x_2355_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2355_, 0, v_methods_2347_);
                lean_ctor_set(v___x_2355_, 1, v_quotContext_2348_);
                lean_ctor_set(v___x_2355_, 2, v_currMacroScope_2349_);
                lean_ctor_set(v___x_2355_, 3, v_currRecDepth_2350_);
                lean_ctor_set(v___x_2355_, 4, v_maxRecDepth_2351_);
                lean_ctor_set(v___x_2355_, 5, v_ref_2354_);
                lean_inc(v___x_2353_);
                v___x_2356_ = l_Lean_Macro_resolveNamespace(v___x_2353_, v___x_2355_, v_a_2306_);
                if lean_obj_tag(v___x_2356_) == 0 {
                    v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
                    lean_inc(v_a_2357_);
                    if lean_obj_tag(v_a_2357_) == 1 {
                        v_a_2358_ = lean_ctor_get(v___x_2356_, 1);
                        lean_inc(v_a_2358_);
                        lean_dec_ref_known(v___x_2356_, 2);
                        v_head_2359_ = lean_ctor_get(v_a_2357_, 0);
                        lean_inc(v_head_2359_);
                        lean_dec_ref_known(v_a_2357_, 2);
                        v___x_2360_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0;
                        v___x_2361_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1;
                        v___x_2362_ = 0;
                        v_fam_2363_ = l_Lean_mkCIdentFrom(v_tk_2335_, v___x_2361_, v___x_2362_);
                        v___x_2364_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(
                            v_head_2359_,
                        );
                        lean_dec(v_head_2359_);
                        v___x_2365_ = l_Lean_Name_isAnonymous(v___x_2364_);
                        if v___x_2365_ == 0 {
                            v___x_2366_ = lean_box(0);
                            v___x_2367_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_2332_, v___x_2336_, v___x_2327_, v_fam_2363_, v___x_2343_, v___x_2360_, v___x_2361_, v___x_2362_, v___y_2346_, v_name_2339_, v_ns_2341_, v___x_2364_, v___x_2329_, v_tk_2335_, v___y_2345_, v___x_2353_, v___x_2366_, v___x_2355_, v_a_2358_);
                            lean_dec_ref_known(v___x_2355_, 6);
                            lean_dec(v___y_2345_);
                            v___y_2308_ = v___x_2367_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2368_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2;
                            lean_inc(v___x_2353_);
                            v___x_2369_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2353_,
                                    v___x_2365_,
                                );
                            v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
                            lean_dec_ref(v___x_2369_);
                            v___x_2371_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3;
                            v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
                            v___x_2373_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_ns_2341_,
                                v___x_2372_,
                                v___x_2355_,
                                v_a_2358_,
                            );
                            if lean_obj_tag(v___x_2373_) == 0 {
                                v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
                                lean_inc(v_a_2374_);
                                v_a_2375_ = lean_ctor_get(v___x_2373_, 1);
                                lean_inc(v_a_2375_);
                                lean_dec_ref_known(v___x_2373_, 2);
                                v___x_2376_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_2332_, v___x_2336_, v___x_2327_, v_fam_2363_, v___x_2343_, v___x_2360_, v___x_2361_, v___x_2362_, v___y_2346_, v_name_2339_, v_ns_2341_, v___x_2364_, v___x_2329_, v_tk_2335_, v___y_2345_, v___x_2353_, v_a_2374_, v___x_2355_, v_a_2375_);
                                lean_dec_ref_known(v___x_2355_, 6);
                                lean_dec(v___y_2345_);
                                v___y_2308_ = v___x_2376_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_2364_);
                                lean_dec(v_fam_2363_);
                                lean_dec_ref_known(v___x_2355_, 6);
                                lean_dec(v___x_2353_);
                                lean_dec(v___y_2346_);
                                lean_dec(v___y_2345_);
                                lean_dec(v___x_2343_);
                                lean_dec(v_ns_2341_);
                                lean_dec(v_name_2339_);
                                lean_dec(v_tk_2335_);
                                v_a_2377_ = lean_ctor_get(v___x_2373_, 0);
                                v_a_2378_ = lean_ctor_get(v___x_2373_, 1);
                                v_isSharedCheck_2385_ = (!lean_is_exclusive(v___x_2373_)) as u8;
                                if v_isSharedCheck_2385_ == 0 {
                                    v___x_2380_ = v___x_2373_;
                                    v_isShared_2381_ = v_isSharedCheck_2385_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2378_);
                                    lean_inc(v_a_2377_);
                                    lean_dec(v___x_2373_);
                                    v___x_2380_ = lean_box(0);
                                    v_isShared_2381_ = v_isSharedCheck_2385_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2357_);
                        lean_dec(v___y_2346_);
                        lean_dec(v___y_2345_);
                        lean_dec(v___x_2343_);
                        lean_dec(v_name_2339_);
                        lean_dec(v_tk_2335_);
                        v_a_2386_ = lean_ctor_get(v___x_2356_, 1);
                        lean_inc(v_a_2386_);
                        lean_dec_ref_known(v___x_2356_, 2);
                        v___x_2387_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4;
                        v___x_2388_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2353_,
                                v___x_2329_,
                            );
                        v___x_2389_ = lean_string_append(v___x_2387_, v___x_2388_);
                        lean_dec_ref(v___x_2388_);
                        v___x_2390_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3;
                        v___x_2391_ = lean_string_append(v___x_2389_, v___x_2390_);
                        v___x_2392_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_ns_2341_,
                            v___x_2391_,
                            v___x_2355_,
                            v_a_2386_,
                        );
                        lean_dec_ref_known(v___x_2355_, 6);
                        lean_dec(v_ns_2341_);
                        v___y_2308_ = v___x_2392_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2355_, 6);
                    lean_dec(v___x_2353_);
                    lean_dec(v___y_2346_);
                    lean_dec(v___y_2345_);
                    lean_dec(v___x_2343_);
                    lean_dec(v_ns_2341_);
                    lean_dec(v_name_2339_);
                    lean_dec(v_tk_2335_);
                    v_a_2393_ = lean_ctor_get(v___x_2356_, 0);
                    v_a_2394_ = lean_ctor_get(v___x_2356_, 1);
                    v_isSharedCheck_2401_ = (!lean_is_exclusive(v___x_2356_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v___x_2396_ = v___x_2356_;
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2394_);
                        lean_inc(v_a_2393_);
                        lean_dec(v___x_2356_);
                        v___x_2396_ = lean_box(0);
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2381_ == 0 {
                    v___x_2383_ = v___x_2380_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2377_);
                    lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2378_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2383_;
            }
            9 => {
                if v_isShared_2397_ == 0 {
                    v___x_2399_ = v___x_2396_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2393_);
                    lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_a_2394_);
                    v___x_2399_ = v_reuseFailAlloc_2400_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2399_;
            }
            11 => {
                v___x_2404_ = l_Lean_Syntax_getOptional_x3f(v___x_2333_);
                lean_dec(v___x_2333_);
                if lean_obj_tag(v___x_2404_) == 0 {
                    v___x_2405_ = lean_box(0);
                    v___y_2345_ = v___y_2403_;
                    v___y_2346_ = v___x_2405_;
                    state = 6;
                    continue;
                } else {
                    v_val_2406_ = lean_ctor_get(v___x_2404_, 0);
                    v_isSharedCheck_2413_ = (!lean_is_exclusive(v___x_2404_)) as u8;
                    if v_isSharedCheck_2413_ == 0 {
                        v___x_2408_ = v___x_2404_;
                        v_isShared_2409_ = v_isSharedCheck_2413_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_val_2406_);
                        lean_dec(v___x_2404_);
                        v___x_2408_ = lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2413_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2409_ == 0 {
                    v___x_2411_ = v___x_2408_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_val_2406_);
                    v___x_2411_ = v_reuseFailAlloc_2412_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2345_ = v___y_2403_;
                v___y_2346_ = v___x_2411_;
                state = 6;
                continue;
            }
            14 => {
                if v_isShared_2419_ == 0 {
                    v___x_2421_ = v___x_2418_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_val_2416_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_2403_ = v___x_2421_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___boxed(
    mut v_x_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
    mut v_a_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2427_: *mut LeanObject = core::ptr::null_mut();
    v_res_2427_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(
        v_x_2424_, v_a_2425_, v_a_2426_,
    );
    lean_dec_ref(v_a_2425_);
    return v_res_2427_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(
    mut v_x_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v_fam_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kindLit_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nameLit_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facetLit_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2506_ = l_Lake_facetDataDecl___closed__1;
                lean_inc(v_x_2503_);
                v___x_2507_ = l_Lean_Syntax_isOfKind(v_x_2503_, v___x_2506_);
                if v___x_2507_ == 0 {
                    lean_dec(v_x_2503_);
                    v___x_2508_ = lean_box(1);
                    v___x_2509_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2509_, 0, v___x_2508_);
                    lean_ctor_set(v___x_2509_, 1, v_a_2505_);
                    return v___x_2509_;
                } else {
                    v___x_2510_ = lean_unsigned_to_nat(0);
                    v___x_2511_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2510_);
                    v___x_2512_ = lean_unsigned_to_nat(1);
                    v_tk_2513_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2512_);
                    v___x_2514_ = lean_unsigned_to_nat(2);
                    v_kind_2515_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2514_);
                    v___x_2516_ = lean_unsigned_to_nat(3);
                    v_name_2517_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2516_);
                    v___x_2518_ = lean_unsigned_to_nat(5);
                    v___x_2519_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2518_);
                    lean_dec(v_x_2503_);
                    v___x_2635_ = l_Lean_Syntax_getOptional_x3f(v___x_2511_);
                    lean_dec(v___x_2511_);
                    if lean_obj_tag(v___x_2635_) == 0 {
                        v___x_2636_ = lean_box(0);
                        v___y_2612_ = v___x_2636_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2637_ = lean_ctor_get(v___x_2635_, 0);
                        v_isSharedCheck_2644_ = (!lean_is_exclusive(v___x_2635_)) as u8;
                        if v_isSharedCheck_2644_ == 0 {
                            v___x_2639_ = v___x_2635_;
                            v_isShared_2640_ = v_isSharedCheck_2644_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2637_);
                            lean_dec(v___x_2635_);
                            v___x_2639_ = lean_box(0);
                            v_isShared_2640_ = v_isSharedCheck_2644_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_2526_, 2);
                v___x_2535_ = l_Array_append___redArg(v___y_2526_, v___y_2534_);
                lean_dec_ref(v___y_2534_);
                lean_inc_n(v___y_2531_, 6);
                lean_inc_n(v___y_2528_, 35);
                v___x_2536_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2536_, 0, v___y_2528_);
                lean_ctor_set(v___x_2536_, 1, v___y_2531_);
                lean_ctor_set(v___x_2536_, 2, v___x_2535_);
                v___x_2537_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2538_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2538_, 0, v___y_2528_);
                lean_ctor_set(v___x_2538_, 1, v___x_2537_);
                v___x_2539_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2540_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2540_, 0, v___y_2528_);
                lean_ctor_set(v___x_2540_, 1, v___x_2539_);
                v___x_2541_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_2542_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2542_, 0, v___y_2528_);
                lean_ctor_set(v___x_2542_, 1, v___x_2541_);
                lean_inc_n(v___x_2519_, 2);
                lean_inc_ref(v___x_2542_);
                lean_inc(v___y_2525_);
                lean_inc_ref(v___x_2540_);
                lean_inc(v___y_2521_);
                v___x_2543_ = l_Lean_Syntax_node8(
                    v___y_2528_,
                    v___y_2521_,
                    v___x_2536_,
                    v___x_2538_,
                    v___y_2532_,
                    v___x_2540_,
                    v___y_2522_,
                    v___y_2525_,
                    v___x_2542_,
                    v___x_2519_,
                );
                v___x_2544_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_2545_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_2546_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2546_, 0, v___y_2528_);
                lean_ctor_set(v___x_2546_, 1, v___y_2531_);
                lean_ctor_set(v___x_2546_, 2, v___y_2526_);
                v___x_2547_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                v___x_2548_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11;
                v___x_2549_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2549_, 0, v___y_2528_);
                lean_ctor_set(v___x_2549_, 1, v___x_2547_);
                v___x_2550_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2548_, v___x_2549_);
                v___x_2551_ = l_Lean_Syntax_node1(v___y_2528_, v___y_2531_, v___x_2550_);
                lean_inc_ref_n(v___x_2546_, 12);
                v___x_2552_ = l_Lean_Syntax_node7(
                    v___y_2528_,
                    v___x_2545_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2551_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2546_,
                );
                v___x_2553_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_2554_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13;
                v___x_2555_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16;
                v___x_2556_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2555_, v___x_2546_);
                v___x_2557_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2557_, 0, v___y_2528_);
                lean_ctor_set(v___x_2557_, 1, v___x_2553_);
                v___x_2558_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18;
                v___x_2559_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20;
                v___x_2560_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22;
                v___x_2561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
                v___x_2562_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17;
                lean_inc_n(v___y_2523_, 3);
                lean_inc_n(v___y_2530_, 3);
                v___x_2563_ = l_Lean_addMacroScope(v___y_2530_, v___x_2562_, v___y_2523_);
                v___x_2564_ = lean_box(0);
                v___x_2565_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4;
                v___x_2566_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2566_, 0, v___y_2528_);
                lean_ctor_set(v___x_2566_, 1, v___x_2561_);
                lean_ctor_set(v___x_2566_, 2, v___x_2563_);
                lean_ctor_set(v___x_2566_, 3, v___x_2565_);
                lean_inc_ref_n(v___y_2524_, 2);
                v___x_2567_ = l_String_toRawSubstring_x27(v___y_2524_);
                v___x_2568_ = l_Lean_Name_mkStr1(v___y_2524_);
                v___x_2569_ = l_Lean_addMacroScope(v___y_2530_, v___x_2568_, v___y_2523_);
                v___x_2570_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2570_, 0, v___y_2529_);
                lean_ctor_set(v___x_2570_, 1, v___x_2564_);
                v___x_2571_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2571_, 0, v___x_2570_);
                lean_ctor_set(v___x_2571_, 1, v___x_2564_);
                v___x_2572_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2572_, 0, v___y_2528_);
                lean_ctor_set(v___x_2572_, 1, v___x_2567_);
                lean_ctor_set(v___x_2572_, 2, v___x_2569_);
                lean_ctor_set(v___x_2572_, 3, v___x_2571_);
                v___x_2573_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5;
                v___x_2574_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6;
                v___x_2575_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2576_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2576_, 0, v___y_2528_);
                lean_ctor_set(v___x_2576_, 1, v___x_2575_);
                v___x_2577_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2578_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_2579_ = lean_box(0);
                v___x_2580_ = l_Lean_addMacroScope(v___y_2530_, v___x_2579_, v___y_2523_);
                v___x_2581_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12;
                v___x_2582_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2582_, 0, v___y_2528_);
                lean_ctor_set(v___x_2582_, 1, v___x_2578_);
                lean_ctor_set(v___x_2582_, 2, v___x_2580_);
                lean_ctor_set(v___x_2582_, 3, v___x_2581_);
                v___x_2583_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2577_, v___x_2582_);
                v___x_2584_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2574_, v___x_2576_, v___x_2583_);
                v___x_2585_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26;
                v___x_2586_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27;
                v___x_2587_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2587_, 0, v___y_2528_);
                lean_ctor_set(v___x_2587_, 1, v___x_2586_);
                v___x_2588_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2585_,
                    v___y_2527_,
                    v___x_2587_,
                    v___y_2533_,
                );
                v___x_2589_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_2590_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2590_, 0, v___y_2528_);
                lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                lean_inc_ref(v___x_2590_);
                lean_inc(v___x_2584_);
                v___x_2591_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2573_,
                    v___x_2584_,
                    v___x_2588_,
                    v___x_2590_,
                );
                lean_inc_ref(v___x_2572_);
                v___x_2592_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___y_2531_,
                    v___x_2572_,
                    v___x_2591_,
                    v___x_2519_,
                );
                lean_inc_ref(v___x_2566_);
                v___x_2593_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2560_, v___x_2566_, v___x_2592_);
                v___x_2594_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2559_, v___x_2540_, v___x_2593_);
                v___x_2595_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2558_, v___x_2546_, v___x_2594_);
                v___x_2596_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32;
                v___x_2597_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29;
                v___x_2598_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13;
                v___x_2599_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2599_, 0, v___y_2528_);
                lean_ctor_set(v___x_2599_, 1, v___x_2597_);
                v___x_2600_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___y_2531_,
                    v___x_2572_,
                    v___y_2525_,
                    v___x_2519_,
                );
                v___x_2601_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2560_, v___x_2566_, v___x_2600_);
                v___x_2602_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2573_,
                    v___x_2584_,
                    v___x_2601_,
                    v___x_2590_,
                );
                v___x_2603_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2598_, v___x_2599_, v___x_2602_);
                v___x_2604_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64;
                v___x_2605_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2604_, v___x_2546_, v___x_2546_);
                v___x_2606_ = l_Lean_Syntax_node4(
                    v___y_2528_,
                    v___x_2596_,
                    v___x_2542_,
                    v___x_2603_,
                    v___x_2605_,
                    v___x_2546_,
                );
                v___x_2607_ = l_Lean_Syntax_node6(
                    v___y_2528_,
                    v___x_2554_,
                    v___x_2556_,
                    v___x_2557_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2595_,
                    v___x_2606_,
                );
                v___x_2608_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2544_, v___x_2552_, v___x_2607_);
                v___x_2609_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___y_2531_, v___x_2543_, v___x_2608_);
                v___x_2610_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                lean_ctor_set(v___x_2610_, 1, v_a_2505_);
                return v___x_2610_;
            }
            2 => {
                v___x_2613_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0;
                v___x_2614_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1;
                v___x_2615_ = 0;
                v_fam_2616_ = l_Lean_mkCIdentFrom(v_tk_2513_, v___x_2614_, v___x_2615_);
                v___x_2617_ = l_Lean_TSyntax_getId(v_kind_2515_);
                lean_inc(v___x_2617_);
                v_kindLit_2618_ = l_Lake_Name_quoteFrom(v_kind_2515_, v___x_2617_, v___x_2615_);
                v___x_2619_ = l_Lean_TSyntax_getId(v_name_2517_);
                lean_inc(v___x_2619_);
                v_nameLit_2620_ = l_Lake_Name_quoteFrom(v_name_2517_, v___x_2619_, v___x_2615_);
                v_quotContext_2621_ = lean_ctor_get(v_a_2504_, 1);
                v_currMacroScope_2622_ = lean_ctor_get(v_a_2504_, 2);
                v_ref_2623_ = lean_ctor_get(v_a_2504_, 5);
                v_facet_2624_ = l_Lean_Name_append(v___x_2617_, v___x_2619_);
                lean_inc(v_facet_2624_);
                lean_inc(v_tk_2513_);
                v_facetLit_2625_ = l_Lake_Name_quoteFrom(v_tk_2513_, v_facet_2624_, v___x_2615_);
                v_id_2626_ = l_Lean_mkIdentFrom(v_tk_2513_, v_facet_2624_, v___x_2507_);
                v_ref_2627_ = l_Lean_replaceRef(v_tk_2513_, v_ref_2623_);
                lean_dec(v_tk_2513_);
                v___x_2628_ = l_Lean_SourceInfo_fromRef(v_ref_2627_, v___x_2615_);
                lean_dec(v_ref_2627_);
                v___x_2629_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2630_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_2631_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_2612_) == 1 {
                    v_val_2632_ = lean_ctor_get(v___y_2612_, 0);
                    lean_inc(v_val_2632_);
                    lean_dec_ref_known(v___y_2612_, 1);
                    v___x_2633_ = l_Array_mkArray1___redArg(v_val_2632_);
                    v___y_2521_ = v___x_2630_;
                    v___y_2522_ = v_fam_2616_;
                    v___y_2523_ = v_currMacroScope_2622_;
                    v___y_2524_ = v___x_2613_;
                    v___y_2525_ = v_facetLit_2625_;
                    v___y_2526_ = v___x_2631_;
                    v___y_2527_ = v_kindLit_2618_;
                    v___y_2528_ = v___x_2628_;
                    v___y_2529_ = v___x_2614_;
                    v___y_2530_ = v_quotContext_2621_;
                    v___y_2531_ = v___x_2629_;
                    v___y_2532_ = v_id_2626_;
                    v___y_2533_ = v_nameLit_2620_;
                    v___y_2534_ = v___x_2633_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2612_);
                    v___x_2634_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2521_ = v___x_2630_;
                    v___y_2522_ = v_fam_2616_;
                    v___y_2523_ = v_currMacroScope_2622_;
                    v___y_2524_ = v___x_2613_;
                    v___y_2525_ = v_facetLit_2625_;
                    v___y_2526_ = v___x_2631_;
                    v___y_2527_ = v_kindLit_2618_;
                    v___y_2528_ = v___x_2628_;
                    v___y_2529_ = v___x_2614_;
                    v___y_2530_ = v_quotContext_2621_;
                    v___y_2531_ = v___x_2629_;
                    v___y_2532_ = v_id_2626_;
                    v___y_2533_ = v_nameLit_2620_;
                    v___y_2534_ = v___x_2634_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2640_ == 0 {
                    v___x_2642_ = v___x_2639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_val_2637_);
                    v___x_2642_ = v_reuseFailAlloc_2643_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2612_ = v___x_2642_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___boxed(
    mut v_x_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2648_: *mut LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(
        v_x_2645_, v_a_2646_, v_a_2647_,
    );
    lean_dec_ref(v_a_2646_);
    return v_res_2648_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(
    mut v_x_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: u8 = 0;
    let mut v___y_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2681_ = l_Lake_packageDataDecl___closed__1;
                lean_inc(v_x_2678_);
                v___x_2682_ = l_Lean_Syntax_isOfKind(v_x_2678_, v___x_2681_);
                if v___x_2682_ == 0 {
                    lean_dec(v_x_2678_);
                    v___x_2683_ = lean_box(1);
                    v___x_2684_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2684_, 0, v___x_2683_);
                    lean_ctor_set(v___x_2684_, 1, v_a_2680_);
                    return v___x_2684_;
                } else {
                    v___x_2685_ = lean_unsigned_to_nat(0);
                    v___x_2686_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2685_);
                    v___x_2687_ = lean_unsigned_to_nat(1);
                    v_tk_2688_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2687_);
                    v___x_2689_ = lean_unsigned_to_nat(2);
                    v___x_2690_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2689_);
                    v___x_2691_ = lean_unsigned_to_nat(4);
                    v___x_2692_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2691_);
                    lean_dec(v_x_2678_);
                    v___x_2722_ = l_Lean_Syntax_getOptional_x3f(v___x_2686_);
                    lean_dec(v___x_2686_);
                    if lean_obj_tag(v___x_2722_) == 0 {
                        v___x_2723_ = lean_box(0);
                        v___y_2712_ = v___x_2723_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2724_ = lean_ctor_get(v___x_2722_, 0);
                        v_isSharedCheck_2731_ = (!lean_is_exclusive(v___x_2722_)) as u8;
                        if v_isSharedCheck_2731_ == 0 {
                            v___x_2726_ = v___x_2722_;
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2724_);
                            lean_dec(v___x_2722_);
                            v___x_2726_ = lean_box(0);
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2697_);
                v___x_2700_ = l_Array_append___redArg(v___y_2697_, v___y_2699_);
                lean_dec_ref(v___y_2699_);
                lean_inc(v___y_2695_);
                lean_inc_n(v___y_2698_, 2);
                v___x_2701_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2701_, 0, v___y_2698_);
                lean_ctor_set(v___x_2701_, 1, v___y_2695_);
                lean_ctor_set(v___x_2701_, 2, v___x_2700_);
                v___x_2702_ = l_Lean_SourceInfo_fromRef(v_tk_2688_, v___x_2682_);
                v___x_2703_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2704_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2704_, 0, v___x_2702_);
                lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                v___x_2705_ = l_Lake_Package_keyword;
                v___x_2706_ = l_Lean_mkIdentFrom(v_tk_2688_, v___x_2705_, v___y_2694_);
                lean_dec(v_tk_2688_);
                v___x_2707_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2708_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2708_, 0, v___y_2698_);
                lean_ctor_set(v___x_2708_, 1, v___x_2707_);
                lean_inc(v___y_2696_);
                v___x_2709_ = l_Lean_Syntax_node6(
                    v___y_2698_,
                    v___y_2696_,
                    v___x_2701_,
                    v___x_2704_,
                    v___x_2706_,
                    v___x_2690_,
                    v___x_2708_,
                    v___x_2692_,
                );
                v___x_2710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2710_, 0, v___x_2709_);
                lean_ctor_set(v___x_2710_, 1, v_a_2680_);
                return v___x_2710_;
            }
            2 => {
                v_ref_2713_ = lean_ctor_get(v_a_2679_, 5);
                v___x_2714_ = 0;
                v___x_2715_ = l_Lean_SourceInfo_fromRef(v_ref_2713_, v___x_2714_);
                v___x_2716_ = l_Lake_facetDataDecl___closed__1;
                v___x_2717_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2718_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_2712_) == 1 {
                    v_val_2719_ = lean_ctor_get(v___y_2712_, 0);
                    lean_inc(v_val_2719_);
                    lean_dec_ref_known(v___y_2712_, 1);
                    v___x_2720_ = l_Array_mkArray1___redArg(v_val_2719_);
                    v___y_2694_ = v___x_2714_;
                    v___y_2695_ = v___x_2717_;
                    v___y_2696_ = v___x_2716_;
                    v___y_2697_ = v___x_2718_;
                    v___y_2698_ = v___x_2715_;
                    v___y_2699_ = v___x_2720_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2712_);
                    v___x_2721_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2694_ = v___x_2714_;
                    v___y_2695_ = v___x_2717_;
                    v___y_2696_ = v___x_2716_;
                    v___y_2697_ = v___x_2718_;
                    v___y_2698_ = v___x_2715_;
                    v___y_2699_ = v___x_2721_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2727_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_val_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2712_ = v___x_2729_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___boxed(
    mut v_x_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(
        v_x_2732_, v_a_2733_, v_a_2734_,
    );
    lean_dec_ref(v_a_2733_);
    return v_res_2735_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(
    mut v_x_2764_: *mut LeanObject,
    mut v_a_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: u8 = 0;
    let mut v___y_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = l_Lake_moduleDataDecl___closed__1;
                lean_inc(v_x_2764_);
                v___x_2768_ = l_Lean_Syntax_isOfKind(v_x_2764_, v___x_2767_);
                if v___x_2768_ == 0 {
                    lean_dec(v_x_2764_);
                    v___x_2769_ = lean_box(1);
                    v___x_2770_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                    lean_ctor_set(v___x_2770_, 1, v_a_2766_);
                    return v___x_2770_;
                } else {
                    v___x_2771_ = lean_unsigned_to_nat(0);
                    v___x_2772_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2771_);
                    v___x_2773_ = lean_unsigned_to_nat(1);
                    v_tk_2774_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2773_);
                    v___x_2775_ = lean_unsigned_to_nat(2);
                    v___x_2776_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2775_);
                    v___x_2777_ = lean_unsigned_to_nat(4);
                    v___x_2778_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2777_);
                    lean_dec(v_x_2764_);
                    v___x_2808_ = l_Lean_Syntax_getOptional_x3f(v___x_2772_);
                    lean_dec(v___x_2772_);
                    if lean_obj_tag(v___x_2808_) == 0 {
                        v___x_2809_ = lean_box(0);
                        v___y_2798_ = v___x_2809_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2810_ = lean_ctor_get(v___x_2808_, 0);
                        v_isSharedCheck_2817_ = (!lean_is_exclusive(v___x_2808_)) as u8;
                        if v_isSharedCheck_2817_ == 0 {
                            v___x_2812_ = v___x_2808_;
                            v_isShared_2813_ = v_isSharedCheck_2817_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2810_);
                            lean_dec(v___x_2808_);
                            v___x_2812_ = lean_box(0);
                            v_isShared_2813_ = v_isSharedCheck_2817_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2783_);
                v___x_2786_ = l_Array_append___redArg(v___y_2783_, v___y_2785_);
                lean_dec_ref(v___y_2785_);
                lean_inc(v___y_2780_);
                lean_inc_n(v___y_2781_, 2);
                v___x_2787_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2787_, 0, v___y_2781_);
                lean_ctor_set(v___x_2787_, 1, v___y_2780_);
                lean_ctor_set(v___x_2787_, 2, v___x_2786_);
                v___x_2788_ = l_Lean_SourceInfo_fromRef(v_tk_2774_, v___x_2768_);
                v___x_2789_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2790_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2790_, 0, v___x_2788_);
                lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                v___x_2791_ = l_Lake_Module_keyword;
                v___x_2792_ = l_Lean_mkIdentFrom(v_tk_2774_, v___x_2791_, v___y_2782_);
                lean_dec(v_tk_2774_);
                v___x_2793_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2794_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2794_, 0, v___y_2781_);
                lean_ctor_set(v___x_2794_, 1, v___x_2793_);
                lean_inc(v___y_2784_);
                v___x_2795_ = l_Lean_Syntax_node6(
                    v___y_2781_,
                    v___y_2784_,
                    v___x_2787_,
                    v___x_2790_,
                    v___x_2792_,
                    v___x_2776_,
                    v___x_2794_,
                    v___x_2778_,
                );
                v___x_2796_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                lean_ctor_set(v___x_2796_, 1, v_a_2766_);
                return v___x_2796_;
            }
            2 => {
                v_ref_2799_ = lean_ctor_get(v_a_2765_, 5);
                v___x_2800_ = 0;
                v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2799_, v___x_2800_);
                v___x_2802_ = l_Lake_facetDataDecl___closed__1;
                v___x_2803_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_2798_) == 1 {
                    v_val_2805_ = lean_ctor_get(v___y_2798_, 0);
                    lean_inc(v_val_2805_);
                    lean_dec_ref_known(v___y_2798_, 1);
                    v___x_2806_ = l_Array_mkArray1___redArg(v_val_2805_);
                    v___y_2780_ = v___x_2803_;
                    v___y_2781_ = v___x_2801_;
                    v___y_2782_ = v___x_2800_;
                    v___y_2783_ = v___x_2804_;
                    v___y_2784_ = v___x_2802_;
                    v___y_2785_ = v___x_2806_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2798_);
                    v___x_2807_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2780_ = v___x_2803_;
                    v___y_2781_ = v___x_2801_;
                    v___y_2782_ = v___x_2800_;
                    v___y_2783_ = v___x_2804_;
                    v___y_2784_ = v___x_2802_;
                    v___y_2785_ = v___x_2807_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_val_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2798_ = v___x_2815_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1___boxed(
    mut v_x_2818_: *mut LeanObject,
    mut v_a_2819_: *mut LeanObject,
    mut v_a_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2821_: *mut LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(
        v_x_2818_, v_a_2819_, v_a_2820_,
    );
    lean_dec_ref(v_a_2819_);
    return v_res_2821_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(
    mut v_x_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: u8 = 0;
    let mut v___y_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = l_Lake_libraryDataDecl___closed__1;
                lean_inc(v_x_2853_);
                v___x_2857_ = l_Lean_Syntax_isOfKind(v_x_2853_, v___x_2856_);
                if v___x_2857_ == 0 {
                    lean_dec(v_x_2853_);
                    v___x_2858_ = lean_box(1);
                    v___x_2859_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2859_, 0, v___x_2858_);
                    lean_ctor_set(v___x_2859_, 1, v_a_2855_);
                    return v___x_2859_;
                } else {
                    v___x_2860_ = lean_unsigned_to_nat(0);
                    v___x_2861_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2860_);
                    v___x_2862_ = lean_unsigned_to_nat(1);
                    v_tk_2863_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2862_);
                    v___x_2864_ = lean_unsigned_to_nat(2);
                    v___x_2865_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2864_);
                    v___x_2866_ = lean_unsigned_to_nat(4);
                    v___x_2867_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2866_);
                    lean_dec(v_x_2853_);
                    v___x_2897_ = l_Lean_Syntax_getOptional_x3f(v___x_2861_);
                    lean_dec(v___x_2861_);
                    if lean_obj_tag(v___x_2897_) == 0 {
                        v___x_2898_ = lean_box(0);
                        v___y_2887_ = v___x_2898_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2899_ = lean_ctor_get(v___x_2897_, 0);
                        v_isSharedCheck_2906_ = (!lean_is_exclusive(v___x_2897_)) as u8;
                        if v_isSharedCheck_2906_ == 0 {
                            v___x_2901_ = v___x_2897_;
                            v_isShared_2902_ = v_isSharedCheck_2906_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2899_);
                            lean_dec(v___x_2897_);
                            v___x_2901_ = lean_box(0);
                            v_isShared_2902_ = v_isSharedCheck_2906_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2872_);
                v___x_2875_ = l_Array_append___redArg(v___y_2872_, v___y_2874_);
                lean_dec_ref(v___y_2874_);
                lean_inc(v___y_2873_);
                lean_inc_n(v___y_2871_, 2);
                v___x_2876_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2876_, 0, v___y_2871_);
                lean_ctor_set(v___x_2876_, 1, v___y_2873_);
                lean_ctor_set(v___x_2876_, 2, v___x_2875_);
                v___x_2877_ = l_Lean_SourceInfo_fromRef(v_tk_2863_, v___x_2857_);
                v___x_2878_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2879_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2879_, 0, v___x_2877_);
                lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                v___x_2880_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1;
                v___x_2881_ = l_Lean_mkIdentFrom(v_tk_2863_, v___x_2880_, v___y_2869_);
                lean_dec(v_tk_2863_);
                v___x_2882_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2883_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2883_, 0, v___y_2871_);
                lean_ctor_set(v___x_2883_, 1, v___x_2882_);
                lean_inc(v___y_2870_);
                v___x_2884_ = l_Lean_Syntax_node6(
                    v___y_2871_,
                    v___y_2870_,
                    v___x_2876_,
                    v___x_2879_,
                    v___x_2881_,
                    v___x_2865_,
                    v___x_2883_,
                    v___x_2867_,
                );
                v___x_2885_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2885_, 0, v___x_2884_);
                lean_ctor_set(v___x_2885_, 1, v_a_2855_);
                return v___x_2885_;
            }
            2 => {
                v_ref_2888_ = lean_ctor_get(v_a_2854_, 5);
                v___x_2889_ = 0;
                v___x_2890_ = l_Lean_SourceInfo_fromRef(v_ref_2888_, v___x_2889_);
                v___x_2891_ = l_Lake_facetDataDecl___closed__1;
                v___x_2892_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_2887_) == 1 {
                    v_val_2894_ = lean_ctor_get(v___y_2887_, 0);
                    lean_inc(v_val_2894_);
                    lean_dec_ref_known(v___y_2887_, 1);
                    v___x_2895_ = l_Array_mkArray1___redArg(v_val_2894_);
                    v___y_2869_ = v___x_2889_;
                    v___y_2870_ = v___x_2891_;
                    v___y_2871_ = v___x_2890_;
                    v___y_2872_ = v___x_2893_;
                    v___y_2873_ = v___x_2892_;
                    v___y_2874_ = v___x_2895_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2887_);
                    v___x_2896_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2869_ = v___x_2889_;
                    v___y_2870_ = v___x_2891_;
                    v___y_2871_ = v___x_2890_;
                    v___y_2872_ = v___x_2893_;
                    v___y_2873_ = v___x_2892_;
                    v___y_2874_ = v___x_2896_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2902_ == 0 {
                    v___x_2904_ = v___x_2901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_val_2899_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2887_ = v___x_2904_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___boxed(
    mut v_x_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2910_: *mut LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(
        v_x_2907_, v_a_2908_, v_a_2909_,
    );
    lean_dec_ref(v_a_2908_);
    return v_res_2910_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(
    mut v_x_2959_: *mut LeanObject,
    mut v_a_2960_: *mut LeanObject,
    mut v_a_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tgt_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2962_ = l_Lake_customDataDecl___closed__1;
                lean_inc(v_x_2959_);
                v___x_2963_ = l_Lean_Syntax_isOfKind(v_x_2959_, v___x_2962_);
                if v___x_2963_ == 0 {
                    lean_dec(v_x_2959_);
                    v___x_2964_ = lean_box(1);
                    v___x_2965_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2965_, 0, v___x_2964_);
                    lean_ctor_set(v___x_2965_, 1, v_a_2961_);
                    return v___x_2965_;
                } else {
                    v___x_2966_ = lean_unsigned_to_nat(0);
                    v___x_2967_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2966_);
                    v___x_2968_ = lean_unsigned_to_nat(1);
                    v_tk_2969_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2968_);
                    v___x_2970_ = lean_unsigned_to_nat(2);
                    v_pkg_2971_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2970_);
                    v___x_2972_ = lean_unsigned_to_nat(3);
                    v_tgt_2973_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2972_);
                    v___x_2974_ = lean_unsigned_to_nat(5);
                    v___x_2975_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2974_);
                    lean_dec(v_x_2959_);
                    v___x_3039_ = l_Lean_Syntax_getOptional_x3f(v___x_2967_);
                    lean_dec(v___x_2967_);
                    if lean_obj_tag(v___x_3039_) == 0 {
                        v___x_3040_ = lean_box(0);
                        v___y_3018_ = v___x_3040_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3041_ = lean_ctor_get(v___x_3039_, 0);
                        v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3039_)) as u8;
                        if v_isSharedCheck_3048_ == 0 {
                            v___x_3043_ = v___x_3039_;
                            v_isShared_3044_ = v_isSharedCheck_3048_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_3041_);
                            lean_dec(v___x_3039_);
                            v___x_3043_ = lean_box(0);
                            v_isShared_3044_ = v_isSharedCheck_3048_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2977_);
                v___x_2988_ = l_Array_append___redArg(v___y_2977_, v___y_2987_);
                lean_dec_ref(v___y_2987_);
                lean_inc_n(v___y_2978_, 3);
                lean_inc_n(v___y_2981_, 13);
                v___x_2989_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2989_, 0, v___y_2981_);
                lean_ctor_set(v___x_2989_, 1, v___y_2978_);
                lean_ctor_set(v___x_2989_, 2, v___x_2988_);
                v___x_2990_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2991_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2991_, 0, v___y_2981_);
                lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                v___x_2992_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2993_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2993_, 0, v___y_2981_);
                lean_ctor_set(v___x_2993_, 1, v___x_2992_);
                v___x_2994_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1;
                v___x_2995_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6;
                v___x_2996_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2997_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2997_, 0, v___y_2981_);
                lean_ctor_set(v___x_2997_, 1, v___x_2996_);
                v___x_2998_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2999_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_3000_ = lean_box(0);
                lean_inc(v___y_2986_);
                lean_inc(v___y_2984_);
                v___x_3001_ = l_Lean_addMacroScope(v___y_2984_, v___x_3000_, v___y_2986_);
                v___x_3002_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3;
                v___x_3003_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3003_, 0, v___y_2981_);
                lean_ctor_set(v___x_3003_, 1, v___x_2999_);
                lean_ctor_set(v___x_3003_, 2, v___x_3001_);
                lean_ctor_set(v___x_3003_, 3, v___x_3002_);
                v___x_3004_ = l_Lean_Syntax_node1(v___y_2981_, v___x_2998_, v___x_3003_);
                v___x_3005_ =
                    l_Lean_Syntax_node2(v___y_2981_, v___x_2995_, v___x_2997_, v___x_3004_);
                v___x_3006_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_3007_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3007_, 0, v___y_2981_);
                lean_ctor_set(v___x_3007_, 1, v___x_3006_);
                v___x_3008_ = l_Lean_Syntax_node1(v___y_2981_, v___y_2978_, v___y_2982_);
                v___x_3009_ = l_Lean_Syntax_node3(
                    v___y_2981_,
                    v___y_2978_,
                    v___y_2985_,
                    v___x_3007_,
                    v___x_3008_,
                );
                v___x_3010_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_3011_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3011_, 0, v___y_2981_);
                lean_ctor_set(v___x_3011_, 1, v___x_3010_);
                v___x_3012_ = l_Lean_Syntax_node3(
                    v___y_2981_,
                    v___x_2994_,
                    v___x_3005_,
                    v___x_3009_,
                    v___x_3011_,
                );
                v___x_3013_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_3014_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3014_, 0, v___y_2981_);
                lean_ctor_set(v___x_3014_, 1, v___x_3013_);
                lean_inc(v___y_2983_);
                v___x_3015_ = l_Lean_Syntax_node8(
                    v___y_2981_,
                    v___y_2983_,
                    v___x_2989_,
                    v___x_2991_,
                    v___y_2979_,
                    v___x_2993_,
                    v___y_2980_,
                    v___x_3012_,
                    v___x_3014_,
                    v___x_2975_,
                );
                v___x_3016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3016_, 0, v___x_3015_);
                lean_ctor_set(v___x_3016_, 1, v_a_2961_);
                return v___x_3016_;
            }
            2 => {
                v_quotContext_3019_ = lean_ctor_get(v_a_2960_, 1);
                v_currMacroScope_3020_ = lean_ctor_get(v_a_2960_, 2);
                v_ref_3021_ = lean_ctor_get(v_a_2960_, 5);
                v_ref_3022_ = l_Lean_replaceRef(v_tk_2969_, v_ref_3021_);
                lean_dec(v_tk_2969_);
                v___x_3023_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5;
                v___x_3024_ = 0;
                v___x_3025_ = l_Lean_mkCIdentFrom(v_ref_3022_, v___x_3023_, v___x_3024_);
                v___x_3026_ = l_Lean_TSyntax_getId(v_pkg_2971_);
                v___x_3027_ = l_Lean_TSyntax_getId(v_tgt_2973_);
                lean_inc(v___x_3027_);
                lean_inc(v___x_3026_);
                v___x_3028_ = l_Lean_Name_append(v___x_3026_, v___x_3027_);
                v___x_3029_ = l_Lean_mkIdentFrom(v_tgt_2973_, v___x_3028_, v___x_3024_);
                lean_dec(v_tgt_2973_);
                v___x_3030_ = l_Lake_Name_quoteFrom(v_pkg_2971_, v___x_3026_, v___x_3024_);
                lean_inc(v___x_3030_);
                v___x_3031_ = l_Lake_Name_quoteFrom(v___x_3030_, v___x_3027_, v___x_3024_);
                v___x_3032_ = l_Lean_SourceInfo_fromRef(v_ref_3022_, v___x_3024_);
                lean_dec(v_ref_3022_);
                v___x_3033_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_3034_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_3035_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if lean_obj_tag(v___y_3018_) == 1 {
                    v_val_3036_ = lean_ctor_get(v___y_3018_, 0);
                    lean_inc(v_val_3036_);
                    lean_dec_ref_known(v___y_3018_, 1);
                    v___x_3037_ = l_Array_mkArray1___redArg(v_val_3036_);
                    v___y_2977_ = v___x_3035_;
                    v___y_2978_ = v___x_3034_;
                    v___y_2979_ = v___x_3029_;
                    v___y_2980_ = v___x_3025_;
                    v___y_2981_ = v___x_3032_;
                    v___y_2982_ = v___x_3031_;
                    v___y_2983_ = v___x_3033_;
                    v___y_2984_ = v_quotContext_3019_;
                    v___y_2985_ = v___x_3030_;
                    v___y_2986_ = v_currMacroScope_3020_;
                    v___y_2987_ = v___x_3037_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_3018_);
                    v___x_3038_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2977_ = v___x_3035_;
                    v___y_2978_ = v___x_3034_;
                    v___y_2979_ = v___x_3029_;
                    v___y_2980_ = v___x_3025_;
                    v___y_2981_ = v___x_3032_;
                    v___y_2982_ = v___x_3031_;
                    v___y_2983_ = v___x_3033_;
                    v___y_2984_ = v_quotContext_3019_;
                    v___y_2985_ = v___x_3030_;
                    v___y_2986_ = v_currMacroScope_3020_;
                    v___y_2987_ = v___x_3038_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3044_ == 0 {
                    v___x_3046_ = v___x_3043_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_val_3041_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3018_ = v___x_3046_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___boxed(
    mut v_x_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3052_: *mut LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(
        v_x_3049_, v_a_3050_, v_a_3051_,
    );
    lean_dec_ref(v_a_3050_);
    return v_res_3052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Key(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Family(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Data(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Key(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Family(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Data(builtin);
}

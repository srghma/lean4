// Lean compiler output
// Module: Lake.Config.Pattern
// Imports: Init.System.FilePath Std.Data.TreeMap.Basic Lean.Data.Name Lake.Util.Name Init.Data.String.TakeDrop Init.Data.String.Basic Init.Data.Option.Coe Init.Omega
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_nat_sub, lean_string_dec_eq, lean_string_memcmp, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_flip;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any;
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, l_System_FilePath_extension, l_System_FilePath_fileName,
    l_System_FilePath_normalize, runtime_initialize_Init_System_FilePath,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    runtime_initialize_Lean_Data_Name,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
pub static l_Lake_term___x3d_x7e___00__closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lake_term___x3d_x7e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [116, 101, 114, 109, 95, 61, 126, 95, 0],
    };
static mut l_Lake_term___x3d_x7e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__1_value)
        as *mut leanh::LeanObject;
static l_Lake_term___x3d_x7e___00__closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_term___x3d_x7e___00__closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__1_value)
                as *mut leanh::LeanObject,
            7154965323529718077 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__3_value: leanh::LeanStringObject<8> =
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
static mut l_Lake_term___x3d_x7e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__5_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 126, 32, 0],
    };
static mut l_Lake_term___x3d_x7e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__7_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lake_term___x3d_x7e___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__7_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__8_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__11_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_term___x3d_x7e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [73, 115, 80, 97, 116, 116, 101, 114, 110, 46, 115, 97, 116, 105, 115, 102, 105, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 115, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 97, 116, 105, 115, 102, 105, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut leanh::LeanObject,9728926758818137547 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut leanh::LeanObject,17326574432564351101 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value) as *mut leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut leanh::LeanObject,13480139565922167655 as *mut leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut leanh::LeanObject,9215142959186488649 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedPattern_default__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedPattern_default__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedPattern_default__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedPattern_default__1___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedPattern_default__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedPattern___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPatternDescr_default__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedPatternDescr_default__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPatternDescr___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPatternDescr___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instCoePatternDescr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoePatternDescr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoePatternDescr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoePatternDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instIsPatternPattern___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instIsPatternPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instIsPatternPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPattern___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__3_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__4_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__5_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__6_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PatternDescr_matches___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instCoeForallBoolPattern___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeForallBoolPattern___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeForallBoolPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeForallBoolPattern___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_empty___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_PatternDescr_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PatternDescr_empty___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Pattern_empty___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [101, 109, 112, 116, 121, 0],
    };
static mut l_Lake_Pattern_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_empty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Pattern_empty___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Pattern_empty___closed__0_value)
                as *mut leanh::LeanObject,
            7601931857476342375 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Pattern_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_empty___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Pattern_empty___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_empty___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_empty___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instEmptyCollectionPattern___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instEmptyCollectionPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_PatternDescr_star___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_star___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_star___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Pattern_star___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Pattern_star___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [115, 116, 97, 114, 0],
    };
static mut l_Lake_Pattern_star___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Pattern_star___closed__1_value)
                as *mut leanh::LeanObject,
            3121916218220129135 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Pattern_star___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_Pattern_star___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_star___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_star___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedStrPatDescr_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_instInhabitedStrPatDescr_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedStrPatDescr_default___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedStrPatDescr_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedStrPatDescr_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedStrPatDescr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instIsPatternStrPatDescrString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StrPatDescr_matches___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instIsPatternStrPatDescrString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instIsPatternStrPatDescrString___closed__1_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_flip as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instIsPatternStrPatDescrString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instIsPatternStrPatDescrString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instCoeArrayStringStrPatDescr___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instCoeArrayStringStrPatDescr___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instCoeArrayStringStrPatDescr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPatDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeArrayStringStrPatDescr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPatDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instCoeArrayStringStrPat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPat_mem as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeArrayStringStrPat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeArrayStringStrPat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_StrPat_beq___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [98, 101, 113, 0],
    };
static mut l_Lake_StrPat_beq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_beq___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_StrPat_beq___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_StrPat_beq___closed__0_value)
                as *mut leanh::LeanObject,
            5562882229368833754 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_beq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_beq___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_instCoeStringStrPatDescr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPatDescr_beq as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStringStrPatDescr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPatDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeStringStrPatDescr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPatDescr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instCoeStringStrPat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPat_beq as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStringStrPat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeStringStrPat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPat___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedPathPatDescr_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPathPatDescr_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPathPatDescr_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPathPatDescr_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPathPatDescr_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPathPatDescr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_PathPatDescr_matches___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instIsPatternPathPatDescrFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_flip as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instIsPatternPathPatDescrFilePath___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instIsPatternPathPatDescrFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_isVerLike___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_StrPat_verLike___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [118, 101, 114, 76, 105, 107, 101, 0],
    };
static mut l_Lake_StrPat_verLike___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__1_value)
                as *mut leanh::LeanObject,
            5548260973545959018 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_verLike___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_verLike___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__3_value) as *mut leanh::LeanObject;
pub static mut l_Lake_StrPat_verLike: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lake_defaultVersionTags___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__0_value)
                as *mut leanh::LeanObject,
            9666231177748665885 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_defaultVersionTags___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__1_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_defaultVersionTags___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_defaultVersionTags: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_versionTagPresets___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionTagPresets___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionTagPresets___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionTagPresets___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_versionTagPresets: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5;
    v___x_1226_ = l_String_toRawSubstring_x27(v___x_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(
    mut v_x_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    v___x_1248_ = l_Lake_term___x3d_x7e___00__closed__2;
    leanh::lean_inc(v_x_1245_);
    v___x_1249_ = l_Lean_Syntax_isOfKind(v_x_1245_, v___x_1248_);
    if v___x_1249_ == 0 {
        let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1245_);
        v___x_1250_ = leanh::lean_box(1);
        v___x_1251_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
        leanh::lean_ctor_set(v___x_1251_, 1, v_a_1247_);
        return v___x_1251_;
    } else {
        let mut v_quotContext_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: u8 = 0;
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1252_ = leanh::lean_ctor_get(v_a_1246_, 1);
        v_currMacroScope_1253_ = leanh::lean_ctor_get(v_a_1246_, 2);
        v_ref_1254_ = leanh::lean_ctor_get(v_a_1246_, 5);
        v___x_1255_ = leanh::lean_unsigned_to_nat(0);
        v___x_1256_ = l_Lean_Syntax_getArg(v_x_1245_, v___x_1255_);
        v___x_1257_ = leanh::lean_unsigned_to_nat(2);
        v___x_1258_ = l_Lean_Syntax_getArg(v_x_1245_, v___x_1257_);
        leanh::lean_dec(v_x_1245_);
        v___x_1259_ = 0;
        v___x_1260_ = l_Lean_SourceInfo_fromRef(v_ref_1254_, v___x_1259_);
        v___x_1261_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4;
        v___x_1262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once), _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6);
        v___x_1263_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9;
        leanh::lean_inc(v_currMacroScope_1253_);
        leanh::lean_inc(v_quotContext_1252_);
        v___x_1264_ =
            l_Lean_addMacroScope(v_quotContext_1252_, v___x_1263_, v_currMacroScope_1253_);
        v___x_1265_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12;
        leanh::lean_inc_n(v___x_1260_, 2);
        v___x_1266_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1266_, 0, v___x_1260_);
        leanh::lean_ctor_set(v___x_1266_, 1, v___x_1262_);
        leanh::lean_ctor_set(v___x_1266_, 2, v___x_1264_);
        leanh::lean_ctor_set(v___x_1266_, 3, v___x_1265_);
        v___x_1267_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14;
        v___x_1268_ = l_Lean_Syntax_node2(v___x_1260_, v___x_1267_, v___x_1256_, v___x_1258_);
        v___x_1269_ = l_Lean_Syntax_node2(v___x_1260_, v___x_1261_, v___x_1266_, v___x_1268_);
        v___x_1270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
        leanh::lean_ctor_set(v___x_1270_, 1, v_a_1247_);
        return v___x_1270_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___boxed(
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v_a_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(
        v_x_1271_, v_a_1272_, v_a_1273_,
    );
    leanh::lean_dec_ref(v_a_1272_);
    return v_res_1274_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(
    mut v_x_1278_: *mut leanh::LeanObject,
    mut v_a_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    v___x_1281_ =
        l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4;
    leanh::lean_inc(v_x_1278_);
    v___x_1282_ = l_Lean_Syntax_isOfKind(v_x_1278_, v___x_1281_);
    if v___x_1282_ == 0 {
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1278_);
        v___x_1283_ = leanh::lean_box(0);
        v___x_1284_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
        leanh::lean_ctor_set(v___x_1284_, 1, v_a_1280_);
        return v___x_1284_;
    } else {
        let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: u8 = 0;
        v___x_1285_ = leanh::lean_unsigned_to_nat(0);
        v___x_1286_ = l_Lean_Syntax_getArg(v_x_1278_, v___x_1285_);
        v___x_1287_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1;
        leanh::lean_inc(v___x_1286_);
        v___x_1288_ = l_Lean_Syntax_isOfKind(v___x_1286_, v___x_1287_);
        if v___x_1288_ == 0 {
            let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1286_);
            leanh::lean_dec(v_x_1278_);
            v___x_1289_ = leanh::lean_box(0);
            v___x_1290_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
            leanh::lean_ctor_set(v___x_1290_, 1, v_a_1280_);
            return v___x_1290_;
        } else {
            let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1294_: u8 = 0;
            v___x_1291_ = leanh::lean_unsigned_to_nat(1);
            v___x_1292_ = l_Lean_Syntax_getArg(v_x_1278_, v___x_1291_);
            leanh::lean_dec(v_x_1278_);
            v___x_1293_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1292_);
            v___x_1294_ = l_Lean_Syntax_matchesNull(v___x_1292_, v___x_1293_);
            if v___x_1294_ == 0 {
                let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1292_);
                leanh::lean_dec(v___x_1286_);
                v___x_1295_ = leanh::lean_box(0);
                v___x_1296_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1296_, 0, v___x_1295_);
                leanh::lean_ctor_set(v___x_1296_, 1, v_a_1280_);
                return v___x_1296_;
            } else {
                let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1300_: u8 = 0;
                let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1297_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1285_);
                v___x_1298_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1291_);
                leanh::lean_dec(v___x_1292_);
                v_ref_1299_ = l_Lean_replaceRef(v___x_1286_, v_a_1279_);
                leanh::lean_dec(v___x_1286_);
                v___x_1300_ = 0;
                v___x_1301_ = l_Lean_SourceInfo_fromRef(v_ref_1299_, v___x_1300_);
                leanh::lean_dec(v_ref_1299_);
                v___x_1302_ = l_Lake_term___x3d_x7e___00__closed__2;
                v___x_1303_ = l_Lake_term___x3d_x7e___00__closed__5;
                leanh::lean_inc(v___x_1301_);
                v___x_1304_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1304_, 0, v___x_1301_);
                leanh::lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                v___x_1305_ = l_Lean_Syntax_node3(
                    v___x_1301_,
                    v___x_1302_,
                    v___x_1297_,
                    v___x_1304_,
                    v___x_1298_,
                );
                v___x_1306_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                leanh::lean_ctor_set(v___x_1306_, 1, v_a_1280_);
                return v___x_1306_;
            }
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___boxed(
    mut v_x_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(
        v_x_1307_, v_a_1308_, v_a_1309_,
    );
    leanh::lean_dec(v_a_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___redArg(
    mut v_x_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1311_) {
        0 => {
            let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1312_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1312_;
        }
        1 => {
            let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1313_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1313_;
        }
        2 => {
            let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1314_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1314_;
        }
        _ => {
            let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1315_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1315_;
        }
    }
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___redArg___boxed(
    mut v_x_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_1316_);
    leanh::lean_dec_ref(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx(
    mut v_00_u03b1_1318_: *mut leanh::LeanObject,
    mut v_00_u03b2_1319_: *mut leanh::LeanObject,
    mut v_x_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___boxed(
    mut v_00_u03b1_1322_: *mut leanh::LeanObject,
    mut v_00_u03b2_1323_: *mut leanh::LeanObject,
    mut v_x_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lake_PatternDescr_ctorIdx(v_00_u03b1_1322_, v_00_u03b2_1323_, v_x_1324_);
    leanh::lean_dec_ref(v_x_1324_);
    return v_res_1325_;
}
pub unsafe fn l_Lake_PatternDescr_ctorElim___redArg(
    mut v_t_1326_: *mut leanh::LeanObject,
    mut v_k_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1326_) == 3 {
        let mut v_p_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_p_1328_ = leanh::lean_ctor_get(v_t_1326_, 0);
        leanh::lean_inc(v_p_1328_);
        leanh::lean_dec_ref_known(v_t_1326_, 1);
        v___x_1329_ = leanh::lean_apply_1(v_k_1327_, v_p_1328_);
        return v___x_1329_;
    } else {
        let mut v_p_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_p_1330_ = leanh::lean_ctor_get(v_t_1326_, 0);
        leanh::lean_inc_ref(v_p_1330_);
        leanh::lean_dec_ref(v_t_1326_);
        v___x_1331_ = leanh::lean_apply_1(v_k_1327_, v_p_1330_);
        return v___x_1331_;
    }
}
pub unsafe fn l_Lake_PatternDescr_ctorElim(
    mut v_00_u03b1_1332_: *mut leanh::LeanObject,
    mut v_00_u03b2_1333_: *mut leanh::LeanObject,
    mut v_motive__2_1334_: *mut leanh::LeanObject,
    mut v_ctorIdx_1335_: *mut leanh::LeanObject,
    mut v_t_1336_: *mut leanh::LeanObject,
    mut v_h_1337_: *mut leanh::LeanObject,
    mut v_k_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1336_, v_k_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Lake_PatternDescr_ctorElim___boxed(
    mut v_00_u03b1_1340_: *mut leanh::LeanObject,
    mut v_00_u03b2_1341_: *mut leanh::LeanObject,
    mut v_motive__2_1342_: *mut leanh::LeanObject,
    mut v_ctorIdx_1343_: *mut leanh::LeanObject,
    mut v_t_1344_: *mut leanh::LeanObject,
    mut v_h_1345_: *mut leanh::LeanObject,
    mut v_k_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l_Lake_PatternDescr_ctorElim(
        v_00_u03b1_1340_,
        v_00_u03b2_1341_,
        v_motive__2_1342_,
        v_ctorIdx_1343_,
        v_t_1344_,
        v_h_1345_,
        v_k_1346_,
    );
    leanh::lean_dec(v_ctorIdx_1343_);
    return v_res_1347_;
}
pub unsafe fn l_Lake_PatternDescr_not_elim___redArg(
    mut v_t_1348_: *mut leanh::LeanObject,
    mut v_not_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1348_, v_not_1349_);
    return v___x_1350_;
}
pub unsafe fn l_Lake_PatternDescr_not_elim(
    mut v_00_u03b1_1351_: *mut leanh::LeanObject,
    mut v_00_u03b2_1352_: *mut leanh::LeanObject,
    mut v_motive__2_1353_: *mut leanh::LeanObject,
    mut v_t_1354_: *mut leanh::LeanObject,
    mut v_h_1355_: *mut leanh::LeanObject,
    mut v_not_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1354_, v_not_1356_);
    return v___x_1357_;
}
pub unsafe fn l_Lake_PatternDescr_all_elim___redArg(
    mut v_t_1358_: *mut leanh::LeanObject,
    mut v_all_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1358_, v_all_1359_);
    return v___x_1360_;
}
pub unsafe fn l_Lake_PatternDescr_all_elim(
    mut v_00_u03b1_1361_: *mut leanh::LeanObject,
    mut v_00_u03b2_1362_: *mut leanh::LeanObject,
    mut v_motive__2_1363_: *mut leanh::LeanObject,
    mut v_t_1364_: *mut leanh::LeanObject,
    mut v_h_1365_: *mut leanh::LeanObject,
    mut v_all_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1364_, v_all_1366_);
    return v___x_1367_;
}
pub unsafe fn l_Lake_PatternDescr_any_elim___redArg(
    mut v_t_1368_: *mut leanh::LeanObject,
    mut v_any_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1368_, v_any_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Lake_PatternDescr_any_elim(
    mut v_00_u03b1_1371_: *mut leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut leanh::LeanObject,
    mut v_motive__2_1373_: *mut leanh::LeanObject,
    mut v_t_1374_: *mut leanh::LeanObject,
    mut v_h_1375_: *mut leanh::LeanObject,
    mut v_any_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1374_, v_any_1376_);
    return v___x_1377_;
}
pub unsafe fn l_Lake_PatternDescr_coe_elim___redArg(
    mut v_t_1378_: *mut leanh::LeanObject,
    mut v_coe_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1378_, v_coe_1379_);
    return v___x_1380_;
}
pub unsafe fn l_Lake_PatternDescr_coe_elim(
    mut v_00_u03b1_1381_: *mut leanh::LeanObject,
    mut v_00_u03b2_1382_: *mut leanh::LeanObject,
    mut v_motive__2_1383_: *mut leanh::LeanObject,
    mut v_t_1384_: *mut leanh::LeanObject,
    mut v_h_1385_: *mut leanh::LeanObject,
    mut v_coe_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1384_, v_coe_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1___lam__0(
    mut v_x_1388_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1389_: u8 = 0;
    v___x_1389_ = 0;
    return v___x_1389_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1___lam__0___boxed(
    mut v_x_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1391_: u8 = 0;
    let mut v_r_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Lake_instInhabitedPattern_default__1___lam__0(v_x_1390_);
    leanh::lean_dec(v_x_1390_);
    v_r_1392_ = leanh::lean_box((v_res_1391_) as usize);
    return v_r_1392_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1(
    mut v_00_u03b1_1398_: *mut leanh::LeanObject,
    mut v_00_u03b2_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l_Lake_instInhabitedPattern_default__1___closed__1;
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_instInhabitedPattern___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lake_instInhabitedPattern_default__1(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1401_;
}
pub unsafe fn l_Lake_instInhabitedPattern(
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0_once),
        _init_l_Lake_instInhabitedPattern___closed__0,
    );
    return v___x_1404_;
}
pub unsafe fn _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0_once),
        _init_l_Lake_instInhabitedPattern___closed__0,
    );
    v___x_1406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Lake_instInhabitedPatternDescr_default__1(
    mut v_00_u03b1_1407_: *mut leanh::LeanObject,
    mut v_00_u03b2_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr_default__1___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr_default__1___closed__0_once),
        _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0,
    );
    return v___x_1409_;
}
pub unsafe fn _init_l_Lake_instInhabitedPatternDescr___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lake_instInhabitedPatternDescr_default__1(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1410_;
}
pub unsafe fn l_Lake_instInhabitedPatternDescr(
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr___closed__0_once),
        _init_l_Lake_instInhabitedPatternDescr___closed__0,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lake_instCoePatternDescr___lam__0(
    mut v_p_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1415_, 0, v_p_1414_);
    return v___x_1415_;
}
pub unsafe fn l_Lake_instCoePatternDescr(
    mut v_00_u03b2_1417_: *mut leanh::LeanObject,
    mut v_00_u03b1_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1419_ = l_Lake_instCoePatternDescr___closed__0;
    return v___f_1419_;
}
pub unsafe fn l_Lake_Pattern_matches___redArg(
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_self_1421_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_filter_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    v_filter_1422_ = leanh::lean_ctor_get(v_self_1421_, 0);
    leanh::lean_inc_ref(v_filter_1422_);
    leanh::lean_dec_ref(v_self_1421_);
    v___x_1423_ = leanh::lean_apply_1(v_filter_1422_, v_a_1420_);
    v___x_1424_ = (leanh::lean_unbox(v___x_1423_) as u8);
    return v___x_1424_;
}
pub unsafe fn l_Lake_Pattern_matches___redArg___boxed(
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_self_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lake_Pattern_matches___redArg(v_a_1425_, v_self_1426_);
    v_r_1428_ = leanh::lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Lake_Pattern_matches(
    mut v_00_u03b1_1429_: *mut leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut leanh::LeanObject,
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_self_1432_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_filter_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    v_filter_1433_ = leanh::lean_ctor_get(v_self_1432_, 0);
    leanh::lean_inc_ref(v_filter_1433_);
    leanh::lean_dec_ref(v_self_1432_);
    v___x_1434_ = leanh::lean_apply_1(v_filter_1433_, v_a_1431_);
    v___x_1435_ = (leanh::lean_unbox(v___x_1434_) as u8);
    return v___x_1435_;
}
pub unsafe fn l_Lake_Pattern_matches___boxed(
    mut v_00_u03b1_1436_: *mut leanh::LeanObject,
    mut v_00_u03b2_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_self_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1440_: u8 = 0;
    let mut v_r_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ =
        l_Lake_Pattern_matches(v_00_u03b1_1436_, v_00_u03b2_1437_, v_a_1438_, v_self_1439_);
    v_r_1441_ = leanh::lean_box((v_res_1440_) as usize);
    return v_r_1441_;
}
pub unsafe fn l_Lake_instIsPatternPattern___lam__0(
    mut v_self_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_filter_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    v_filter_1444_ = leanh::lean_ctor_get(v_self_1442_, 0);
    leanh::lean_inc_ref(v_filter_1444_);
    leanh::lean_dec_ref(v_self_1442_);
    v___x_1445_ = leanh::lean_apply_1(v_filter_1444_, v___y_1443_);
    v___x_1446_ = (leanh::lean_unbox(v___x_1445_) as u8);
    return v___x_1446_;
}
pub unsafe fn l_Lake_instIsPatternPattern___lam__0___boxed(
    mut v_self_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: u8 = 0;
    let mut v_r_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Lake_instIsPatternPattern___lam__0(v_self_1447_, v___y_1448_);
    v_r_1450_ = leanh::lean_box((v_res_1449_) as usize);
    return v_r_1450_;
}
pub unsafe fn l_Lake_instIsPatternPattern(
    mut v_00_u03b1_1452_: *mut leanh::LeanObject,
    mut v_00_u03b2_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1454_ = l_Lake_instIsPatternPattern___closed__0;
    return v___f_1454_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__0(
    mut v_val_1455_: *mut leanh::LeanObject,
    mut v___x_1456_: u8,
    mut v_v_1457_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_filter_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    v_filter_1458_ = leanh::lean_ctor_get(v_v_1457_, 0);
    leanh::lean_inc_ref(v_filter_1458_);
    leanh::lean_dec_ref(v_v_1457_);
    v___x_1459_ = leanh::lean_apply_1(v_filter_1458_, v_val_1455_);
    v___x_1460_ = (leanh::lean_unbox(v___x_1459_) as u8);
    if v___x_1460_ == 0 {
        return v___x_1456_;
    } else {
        let mut v___x_1461_: u8 = 0;
        v___x_1461_ = 0;
        return v___x_1461_;
    }
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__0___boxed(
    mut v_val_1462_: *mut leanh::LeanObject,
    mut v___x_1463_: *mut leanh::LeanObject,
    mut v_v_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_220__boxed_1465_: u8 = 0;
    let mut v_res_1466_: u8 = 0;
    let mut v_r_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_220__boxed_1465_ = (leanh::lean_unbox(v___x_1463_) as u8);
    v_res_1466_ = l_Lake_PatternDescr_matches___redArg___lam__0(
        v_val_1462_,
        v___x_220__boxed_1465_,
        v_v_1464_,
    );
    v_r_1467_ = leanh::lean_box((v_res_1466_) as usize);
    return v_r_1467_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__1(
    mut v_val_1468_: *mut leanh::LeanObject,
    mut v_x_1469_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_filter_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: u8 = 0;
    v_filter_1470_ = leanh::lean_ctor_get(v_x_1469_, 0);
    leanh::lean_inc_ref(v_filter_1470_);
    leanh::lean_dec_ref(v_x_1469_);
    v___x_1471_ = leanh::lean_apply_1(v_filter_1470_, v_val_1468_);
    v___x_1472_ = (leanh::lean_unbox(v___x_1471_) as u8);
    return v___x_1472_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__1___boxed(
    mut v_val_1473_: *mut leanh::LeanObject,
    mut v_x_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1475_: u8 = 0;
    let mut v_r_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_1473_, v_x_1474_);
    v_r_1476_ = leanh::lean_box((v_res_1475_) as usize);
    return v_r_1476_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg(
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_val_1497_: *mut leanh::LeanObject,
    mut v_self_1498_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_self_1498_) {
        0 => {
            let mut v_p_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_filter_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1502_: u8 = 0;
            leanh::lean_dec_ref(v_inst_1496_);
            v_p_1499_ = leanh::lean_ctor_get(v_self_1498_, 0);
            leanh::lean_inc_ref(v_p_1499_);
            leanh::lean_dec_ref_known(v_self_1498_, 1);
            v_filter_1500_ = leanh::lean_ctor_get(v_p_1499_, 0);
            leanh::lean_inc_ref(v_filter_1500_);
            leanh::lean_dec_ref(v_p_1499_);
            v___x_1501_ = leanh::lean_apply_1(v_filter_1500_, v_val_1497_);
            v___x_1502_ = (leanh::lean_unbox(v___x_1501_) as u8);
            if v___x_1502_ == 0 {
                let mut v___x_1503_: u8 = 0;
                v___x_1503_ = 1;
                return v___x_1503_;
            } else {
                let mut v___x_1504_: u8 = 0;
                v___x_1504_ = 0;
                return v___x_1504_;
            }
        }
        1 => {
            let mut v_ps_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1509_: u8 = 0;
            leanh::lean_dec_ref(v_inst_1496_);
            v_ps_1505_ = leanh::lean_ctor_get(v_self_1498_, 0);
            leanh::lean_inc_ref(v_ps_1505_);
            leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1506_ = leanh::lean_unsigned_to_nat(0);
            v___x_1507_ = lean_array_get_size(v_ps_1505_);
            v___x_1508_ = l_Lake_PatternDescr_matches___redArg___closed__9;
            v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
            if v___x_1509_ == 0 {
                let mut v___x_1510_: u8 = 0;
                leanh::lean_dec_ref(v_ps_1505_);
                leanh::lean_dec(v_val_1497_);
                v___x_1510_ = 1;
                return v___x_1510_;
            } else {
                if v___x_1509_ == 0 {
                    leanh::lean_dec_ref(v_ps_1505_);
                    leanh::lean_dec(v_val_1497_);
                    return v___x_1509_;
                } else {
                    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1513_: usize = 0;
                    let mut v___x_1514_: usize = 0;
                    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1516_: u8 = 0;
                    v___x_1511_ = leanh::lean_box((v___x_1509_) as usize);
                    v___f_1512_ = leanh::lean_alloc_closure(
                        l_Lake_PatternDescr_matches___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1512_, 0, v_val_1497_);
                    leanh::lean_closure_set(v___f_1512_, 1, v___x_1511_);
                    v___x_1513_ = 0usize;
                    v___x_1514_ = lean_usize_of_nat(v___x_1507_);
                    v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1508_,
                        v___f_1512_,
                        v_ps_1505_,
                        v___x_1513_,
                        v___x_1514_,
                    );
                    v___x_1516_ = (leanh::lean_unbox(v___x_1515_) as u8);
                    leanh::lean_dec(v___x_1515_);
                    if v___x_1516_ == 0 {
                        return v___x_1509_;
                    } else {
                        let mut v___x_1517_: u8 = 0;
                        v___x_1517_ = 0;
                        return v___x_1517_;
                    }
                }
            }
        }
        2 => {
            let mut v_ps_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1522_: u8 = 0;
            leanh::lean_dec_ref(v_inst_1496_);
            v_ps_1518_ = leanh::lean_ctor_get(v_self_1498_, 0);
            leanh::lean_inc_ref(v_ps_1518_);
            leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1519_ = leanh::lean_unsigned_to_nat(0);
            v___x_1520_ = lean_array_get_size(v_ps_1518_);
            v___x_1521_ = l_Lake_PatternDescr_matches___redArg___closed__9;
            v___x_1522_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
            if v___x_1522_ == 0 {
                leanh::lean_dec_ref(v_ps_1518_);
                leanh::lean_dec(v_val_1497_);
                return v___x_1522_;
            } else {
                if v___x_1522_ == 0 {
                    leanh::lean_dec_ref(v_ps_1518_);
                    leanh::lean_dec(v_val_1497_);
                    return v___x_1522_;
                } else {
                    let mut v___f_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1524_: usize = 0;
                    let mut v___x_1525_: usize = 0;
                    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1527_: u8 = 0;
                    v___f_1523_ = leanh::lean_alloc_closure(
                        l_Lake_PatternDescr_matches___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1523_, 0, v_val_1497_);
                    v___x_1524_ = 0usize;
                    v___x_1525_ = lean_usize_of_nat(v___x_1520_);
                    v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1521_,
                        v___f_1523_,
                        v_ps_1518_,
                        v___x_1524_,
                        v___x_1525_,
                    );
                    v___x_1527_ = (leanh::lean_unbox(v___x_1526_) as u8);
                    leanh::lean_dec(v___x_1526_);
                    return v___x_1527_;
                }
            }
        }
        _ => {
            let mut v_p_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1530_: u8 = 0;
            v_p_1528_ = leanh::lean_ctor_get(v_self_1498_, 0);
            leanh::lean_inc(v_p_1528_);
            leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1529_ = leanh::lean_apply_2(v_inst_1496_, v_p_1528_, v_val_1497_);
            v___x_1530_ = (leanh::lean_unbox(v___x_1529_) as u8);
            return v___x_1530_;
        }
    }
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___boxed(
    mut v_inst_1531_: *mut leanh::LeanObject,
    mut v_val_1532_: *mut leanh::LeanObject,
    mut v_self_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1534_: u8 = 0;
    let mut v_r_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lake_PatternDescr_matches___redArg(v_inst_1531_, v_val_1532_, v_self_1533_);
    v_r_1535_ = leanh::lean_box((v_res_1534_) as usize);
    return v_r_1535_;
}
pub unsafe fn l_Lake_PatternDescr_matches(
    mut v_00_u03b2_1536_: *mut leanh::LeanObject,
    mut v_00_u03b1_1537_: *mut leanh::LeanObject,
    mut v_inst_1538_: *mut leanh::LeanObject,
    mut v_val_1539_: *mut leanh::LeanObject,
    mut v_self_1540_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1541_: u8 = 0;
    v___x_1541_ = l_Lake_PatternDescr_matches___redArg(v_inst_1538_, v_val_1539_, v_self_1540_);
    return v___x_1541_;
}
pub unsafe fn l_Lake_PatternDescr_matches___boxed(
    mut v_00_u03b2_1542_: *mut leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_val_1545_: *mut leanh::LeanObject,
    mut v_self_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1547_: u8 = 0;
    let mut v_r_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_Lake_PatternDescr_matches(
        v_00_u03b2_1542_,
        v_00_u03b1_1543_,
        v_inst_1544_,
        v_val_1545_,
        v_self_1546_,
    );
    v_r_1548_ = leanh::lean_box((v_res_1547_) as usize);
    return v_r_1548_;
}
pub unsafe fn l_Lake_instIsPatternPatternDescr___redArg(
    mut v_inst_1549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1550_ = leanh::lean_alloc_closure(
        l_Lake_PatternDescr_matches___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_1550_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1550_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1550_, 2, v_inst_1549_);
    v___x_1551_ = leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1551_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1551_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1551_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1551_, 3, v___x_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Lake_instIsPatternPatternDescr(
    mut v_00_u03b2_1552_: *mut leanh::LeanObject,
    mut v_00_u03b1_1553_: *mut leanh::LeanObject,
    mut v_inst_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lake_Pattern_ofFn___redArg(
    mut v_f_1556_: *mut leanh::LeanObject,
    mut v_name_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = leanh::lean_box(0);
    v___x_1559_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1559_, 0, v_f_1556_);
    leanh::lean_ctor_set(v___x_1559_, 1, v_name_1557_);
    leanh::lean_ctor_set(v___x_1559_, 2, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_Pattern_ofFn(
    mut v_00_u03b1_1560_: *mut leanh::LeanObject,
    mut v_00_u03b2_1561_: *mut leanh::LeanObject,
    mut v_f_1562_: *mut leanh::LeanObject,
    mut v_name_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = leanh::lean_box(0);
    v___x_1565_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1565_, 0, v_f_1562_);
    leanh::lean_ctor_set(v___x_1565_, 1, v_name_1563_);
    leanh::lean_ctor_set(v___x_1565_, 2, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lake_instCoeForallBoolPattern___lam__0(
    mut v_f_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = leanh::lean_box(0);
    v___x_1568_ = leanh::lean_box(0);
    v___x_1569_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1569_, 0, v_f_1566_);
    leanh::lean_ctor_set(v___x_1569_, 1, v___x_1567_);
    leanh::lean_ctor_set(v___x_1569_, 2, v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Lake_instCoeForallBoolPattern(
    mut v_00_u03b1_1571_: *mut leanh::LeanObject,
    mut v_00_u03b2_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1573_ = l_Lake_instCoeForallBoolPattern___closed__0;
    return v___f_1573_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg___lam__0(
    mut v_inst_1574_: *mut leanh::LeanObject,
    mut v_descr_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1577_: u8 = 0;
    v___x_1577_ = l_Lake_PatternDescr_matches___redArg(v_inst_1574_, v_x_1576_, v_descr_1575_);
    return v___x_1577_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_descr_1579_: *mut leanh::LeanObject,
    mut v_x_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1581_: u8 = 0;
    let mut v_r_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_1578_, v_descr_1579_, v_x_1580_);
    v_r_1582_ = leanh::lean_box((v_res_1581_) as usize);
    return v_r_1582_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg(
    mut v_inst_1583_: *mut leanh::LeanObject,
    mut v_descr_1584_: *mut leanh::LeanObject,
    mut v_name_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_descr_1584_);
    v___f_1586_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_ofDescr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1586_, 0, v_inst_1583_);
    leanh::lean_closure_set(v___f_1586_, 1, v_descr_1584_);
    v___x_1587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1587_, 0, v_descr_1584_);
    v___x_1588_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1588_, 0, v___f_1586_);
    leanh::lean_ctor_set(v___x_1588_, 1, v_name_1585_);
    leanh::lean_ctor_set(v___x_1588_, 2, v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Lake_Pattern_ofDescr(
    mut v_00_u03b2_1589_: *mut leanh::LeanObject,
    mut v_00_u03b1_1590_: *mut leanh::LeanObject,
    mut v_inst_1591_: *mut leanh::LeanObject,
    mut v_descr_1592_: *mut leanh::LeanObject,
    mut v_name_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_descr_1592_);
    v___f_1594_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_ofDescr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1594_, 0, v_inst_1591_);
    leanh::lean_closure_set(v___f_1594_, 1, v_descr_1592_);
    v___x_1595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1595_, 0, v_descr_1592_);
    v___x_1596_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1596_, 0, v___f_1594_);
    leanh::lean_ctor_set(v___x_1596_, 1, v_name_1593_);
    leanh::lean_ctor_set(v___x_1596_, 2, v___x_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(
    mut v_inst_1597_: *mut leanh::LeanObject,
    mut v_x_1598_: *mut leanh::LeanObject,
    mut v_x_1599_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1600_: u8 = 0;
    v___x_1600_ = l_Lake_PatternDescr_matches___redArg(v_inst_1597_, v_x_1599_, v_x_1598_);
    return v___x_1600_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(
    mut v_inst_1601_: *mut leanh::LeanObject,
    mut v_x_1602_: *mut leanh::LeanObject,
    mut v_x_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1604_: u8 = 0;
    let mut v_r_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(
        v_inst_1601_,
        v_x_1602_,
        v_x_1603_,
    );
    v_r_1605_ = leanh::lean_box((v_res_1604_) as usize);
    return v_r_1605_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_x_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_1607_);
    v___f_1608_ = leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1608_, 0, v_inst_1606_);
    leanh::lean_closure_set(v___f_1608_, 1, v_x_1607_);
    v___x_1609_ = leanh::lean_box(0);
    v___x_1610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1610_, 0, v_x_1607_);
    v___x_1611_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1611_, 0, v___f_1608_);
    leanh::lean_ctor_set(v___x_1611_, 1, v___x_1609_);
    leanh::lean_ctor_set(v___x_1611_, 2, v___x_1610_);
    return v___x_1611_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(
    mut v_inst_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1613_ = leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1613_, 0, v_inst_1612_);
    return v___f_1613_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern(
    mut v_00_u03b2_1614_: *mut leanh::LeanObject,
    mut v_00_u03b1_1615_: *mut leanh::LeanObject,
    mut v_inst_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1617_ = leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1617_, 0, v_inst_1616_);
    return v___f_1617_;
}
pub unsafe fn l_Lake_Pattern_not___redArg___lam__0(
    mut v_inst_1618_: *mut leanh::LeanObject,
    mut v___x_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1621_: u8 = 0;
    v___x_1621_ = l_Lake_PatternDescr_matches___redArg(v_inst_1618_, v_x_1620_, v___x_1619_);
    return v___x_1621_;
}
pub unsafe fn l_Lake_Pattern_not___redArg___lam__0___boxed(
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v___x_1623_: *mut leanh::LeanObject,
    mut v_x_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1625_: u8 = 0;
    let mut v_r_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_1622_, v___x_1623_, v_x_1624_);
    v_r_1626_ = leanh::lean_box((v_res_1625_) as usize);
    return v_r_1626_;
}
pub unsafe fn l_Lake_Pattern_not___redArg(
    mut v_inst_1627_: *mut leanh::LeanObject,
    mut v_p_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1629_, 0, v_p_1628_);
    leanh::lean_inc_ref(v___x_1629_);
    v___f_1630_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1630_, 0, v_inst_1627_);
    leanh::lean_closure_set(v___f_1630_, 1, v___x_1629_);
    v___x_1631_ = leanh::lean_box(0);
    v___x_1632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1632_, 0, v___x_1629_);
    v___x_1633_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1633_, 0, v___f_1630_);
    leanh::lean_ctor_set(v___x_1633_, 1, v___x_1631_);
    leanh::lean_ctor_set(v___x_1633_, 2, v___x_1632_);
    return v___x_1633_;
}
pub unsafe fn l_Lake_Pattern_not(
    mut v_00_u03b2_1634_: *mut leanh::LeanObject,
    mut v_00_u03b1_1635_: *mut leanh::LeanObject,
    mut v_inst_1636_: *mut leanh::LeanObject,
    mut v_p_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1638_, 0, v_p_1637_);
    leanh::lean_inc_ref(v___x_1638_);
    v___f_1639_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1639_, 0, v_inst_1636_);
    leanh::lean_closure_set(v___f_1639_, 1, v___x_1638_);
    v___x_1640_ = leanh::lean_box(0);
    v___x_1641_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1641_, 0, v___x_1638_);
    v___x_1642_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1642_, 0, v___f_1639_);
    leanh::lean_ctor_set(v___x_1642_, 1, v___x_1640_);
    leanh::lean_ctor_set(v___x_1642_, 2, v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lake_Pattern_all___redArg(
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_ps_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1645_, 0, v_ps_1644_);
    leanh::lean_inc_ref(v___x_1645_);
    v___f_1646_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1646_, 0, v_inst_1643_);
    leanh::lean_closure_set(v___f_1646_, 1, v___x_1645_);
    v___x_1647_ = leanh::lean_box(0);
    v___x_1648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1648_, 0, v___x_1645_);
    v___x_1649_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1649_, 0, v___f_1646_);
    leanh::lean_ctor_set(v___x_1649_, 1, v___x_1647_);
    leanh::lean_ctor_set(v___x_1649_, 2, v___x_1648_);
    return v___x_1649_;
}
pub unsafe fn l_Lake_Pattern_all(
    mut v_00_u03b2_1650_: *mut leanh::LeanObject,
    mut v_00_u03b1_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_ps_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1654_, 0, v_ps_1653_);
    leanh::lean_inc_ref(v___x_1654_);
    v___f_1655_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1655_, 0, v_inst_1652_);
    leanh::lean_closure_set(v___f_1655_, 1, v___x_1654_);
    v___x_1656_ = leanh::lean_box(0);
    v___x_1657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1657_, 0, v___x_1654_);
    v___x_1658_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1658_, 0, v___f_1655_);
    leanh::lean_ctor_set(v___x_1658_, 1, v___x_1656_);
    leanh::lean_ctor_set(v___x_1658_, 2, v___x_1657_);
    return v___x_1658_;
}
pub unsafe fn l_Lake_Pattern_any___redArg(
    mut v_inst_1659_: *mut leanh::LeanObject,
    mut v_ps_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1661_, 0, v_ps_1660_);
    leanh::lean_inc_ref(v___x_1661_);
    v___f_1662_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1662_, 0, v_inst_1659_);
    leanh::lean_closure_set(v___f_1662_, 1, v___x_1661_);
    v___x_1663_ = leanh::lean_box(0);
    v___x_1664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1664_, 0, v___x_1661_);
    v___x_1665_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1665_, 0, v___f_1662_);
    leanh::lean_ctor_set(v___x_1665_, 1, v___x_1663_);
    leanh::lean_ctor_set(v___x_1665_, 2, v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn l_Lake_Pattern_any(
    mut v_00_u03b2_1666_: *mut leanh::LeanObject,
    mut v_00_u03b1_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_ps_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1670_, 0, v_ps_1669_);
    leanh::lean_inc_ref(v___x_1670_);
    v___f_1671_ = leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1671_, 0, v_inst_1668_);
    leanh::lean_closure_set(v___f_1671_, 1, v___x_1670_);
    v___x_1672_ = leanh::lean_box(0);
    v___x_1673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1673_, 0, v___x_1670_);
    v___x_1674_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1674_, 0, v___f_1671_);
    leanh::lean_ctor_set(v___x_1674_, 1, v___x_1672_);
    leanh::lean_ctor_set(v___x_1674_, 2, v___x_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Lake_PatternDescr_empty(
    mut v_00_u03b1_1679_: *mut leanh::LeanObject,
    mut v_00_u03b2_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lake_PatternDescr_empty___closed__1;
    return v___x_1681_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Lake_PatternDescr_empty(leanh::lean_box(0), leanh::lean_box(0));
    return v___x_1685_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2_once),
        _init_l_Lake_Pattern_empty___closed__2,
    );
    v___x_1687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__3_once),
        _init_l_Lake_Pattern_empty___closed__3,
    );
    v___x_1689_ = l_Lake_Pattern_empty___closed__1;
    v___f_1690_ = l_Lake_instInhabitedPattern_default__1___closed__0;
    v___x_1691_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1691_, 0, v___f_1690_);
    leanh::lean_ctor_set(v___x_1691_, 1, v___x_1689_);
    leanh::lean_ctor_set(v___x_1691_, 2, v___x_1688_);
    return v___x_1691_;
}
pub unsafe fn l_Lake_Pattern_empty(
    mut v_00_u03b1_1692_: *mut leanh::LeanObject,
    mut v_00_u03b2_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__4_once),
        _init_l_Lake_Pattern_empty___closed__4,
    );
    return v___x_1694_;
}
pub unsafe fn l_Lake_instEmptyCollectionPatternDescr(
    mut v_00_u03b1_1695_: *mut leanh::LeanObject,
    mut v_00_u03b2_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2_once),
        _init_l_Lake_Pattern_empty___closed__2,
    );
    return v___x_1697_;
}
pub unsafe fn _init_l_Lake_instEmptyCollectionPattern___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lake_Pattern_empty(leanh::lean_box(0), leanh::lean_box(0));
    return v___x_1698_;
}
pub unsafe fn l_Lake_instEmptyCollectionPattern(
    mut v_00_u03b1_1699_: *mut leanh::LeanObject,
    mut v_00_u03b2_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instEmptyCollectionPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instEmptyCollectionPattern___closed__0_once),
        _init_l_Lake_instEmptyCollectionPattern___closed__0,
    );
    return v___x_1701_;
}
pub unsafe fn l_Lake_PatternDescr_star(
    mut v_00_u03b1_1704_: *mut leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lake_PatternDescr_star___closed__0;
    return v___x_1706_;
}
pub unsafe fn l_Lake_Pattern_star___lam__0(mut v_x_1707_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1708_: u8 = 0;
    v___x_1708_ = 1;
    return v___x_1708_;
}
pub unsafe fn l_Lake_Pattern_star___lam__0___boxed(
    mut v_x_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1710_: u8 = 0;
    let mut v_r_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lake_Pattern_star___lam__0(v_x_1709_);
    leanh::lean_dec(v_x_1709_);
    v_r_1711_ = leanh::lean_box((v_res_1710_) as usize);
    return v_r_1711_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Lake_PatternDescr_star(leanh::lean_box(0), leanh::lean_box(0));
    return v___x_1716_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__3_once),
        _init_l_Lake_Pattern_star___closed__3,
    );
    v___x_1718_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__4_once),
        _init_l_Lake_Pattern_star___closed__4,
    );
    v___x_1720_ = l_Lake_Pattern_star___closed__2;
    v___f_1721_ = l_Lake_Pattern_star___closed__0;
    v___x_1722_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1722_, 0, v___f_1721_);
    leanh::lean_ctor_set(v___x_1722_, 1, v___x_1720_);
    leanh::lean_ctor_set(v___x_1722_, 2, v___x_1719_);
    return v___x_1722_;
}
pub unsafe fn l_Lake_Pattern_star(
    mut v_00_u03b1_1723_: *mut leanh::LeanObject,
    mut v_00_u03b2_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__5_once),
        _init_l_Lake_Pattern_star___closed__5,
    );
    return v___x_1725_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorIdx(
    mut v_x_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1726_) {
        0 => {
            let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1727_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1727_;
        }
        1 => {
            let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1728_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1728_;
        }
        _ => {
            let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1729_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1729_;
        }
    }
}
pub unsafe fn l_Lake_StrPatDescr_ctorIdx___boxed(
    mut v_x_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lake_StrPatDescr_ctorIdx(v_x_1730_);
    leanh::lean_dec_ref(v_x_1730_);
    return v_res_1731_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim___redArg(
    mut v_t_1732_: *mut leanh::LeanObject,
    mut v_k_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_xs_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_xs_1734_ = leanh::lean_ctor_get(v_t_1732_, 0);
    leanh::lean_inc_ref(v_xs_1734_);
    leanh::lean_dec_ref(v_t_1732_);
    v___x_1735_ = leanh::lean_apply_1(v_k_1733_, v_xs_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim(
    mut v_motive_1736_: *mut leanh::LeanObject,
    mut v_ctorIdx_1737_: *mut leanh::LeanObject,
    mut v_t_1738_: *mut leanh::LeanObject,
    mut v_h_1739_: *mut leanh::LeanObject,
    mut v_k_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1738_, v_k_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim___boxed(
    mut v_motive_1742_: *mut leanh::LeanObject,
    mut v_ctorIdx_1743_: *mut leanh::LeanObject,
    mut v_t_1744_: *mut leanh::LeanObject,
    mut v_h_1745_: *mut leanh::LeanObject,
    mut v_k_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lake_StrPatDescr_ctorElim(
        v_motive_1742_,
        v_ctorIdx_1743_,
        v_t_1744_,
        v_h_1745_,
        v_k_1746_,
    );
    leanh::lean_dec(v_ctorIdx_1743_);
    return v_res_1747_;
}
pub unsafe fn l_Lake_StrPatDescr_mem_elim___redArg(
    mut v_t_1748_: *mut leanh::LeanObject,
    mut v_mem_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1748_, v_mem_1749_);
    return v___x_1750_;
}
pub unsafe fn l_Lake_StrPatDescr_mem_elim(
    mut v_motive_1751_: *mut leanh::LeanObject,
    mut v_t_1752_: *mut leanh::LeanObject,
    mut v_h_1753_: *mut leanh::LeanObject,
    mut v_mem_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1752_, v_mem_1754_);
    return v___x_1755_;
}
pub unsafe fn l_Lake_StrPatDescr_startsWith_elim___redArg(
    mut v_t_1756_: *mut leanh::LeanObject,
    mut v_startsWith_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1756_, v_startsWith_1757_);
    return v___x_1758_;
}
pub unsafe fn l_Lake_StrPatDescr_startsWith_elim(
    mut v_motive_1759_: *mut leanh::LeanObject,
    mut v_t_1760_: *mut leanh::LeanObject,
    mut v_h_1761_: *mut leanh::LeanObject,
    mut v_startsWith_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1760_, v_startsWith_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Lake_StrPatDescr_endsWith_elim___redArg(
    mut v_t_1764_: *mut leanh::LeanObject,
    mut v_endsWith_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1764_, v_endsWith_1765_);
    return v___x_1766_;
}
pub unsafe fn l_Lake_StrPatDescr_endsWith_elim(
    mut v_motive_1767_: *mut leanh::LeanObject,
    mut v_t_1768_: *mut leanh::LeanObject,
    mut v_h_1769_: *mut leanh::LeanObject,
    mut v_endsWith_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1768_, v_endsWith_1770_);
    return v___x_1771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_as_1779_: *mut leanh::LeanObject,
    mut v_i_1780_: usize,
    mut v_stop_1781_: usize,
) -> u8 {
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1782_ = lean_usize_dec_eq(v_i_1780_, v_stop_1781_);
                if v___x_1782_ == 0 {
                    v___x_1783_ = lean_array_uget_borrowed(v_as_1779_, v_i_1780_);
                    v___x_1784_ = lean_string_dec_eq(v_a_1778_, v___x_1783_);
                    if v___x_1784_ == 0 {
                        v___x_1785_ = 1usize;
                        v___x_1786_ = lean_usize_add(v_i_1780_, v___x_1785_);
                        v_i_1780_ = v___x_1786_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1784_;
                    }
                } else {
                    v___x_1788_ = 0;
                    return v___x_1788_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_as_1790_: *mut leanh::LeanObject,
    mut v_i_1791_: *mut leanh::LeanObject,
    mut v_stop_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1793_: usize = 0;
    let mut v_stop_boxed_1794_: usize = 0;
    let mut v_res_1795_: u8 = 0;
    let mut v_r_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1793_ = leanh::lean_unbox_usize(v_i_1791_);
    leanh::lean_dec(v_i_1791_);
    v_stop_boxed_1794_ = leanh::lean_unbox_usize(v_stop_1792_);
    leanh::lean_dec(v_stop_1792_);
    v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_1789_, v_as_1790_, v_i_boxed_1793_, v_stop_boxed_1794_);
    leanh::lean_dec_ref(v_as_1790_);
    leanh::lean_dec_ref(v_a_1789_);
    v_r_1796_ = leanh::lean_box((v_res_1795_) as usize);
    return v_r_1796_;
}
pub unsafe fn l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(
    mut v_as_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    v___x_1799_ = leanh::lean_unsigned_to_nat(0);
    v___x_1800_ = lean_array_get_size(v_as_1797_);
    v___x_1801_ = lean_nat_dec_lt(v___x_1799_, v___x_1800_);
    if v___x_1801_ == 0 {
        return v___x_1801_;
    } else {
        if v___x_1801_ == 0 {
            return v___x_1801_;
        } else {
            let mut v___x_1802_: usize = 0;
            let mut v___x_1803_: usize = 0;
            let mut v___x_1804_: u8 = 0;
            v___x_1802_ = 0usize;
            v___x_1803_ = lean_usize_of_nat(v___x_1800_);
            v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_1798_, v_as_1797_, v___x_1802_, v___x_1803_);
            return v___x_1804_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(
    mut v_as_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1807_: u8 = 0;
    let mut v_r_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_1805_, v_a_1806_);
    leanh::lean_dec_ref(v_a_1806_);
    leanh::lean_dec_ref(v_as_1805_);
    v_r_1808_ = leanh::lean_box((v_res_1807_) as usize);
    return v_r_1808_;
}
pub unsafe fn l_Lake_StrPatDescr_matches(
    mut v_s_1809_: *mut leanh::LeanObject,
    mut v_self_1810_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_self_1810_) {
        0 => {
            let mut v_xs_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1812_: u8 = 0;
            v_xs_1811_ = leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1812_ =
                l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_1811_, v_s_1809_);
            return v___x_1812_;
        }
        1 => {
            let mut v_affix_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1816_: u8 = 0;
            v_affix_1813_ = leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1814_ = lean_string_utf8_byte_size(v_s_1809_);
            v___x_1815_ = lean_string_utf8_byte_size(v_affix_1813_);
            v___x_1816_ = lean_nat_dec_le(v___x_1815_, v___x_1814_);
            if v___x_1816_ == 0 {
                return v___x_1816_;
            } else {
                let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1818_: u8 = 0;
                v___x_1817_ = leanh::lean_unsigned_to_nat(0);
                v___x_1818_ = lean_string_memcmp(
                    v_s_1809_,
                    v_affix_1813_,
                    v___x_1817_,
                    v___x_1817_,
                    v___x_1815_,
                );
                return v___x_1818_;
            }
        }
        _ => {
            let mut v_affix_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1822_: u8 = 0;
            v_affix_1819_ = leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1820_ = lean_string_utf8_byte_size(v_s_1809_);
            v___x_1821_ = lean_string_utf8_byte_size(v_affix_1819_);
            v___x_1822_ = lean_nat_dec_le(v___x_1821_, v___x_1820_);
            if v___x_1822_ == 0 {
                return v___x_1822_;
            } else {
                let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1825_: u8 = 0;
                v___x_1823_ = leanh::lean_unsigned_to_nat(0);
                v___x_1824_ = lean_nat_sub(v___x_1820_, v___x_1821_);
                v___x_1825_ = lean_string_memcmp(
                    v_s_1809_,
                    v_affix_1819_,
                    v___x_1824_,
                    v___x_1823_,
                    v___x_1821_,
                );
                leanh::lean_dec(v___x_1824_);
                return v___x_1825_;
            }
        }
    }
}
pub unsafe fn l_Lake_StrPatDescr_matches___boxed(
    mut v_s_1826_: *mut leanh::LeanObject,
    mut v_self_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1828_: u8 = 0;
    let mut v_r_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lake_StrPatDescr_matches(v_s_1826_, v_self_1827_);
    leanh::lean_dec_ref(v_self_1827_);
    leanh::lean_dec_ref(v_s_1826_);
    v_r_1829_ = leanh::lean_box((v_res_1828_) as usize);
    return v_r_1829_;
}
pub unsafe fn l_Lake_StrPat_mem___lam__0(
    mut v___x_1834_: *mut leanh::LeanObject,
    mut v___x_1835_: *mut leanh::LeanObject,
    mut v_x_1836_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1837_: u8 = 0;
    v___x_1837_ = l_Lake_PatternDescr_matches___redArg(v___x_1834_, v_x_1836_, v___x_1835_);
    return v___x_1837_;
}
pub unsafe fn l_Lake_StrPat_mem___lam__0___boxed(
    mut v___x_1838_: *mut leanh::LeanObject,
    mut v___x_1839_: *mut leanh::LeanObject,
    mut v_x_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1841_: u8 = 0;
    let mut v_r_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Lake_StrPat_mem___lam__0(v___x_1838_, v___x_1839_, v_x_1840_);
    v_r_1842_ = leanh::lean_box((v_res_1841_) as usize);
    return v_r_1842_;
}
pub unsafe fn l_Lake_StrPat_mem(
    mut v_xs_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1845_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1845_, 0, v_xs_1843_);
    v___x_1846_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1846_, 0, v___x_1845_);
    leanh::lean_inc_ref(v___x_1846_);
    v___f_1847_ = leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1847_, 0, v___x_1844_);
    leanh::lean_closure_set(v___f_1847_, 1, v___x_1846_);
    v___x_1848_ = leanh::lean_box(0);
    v___x_1849_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1849_, 0, v___x_1846_);
    v___x_1850_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1850_, 0, v___f_1847_);
    leanh::lean_ctor_set(v___x_1850_, 1, v___x_1848_);
    leanh::lean_ctor_set(v___x_1850_, 2, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Lake_instCoeArrayStringStrPatDescr___lam__0(
    mut v_xs_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1852_, 0, v_xs_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lake_StrPat_startsWith(
    mut v_affix_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1859_, 0, v_affix_1857_);
    v___x_1860_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    leanh::lean_inc_ref(v___x_1860_);
    v___f_1861_ = leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1861_, 0, v___x_1858_);
    leanh::lean_closure_set(v___f_1861_, 1, v___x_1860_);
    v___x_1862_ = leanh::lean_box(0);
    v___x_1863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1860_);
    v___x_1864_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1864_, 0, v___f_1861_);
    leanh::lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    leanh::lean_ctor_set(v___x_1864_, 2, v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l_Lake_StrPat_endsWith(
    mut v_affix_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1867_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1867_, 0, v_affix_1865_);
    v___x_1868_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    leanh::lean_inc_ref(v___x_1868_);
    v___f_1869_ = leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1869_, 0, v___x_1866_);
    leanh::lean_closure_set(v___f_1869_, 1, v___x_1868_);
    v___x_1870_ = leanh::lean_box(0);
    v___x_1871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1868_);
    v___x_1872_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1872_, 0, v___f_1869_);
    leanh::lean_ctor_set(v___x_1872_, 1, v___x_1870_);
    leanh::lean_ctor_set(v___x_1872_, 2, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn l_Lake_StrPatDescr_beq(
    mut v_s_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = leanh::lean_unsigned_to_nat(1);
    v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1874_);
    v___x_1876_ = lean_array_push(v___x_1875_, v_s_1873_);
    v___x_1877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1877_, 0, v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn l_Lake_StrPat_beq___lam__0(
    mut v_s_1878_: *mut leanh::LeanObject,
    mut v_x_1879_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1880_: u8 = 0;
    v___x_1880_ = lean_string_dec_eq(v_x_1879_, v_s_1878_);
    return v___x_1880_;
}
pub unsafe fn l_Lake_StrPat_beq___lam__0___boxed(
    mut v_s_1881_: *mut leanh::LeanObject,
    mut v_x_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1883_: u8 = 0;
    let mut v_r_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lake_StrPat_beq___lam__0(v_s_1881_, v_x_1882_);
    leanh::lean_dec_ref(v_x_1882_);
    leanh::lean_dec_ref(v_s_1881_);
    v_r_1884_ = leanh::lean_box((v_res_1883_) as usize);
    return v_r_1884_;
}
pub unsafe fn l_Lake_StrPat_beq(
    mut v_s_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_s_1888_);
    v___f_1889_ = leanh::lean_alloc_closure(
        l_Lake_StrPat_beq___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1889_, 0, v_s_1888_);
    v___x_1890_ = l_Lake_StrPat_beq___closed__1;
    v___x_1891_ = l_Lake_StrPatDescr_beq(v_s_1888_);
    v___x_1892_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    v___x_1893_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
    v___x_1894_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1894_, 0, v___f_1889_);
    leanh::lean_ctor_set(v___x_1894_, 1, v___x_1890_);
    leanh::lean_ctor_set(v___x_1894_, 2, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorIdx(
    mut v_x_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1899_) {
        0 => {
            let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1900_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1900_;
        }
        1 => {
            let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1901_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1901_;
        }
        _ => {
            let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1902_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1902_;
        }
    }
}
pub unsafe fn l_Lake_PathPatDescr_ctorIdx___boxed(
    mut v_x_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_Lake_PathPatDescr_ctorIdx(v_x_1903_);
    leanh::lean_dec_ref(v_x_1903_);
    return v_res_1904_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim___redArg(
    mut v_t_1905_: *mut leanh::LeanObject,
    mut v_k_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_1907_ = leanh::lean_ctor_get(v_t_1905_, 0);
    leanh::lean_inc_ref(v_p_1907_);
    leanh::lean_dec_ref(v_t_1905_);
    v___x_1908_ = leanh::lean_apply_1(v_k_1906_, v_p_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim(
    mut v_motive_1909_: *mut leanh::LeanObject,
    mut v_ctorIdx_1910_: *mut leanh::LeanObject,
    mut v_t_1911_: *mut leanh::LeanObject,
    mut v_h_1912_: *mut leanh::LeanObject,
    mut v_k_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1911_, v_k_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim___boxed(
    mut v_motive_1915_: *mut leanh::LeanObject,
    mut v_ctorIdx_1916_: *mut leanh::LeanObject,
    mut v_t_1917_: *mut leanh::LeanObject,
    mut v_h_1918_: *mut leanh::LeanObject,
    mut v_k_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lake_PathPatDescr_ctorElim(
        v_motive_1915_,
        v_ctorIdx_1916_,
        v_t_1917_,
        v_h_1918_,
        v_k_1919_,
    );
    leanh::lean_dec(v_ctorIdx_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Lake_PathPatDescr_path_elim___redArg(
    mut v_t_1921_: *mut leanh::LeanObject,
    mut v_path_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1921_, v_path_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Lake_PathPatDescr_path_elim(
    mut v_motive_1924_: *mut leanh::LeanObject,
    mut v_t_1925_: *mut leanh::LeanObject,
    mut v_h_1926_: *mut leanh::LeanObject,
    mut v_path_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1925_, v_path_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lake_PathPatDescr_extension_elim___redArg(
    mut v_t_1929_: *mut leanh::LeanObject,
    mut v_extension_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1929_, v_extension_1930_);
    return v___x_1931_;
}
pub unsafe fn l_Lake_PathPatDescr_extension_elim(
    mut v_motive_1932_: *mut leanh::LeanObject,
    mut v_t_1933_: *mut leanh::LeanObject,
    mut v_h_1934_: *mut leanh::LeanObject,
    mut v_extension_1935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1933_, v_extension_1935_);
    return v___x_1936_;
}
pub unsafe fn l_Lake_PathPatDescr_fileName_elim___redArg(
    mut v_t_1937_: *mut leanh::LeanObject,
    mut v_fileName_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1937_, v_fileName_1938_);
    return v___x_1939_;
}
pub unsafe fn l_Lake_PathPatDescr_fileName_elim(
    mut v_motive_1940_: *mut leanh::LeanObject,
    mut v_t_1941_: *mut leanh::LeanObject,
    mut v_h_1942_: *mut leanh::LeanObject,
    mut v_fileName_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1941_, v_fileName_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lake_instInhabitedPattern_default__1(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1945_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__0_once),
        _init_l_Lake_instInhabitedPathPatDescr_default___closed__0,
    );
    v___x_1947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1947_, 0, v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default() -> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__1_once),
        _init_l_Lake_instInhabitedPathPatDescr_default___closed__1,
    );
    return v___x_1948_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr() -> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lake_instInhabitedPathPatDescr_default;
    return v___x_1949_;
}
pub unsafe fn l_Lake_PathPatDescr_eq___lam__0(
    mut v_p_1950_: *mut leanh::LeanObject,
    mut v_x_1951_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1952_: u8 = 0;
    v___x_1952_ = lean_string_dec_eq(v_x_1951_, v_p_1950_);
    return v___x_1952_;
}
pub unsafe fn l_Lake_PathPatDescr_eq___lam__0___boxed(
    mut v_p_1953_: *mut leanh::LeanObject,
    mut v_x_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1955_: u8 = 0;
    let mut v_r_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lake_PathPatDescr_eq___lam__0(v_p_1953_, v_x_1954_);
    leanh::lean_dec_ref(v_x_1954_);
    leanh::lean_dec_ref(v_p_1953_);
    v_r_1956_ = leanh::lean_box((v_res_1955_) as usize);
    return v_r_1956_;
}
pub unsafe fn l_Lake_PathPatDescr_eq(
    mut v_p_1957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_p_1957_);
    v___f_1958_ = leanh::lean_alloc_closure(
        l_Lake_PathPatDescr_eq___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1958_, 0, v_p_1957_);
    v___x_1959_ = l_Lake_StrPat_beq___closed__1;
    v___x_1960_ = l_Lake_StrPatDescr_beq(v_p_1957_);
    v___x_1961_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1961_, 0, v___x_1960_);
    v___x_1962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    v___x_1963_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1963_, 0, v___f_1958_);
    leanh::lean_ctor_set(v___x_1963_, 1, v___x_1959_);
    leanh::lean_ctor_set(v___x_1963_, 2, v___x_1962_);
    v___x_1964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1964_, 0, v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn l_Lake_PathPatDescr_matches(
    mut v_path_1965_: *mut leanh::LeanObject,
    mut v_self_1966_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_self_1966_) {
        0 => {
            let mut v_p_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_filter_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1971_: u8 = 0;
            v_p_1967_ = leanh::lean_ctor_get(v_self_1966_, 0);
            leanh::lean_inc_ref(v_p_1967_);
            leanh::lean_dec_ref_known(v_self_1966_, 1);
            v_filter_1968_ = leanh::lean_ctor_get(v_p_1967_, 0);
            leanh::lean_inc_ref(v_filter_1968_);
            leanh::lean_dec_ref(v_p_1967_);
            v___x_1969_ = l_System_FilePath_normalize(v_path_1965_);
            v___x_1970_ = leanh::lean_apply_1(v_filter_1968_, v___x_1969_);
            v___x_1971_ = (leanh::lean_unbox(v___x_1970_) as u8);
            return v___x_1971_;
        }
        1 => {
            let mut v_p_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_p_1972_ = leanh::lean_ctor_get(v_self_1966_, 0);
            leanh::lean_inc_ref(v_p_1972_);
            leanh::lean_dec_ref_known(v_self_1966_, 1);
            v___x_1973_ = l_System_FilePath_extension(v_path_1965_);
            if leanh::lean_obj_tag(v___x_1973_) == 0 {
                let mut v___x_1974_: u8 = 0;
                leanh::lean_dec_ref(v_p_1972_);
                v___x_1974_ = 0;
                return v___x_1974_;
            } else {
                let mut v_val_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_filter_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1978_: u8 = 0;
                v_val_1975_ = leanh::lean_ctor_get(v___x_1973_, 0);
                leanh::lean_inc(v_val_1975_);
                leanh::lean_dec_ref_known(v___x_1973_, 1);
                v_filter_1976_ = leanh::lean_ctor_get(v_p_1972_, 0);
                leanh::lean_inc_ref(v_filter_1976_);
                leanh::lean_dec_ref(v_p_1972_);
                v___x_1977_ = leanh::lean_apply_1(v_filter_1976_, v_val_1975_);
                v___x_1978_ = (leanh::lean_unbox(v___x_1977_) as u8);
                return v___x_1978_;
            }
        }
        _ => {
            let mut v_p_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_p_1979_ = leanh::lean_ctor_get(v_self_1966_, 0);
            leanh::lean_inc_ref(v_p_1979_);
            leanh::lean_dec_ref_known(v_self_1966_, 1);
            v___x_1980_ = l_System_FilePath_fileName(v_path_1965_);
            if leanh::lean_obj_tag(v___x_1980_) == 0 {
                let mut v___x_1981_: u8 = 0;
                leanh::lean_dec_ref(v_p_1979_);
                v___x_1981_ = 0;
                return v___x_1981_;
            } else {
                let mut v_val_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_filter_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1985_: u8 = 0;
                v_val_1982_ = leanh::lean_ctor_get(v___x_1980_, 0);
                leanh::lean_inc(v_val_1982_);
                leanh::lean_dec_ref_known(v___x_1980_, 1);
                v_filter_1983_ = leanh::lean_ctor_get(v_p_1979_, 0);
                leanh::lean_inc_ref(v_filter_1983_);
                leanh::lean_dec_ref(v_p_1979_);
                v___x_1984_ = leanh::lean_apply_1(v_filter_1983_, v_val_1982_);
                v___x_1985_ = (leanh::lean_unbox(v___x_1984_) as u8);
                return v___x_1985_;
            }
        }
    }
}
pub unsafe fn l_Lake_PathPatDescr_matches___boxed(
    mut v_path_1986_: *mut leanh::LeanObject,
    mut v_self_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1988_: u8 = 0;
    let mut v_r_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1988_ = l_Lake_PathPatDescr_matches(v_path_1986_, v_self_1987_);
    v_r_1989_ = leanh::lean_box((v_res_1988_) as usize);
    return v_r_1989_;
}
pub unsafe fn l_Lake_PathPat_path___lam__0(
    mut v___x_1994_: *mut leanh::LeanObject,
    mut v___x_1995_: *mut leanh::LeanObject,
    mut v_x_1996_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1997_: u8 = 0;
    v___x_1997_ = l_Lake_PatternDescr_matches___redArg(v___x_1994_, v_x_1996_, v___x_1995_);
    return v___x_1997_;
}
pub unsafe fn l_Lake_PathPat_path___lam__0___boxed(
    mut v___x_1998_: *mut leanh::LeanObject,
    mut v___x_1999_: *mut leanh::LeanObject,
    mut v_x_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2001_: u8 = 0;
    let mut v_r_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Lake_PathPat_path___lam__0(v___x_1998_, v___x_1999_, v_x_2000_);
    v_r_2002_ = leanh::lean_box((v_res_2001_) as usize);
    return v_r_2002_;
}
pub unsafe fn l_Lake_PathPat_path(
    mut v_p_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2005_, 0, v_p_2003_);
    v___x_2006_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2006_, 0, v___x_2005_);
    leanh::lean_inc_ref(v___x_2006_);
    v___f_2007_ = leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2007_, 0, v___x_2004_);
    leanh::lean_closure_set(v___f_2007_, 1, v___x_2006_);
    v___x_2008_ = leanh::lean_box(0);
    v___x_2009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2009_, 0, v___x_2006_);
    v___x_2010_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2010_, 0, v___f_2007_);
    leanh::lean_ctor_set(v___x_2010_, 1, v___x_2008_);
    leanh::lean_ctor_set(v___x_2010_, 2, v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn l_Lake_PathPat_extension(
    mut v_p_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2013_, 0, v_p_2011_);
    v___x_2014_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2014_, 0, v___x_2013_);
    leanh::lean_inc_ref(v___x_2014_);
    v___f_2015_ = leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2015_, 0, v___x_2012_);
    leanh::lean_closure_set(v___f_2015_, 1, v___x_2014_);
    v___x_2016_ = leanh::lean_box(0);
    v___x_2017_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2017_, 0, v___x_2014_);
    v___x_2018_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2018_, 0, v___f_2015_);
    leanh::lean_ctor_set(v___x_2018_, 1, v___x_2016_);
    leanh::lean_ctor_set(v___x_2018_, 2, v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lake_PathPat_fileName(
    mut v_p_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2021_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2021_, 0, v_p_2019_);
    v___x_2022_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
    leanh::lean_inc_ref(v___x_2022_);
    v___f_2023_ = leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2023_, 0, v___x_2020_);
    leanh::lean_closure_set(v___f_2023_, 1, v___x_2022_);
    v___x_2024_ = leanh::lean_box(0);
    v___x_2025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2025_, 0, v___x_2022_);
    v___x_2026_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2026_, 0, v___f_2023_);
    leanh::lean_ctor_set(v___x_2026_, 1, v___x_2024_);
    leanh::lean_ctor_set(v___x_2026_, 2, v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_2027_: *mut leanh::LeanObject,
    mut v_x_2028_: *mut leanh::LeanObject,
    mut v_h__1_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = leanh::lean_apply_2(v_h__1_2029_, v_x_2027_, v_x_2028_);
    return v___x_2030_;
}
pub unsafe fn l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_2031_: *mut leanh::LeanObject,
    mut v_x_2032_: *mut leanh::LeanObject,
    mut v_x_2033_: *mut leanh::LeanObject,
    mut v_h__1_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = leanh::lean_apply_2(v_h__1_2034_, v_x_2032_, v_x_2033_);
    return v___x_2035_;
}
pub unsafe fn l_Lake_isVerLike(mut v_s_2036_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    v___x_2037_ = leanh::lean_unsigned_to_nat(2);
    v___x_2038_ = lean_string_utf8_byte_size(v_s_2036_);
    v___x_2039_ = lean_nat_dec_le(v___x_2037_, v___x_2038_);
    if v___x_2039_ == 0 {
        return v___x_2039_;
    } else {
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: u32 = 0;
        let mut v___x_2042_: u32 = 0;
        let mut v___x_2043_: u8 = 0;
        v___x_2040_ = leanh::lean_unsigned_to_nat(0);
        v___x_2041_ = lean_string_utf8_get_fast(v_s_2036_, v___x_2040_);
        v___x_2042_ = 118;
        v___x_2043_ = lean_uint32_dec_eq(v___x_2041_, v___x_2042_);
        if v___x_2043_ == 0 {
            return v___x_2043_;
        } else {
            let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2045_: u32 = 0;
            let mut v___x_2046_: u32 = 0;
            let mut v___x_2047_: u8 = 0;
            v___x_2044_ = leanh::lean_unsigned_to_nat(1);
            v___x_2045_ = lean_string_utf8_get_fast(v_s_2036_, v___x_2044_);
            v___x_2046_ = 48;
            v___x_2047_ = lean_uint32_dec_le(v___x_2046_, v___x_2045_);
            if v___x_2047_ == 0 {
                return v___x_2047_;
            } else {
                let mut v___x_2048_: u32 = 0;
                let mut v___x_2049_: u8 = 0;
                v___x_2048_ = 57;
                v___x_2049_ = lean_uint32_dec_le(v___x_2045_, v___x_2048_);
                return v___x_2049_;
            }
        }
    }
}
pub unsafe fn l_Lake_isVerLike___boxed(
    mut v_s_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2051_: u8 = 0;
    let mut v_r_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lake_isVerLike(v_s_2050_);
    leanh::lean_dec_ref(v_s_2050_);
    v_r_2052_ = leanh::lean_box((v_res_2051_) as usize);
    return v_r_2052_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(
    mut v_k_2070_: *mut leanh::LeanObject,
    mut v_v_2071_: *mut leanh::LeanObject,
    mut v_t_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v_impl_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v_size_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v_unused_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut v_unused_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_unused_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v_k_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_unused_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v_size_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_unused_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v_unused_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut v_unused_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v_k_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_unused_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_unused_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2341_: u8 = 0;
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_unused_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2072_) == 0 {
                    v_size_2073_ = leanh::lean_ctor_get(v_t_2072_, 0);
                    v_k_2074_ = leanh::lean_ctor_get(v_t_2072_, 1);
                    v_v_2075_ = leanh::lean_ctor_get(v_t_2072_, 2);
                    v_l_2076_ = leanh::lean_ctor_get(v_t_2072_, 3);
                    v_r_2077_ = leanh::lean_ctor_get(v_t_2072_, 4);
                    v_isSharedCheck_2357_ = (!leanh::lean_is_exclusive(v_t_2072_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2079_ = v_t_2072_;
                        v_isShared_2080_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2077_);
                        leanh::lean_inc(v_l_2076_);
                        leanh::lean_inc(v_v_2075_);
                        leanh::lean_inc(v_k_2074_);
                        leanh::lean_inc(v_size_2073_);
                        leanh::lean_dec(v_t_2072_);
                        v___x_2079_ = leanh::lean_box(0);
                        v_isShared_2080_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2358_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2359_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_2359_, 0, v___x_2358_);
                    leanh::lean_ctor_set(v___x_2359_, 1, v_k_2070_);
                    leanh::lean_ctor_set(v___x_2359_, 2, v_v_2071_);
                    leanh::lean_ctor_set(v___x_2359_, 3, v_t_2072_);
                    leanh::lean_ctor_set(v___x_2359_, 4, v_t_2072_);
                    return v___x_2359_;
                }
            }
            1 => {
                v___x_2081_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2070_, v_k_2074_);
                match v___x_2081_ {
                    0 => {
                        leanh::lean_dec(v_size_2073_);
                        v_impl_2082_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_2070_, v_v_2071_, v_l_2076_);
                        v___x_2083_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_2077_) == 0 {
                            v_size_2084_ = leanh::lean_ctor_get(v_r_2077_, 0);
                            v_size_2085_ = leanh::lean_ctor_get(v_impl_2082_, 0);
                            leanh::lean_inc(v_size_2085_);
                            v_k_2086_ = leanh::lean_ctor_get(v_impl_2082_, 1);
                            leanh::lean_inc(v_k_2086_);
                            v_v_2087_ = leanh::lean_ctor_get(v_impl_2082_, 2);
                            leanh::lean_inc(v_v_2087_);
                            v_l_2088_ = leanh::lean_ctor_get(v_impl_2082_, 3);
                            leanh::lean_inc(v_l_2088_);
                            v_r_2089_ = leanh::lean_ctor_get(v_impl_2082_, 4);
                            leanh::lean_inc(v_r_2089_);
                            v___x_2090_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2091_ = lean_nat_mul(v___x_2090_, v_size_2084_);
                            v___x_2092_ = lean_nat_dec_lt(v___x_2091_, v_size_2085_);
                            leanh::lean_dec(v___x_2091_);
                            if v___x_2092_ == 0 {
                                leanh::lean_dec(v_r_2089_);
                                leanh::lean_dec(v_l_2088_);
                                leanh::lean_dec(v_v_2087_);
                                leanh::lean_dec(v_k_2086_);
                                v___x_2093_ = lean_nat_add(v___x_2083_, v_size_2085_);
                                leanh::lean_dec(v_size_2085_);
                                v___x_2094_ = lean_nat_add(v___x_2093_, v_size_2084_);
                                leanh::lean_dec(v___x_2093_);
                                if v_isShared_2080_ == 0 {
                                    leanh::lean_ctor_set(v___x_2079_, 3, v_impl_2082_);
                                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2094_);
                                    v___x_2096_ = v___x_2079_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2097_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        0,
                                        v___x_2094_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        1,
                                        v_k_2074_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        2,
                                        v_v_2075_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        3,
                                        v_impl_2082_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        4,
                                        v_r_2077_,
                                    );
                                    v___x_2096_ = v_reuseFailAlloc_2097_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2163_ =
                                    (!leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                if v_isSharedCheck_2163_ == 0 {
                                    v_unused_2164_ = leanh::lean_ctor_get(v_impl_2082_, 4);
                                    leanh::lean_dec(v_unused_2164_);
                                    v_unused_2165_ = leanh::lean_ctor_get(v_impl_2082_, 3);
                                    leanh::lean_dec(v_unused_2165_);
                                    v_unused_2166_ = leanh::lean_ctor_get(v_impl_2082_, 2);
                                    leanh::lean_dec(v_unused_2166_);
                                    v_unused_2167_ = leanh::lean_ctor_get(v_impl_2082_, 1);
                                    leanh::lean_dec(v_unused_2167_);
                                    v_unused_2168_ = leanh::lean_ctor_get(v_impl_2082_, 0);
                                    leanh::lean_dec(v_unused_2168_);
                                    v___x_2099_ = v_impl_2082_;
                                    v_isShared_2100_ = v_isSharedCheck_2163_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2082_);
                                    v___x_2099_ = leanh::lean_box(0);
                                    v_isShared_2100_ = v_isSharedCheck_2163_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2169_ = leanh::lean_ctor_get(v_impl_2082_, 3);
                            leanh::lean_inc(v_l_2169_);
                            if leanh::lean_obj_tag(v_l_2169_) == 0 {
                                v_r_2170_ = leanh::lean_ctor_get(v_impl_2082_, 4);
                                v_k_2171_ = leanh::lean_ctor_get(v_impl_2082_, 1);
                                v_v_2172_ = leanh::lean_ctor_get(v_impl_2082_, 2);
                                v_isSharedCheck_2183_ =
                                    (!leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                if v_isSharedCheck_2183_ == 0 {
                                    v_unused_2184_ = leanh::lean_ctor_get(v_impl_2082_, 3);
                                    leanh::lean_dec(v_unused_2184_);
                                    v_unused_2185_ = leanh::lean_ctor_get(v_impl_2082_, 0);
                                    leanh::lean_dec(v_unused_2185_);
                                    v___x_2174_ = v_impl_2082_;
                                    v_isShared_2175_ = v_isSharedCheck_2183_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2170_);
                                    leanh::lean_inc(v_v_2172_);
                                    leanh::lean_inc(v_k_2171_);
                                    leanh::lean_dec(v_impl_2082_);
                                    v___x_2174_ = leanh::lean_box(0);
                                    v_isShared_2175_ = v_isSharedCheck_2183_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2186_ = leanh::lean_ctor_get(v_impl_2082_, 4);
                                leanh::lean_inc(v_r_2186_);
                                if leanh::lean_obj_tag(v_r_2186_) == 0 {
                                    v_k_2187_ = leanh::lean_ctor_get(v_impl_2082_, 1);
                                    v_v_2188_ = leanh::lean_ctor_get(v_impl_2082_, 2);
                                    v_isSharedCheck_2211_ =
                                        (!leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                    if v_isSharedCheck_2211_ == 0 {
                                        v_unused_2212_ =
                                            leanh::lean_ctor_get(v_impl_2082_, 4);
                                        leanh::lean_dec(v_unused_2212_);
                                        v_unused_2213_ =
                                            leanh::lean_ctor_get(v_impl_2082_, 3);
                                        leanh::lean_dec(v_unused_2213_);
                                        v_unused_2214_ =
                                            leanh::lean_ctor_get(v_impl_2082_, 0);
                                        leanh::lean_dec(v_unused_2214_);
                                        v___x_2190_ = v_impl_2082_;
                                        v_isShared_2191_ = v_isSharedCheck_2211_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2188_);
                                        leanh::lean_inc(v_k_2187_);
                                        leanh::lean_dec(v_impl_2082_);
                                        v___x_2190_ = leanh::lean_box(0);
                                        v_isShared_2191_ = v_isSharedCheck_2211_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2215_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2080_ == 0 {
                                        leanh::lean_ctor_set(v___x_2079_, 4, v_r_2186_);
                                        leanh::lean_ctor_set(v___x_2079_, 3, v_impl_2082_);
                                        leanh::lean_ctor_set(v___x_2079_, 0, v___x_2215_);
                                        v___x_2217_ = v___x_2079_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2218_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            0,
                                            v___x_2215_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            1,
                                            v_k_2074_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            2,
                                            v_v_2075_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            3,
                                            v_impl_2082_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            4,
                                            v_r_2186_,
                                        );
                                        v___x_2217_ = v_reuseFailAlloc_2218_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_2075_);
                        leanh::lean_dec(v_k_2074_);
                        if v_isShared_2080_ == 0 {
                            leanh::lean_ctor_set(v___x_2079_, 2, v_v_2071_);
                            leanh::lean_ctor_set(v___x_2079_, 1, v_k_2070_);
                            v___x_2220_ = v___x_2079_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2221_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_size_2073_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2070_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2071_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_l_2076_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_r_2077_);
                            v___x_2220_ = v_reuseFailAlloc_2221_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_2073_);
                        v_impl_2222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_2070_, v_v_2071_, v_r_2077_);
                        v___x_2223_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_2076_) == 0 {
                            v_size_2224_ = leanh::lean_ctor_get(v_l_2076_, 0);
                            v_size_2225_ = leanh::lean_ctor_get(v_impl_2222_, 0);
                            leanh::lean_inc(v_size_2225_);
                            v_k_2226_ = leanh::lean_ctor_get(v_impl_2222_, 1);
                            leanh::lean_inc(v_k_2226_);
                            v_v_2227_ = leanh::lean_ctor_get(v_impl_2222_, 2);
                            leanh::lean_inc(v_v_2227_);
                            v_l_2228_ = leanh::lean_ctor_get(v_impl_2222_, 3);
                            leanh::lean_inc(v_l_2228_);
                            v_r_2229_ = leanh::lean_ctor_get(v_impl_2222_, 4);
                            leanh::lean_inc(v_r_2229_);
                            v___x_2230_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2231_ = lean_nat_mul(v___x_2230_, v_size_2224_);
                            v___x_2232_ = lean_nat_dec_lt(v___x_2231_, v_size_2225_);
                            leanh::lean_dec(v___x_2231_);
                            if v___x_2232_ == 0 {
                                leanh::lean_dec(v_r_2229_);
                                leanh::lean_dec(v_l_2228_);
                                leanh::lean_dec(v_v_2227_);
                                leanh::lean_dec(v_k_2226_);
                                v___x_2233_ = lean_nat_add(v___x_2223_, v_size_2224_);
                                v___x_2234_ = lean_nat_add(v___x_2233_, v_size_2225_);
                                leanh::lean_dec(v_size_2225_);
                                leanh::lean_dec(v___x_2233_);
                                if v_isShared_2080_ == 0 {
                                    leanh::lean_ctor_set(v___x_2079_, 4, v_impl_2222_);
                                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2234_);
                                    v___x_2236_ = v___x_2079_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2237_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        0,
                                        v___x_2234_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        1,
                                        v_k_2074_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        2,
                                        v_v_2075_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        3,
                                        v_l_2076_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        4,
                                        v_impl_2222_,
                                    );
                                    v___x_2236_ = v_reuseFailAlloc_2237_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2301_ =
                                    (!leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                if v_isSharedCheck_2301_ == 0 {
                                    v_unused_2302_ = leanh::lean_ctor_get(v_impl_2222_, 4);
                                    leanh::lean_dec(v_unused_2302_);
                                    v_unused_2303_ = leanh::lean_ctor_get(v_impl_2222_, 3);
                                    leanh::lean_dec(v_unused_2303_);
                                    v_unused_2304_ = leanh::lean_ctor_get(v_impl_2222_, 2);
                                    leanh::lean_dec(v_unused_2304_);
                                    v_unused_2305_ = leanh::lean_ctor_get(v_impl_2222_, 1);
                                    leanh::lean_dec(v_unused_2305_);
                                    v_unused_2306_ = leanh::lean_ctor_get(v_impl_2222_, 0);
                                    leanh::lean_dec(v_unused_2306_);
                                    v___x_2239_ = v_impl_2222_;
                                    v_isShared_2240_ = v_isSharedCheck_2301_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2222_);
                                    v___x_2239_ = leanh::lean_box(0);
                                    v_isShared_2240_ = v_isSharedCheck_2301_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2307_ = leanh::lean_ctor_get(v_impl_2222_, 3);
                            leanh::lean_inc(v_l_2307_);
                            if leanh::lean_obj_tag(v_l_2307_) == 0 {
                                v_r_2308_ = leanh::lean_ctor_get(v_impl_2222_, 4);
                                v_k_2309_ = leanh::lean_ctor_get(v_impl_2222_, 1);
                                v_v_2310_ = leanh::lean_ctor_get(v_impl_2222_, 2);
                                v_isSharedCheck_2333_ =
                                    (!leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                if v_isSharedCheck_2333_ == 0 {
                                    v_unused_2334_ = leanh::lean_ctor_get(v_impl_2222_, 3);
                                    leanh::lean_dec(v_unused_2334_);
                                    v_unused_2335_ = leanh::lean_ctor_get(v_impl_2222_, 0);
                                    leanh::lean_dec(v_unused_2335_);
                                    v___x_2312_ = v_impl_2222_;
                                    v_isShared_2313_ = v_isSharedCheck_2333_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2308_);
                                    leanh::lean_inc(v_v_2310_);
                                    leanh::lean_inc(v_k_2309_);
                                    leanh::lean_dec(v_impl_2222_);
                                    v___x_2312_ = leanh::lean_box(0);
                                    v_isShared_2313_ = v_isSharedCheck_2333_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_2336_ = leanh::lean_ctor_get(v_impl_2222_, 4);
                                leanh::lean_inc(v_r_2336_);
                                if leanh::lean_obj_tag(v_r_2336_) == 0 {
                                    v_k_2337_ = leanh::lean_ctor_get(v_impl_2222_, 1);
                                    v_v_2338_ = leanh::lean_ctor_get(v_impl_2222_, 2);
                                    v_isSharedCheck_2349_ =
                                        (!leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                    if v_isSharedCheck_2349_ == 0 {
                                        v_unused_2350_ =
                                            leanh::lean_ctor_get(v_impl_2222_, 4);
                                        leanh::lean_dec(v_unused_2350_);
                                        v_unused_2351_ =
                                            leanh::lean_ctor_get(v_impl_2222_, 3);
                                        leanh::lean_dec(v_unused_2351_);
                                        v_unused_2352_ =
                                            leanh::lean_ctor_get(v_impl_2222_, 0);
                                        leanh::lean_dec(v_unused_2352_);
                                        v___x_2340_ = v_impl_2222_;
                                        v_isShared_2341_ = v_isSharedCheck_2349_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2338_);
                                        leanh::lean_inc(v_k_2337_);
                                        leanh::lean_dec(v_impl_2222_);
                                        v___x_2340_ = leanh::lean_box(0);
                                        v_isShared_2341_ = v_isSharedCheck_2349_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_2353_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2080_ == 0 {
                                        leanh::lean_ctor_set(v___x_2079_, 4, v_impl_2222_);
                                        leanh::lean_ctor_set(v___x_2079_, 3, v_r_2336_);
                                        leanh::lean_ctor_set(v___x_2079_, 0, v___x_2353_);
                                        v___x_2355_ = v___x_2079_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2356_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            0,
                                            v___x_2353_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            1,
                                            v_k_2074_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            2,
                                            v_v_2075_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            3,
                                            v_r_2336_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            4,
                                            v_impl_2222_,
                                        );
                                        v___x_2355_ = v_reuseFailAlloc_2356_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2096_;
            }
            3 => {
                v_size_2101_ = leanh::lean_ctor_get(v_l_2088_, 0);
                v_size_2102_ = leanh::lean_ctor_get(v_r_2089_, 0);
                v_k_2103_ = leanh::lean_ctor_get(v_r_2089_, 1);
                v_v_2104_ = leanh::lean_ctor_get(v_r_2089_, 2);
                v_l_2105_ = leanh::lean_ctor_get(v_r_2089_, 3);
                v_r_2106_ = leanh::lean_ctor_get(v_r_2089_, 4);
                v___x_2107_ = leanh::lean_unsigned_to_nat(2);
                v___x_2108_ = lean_nat_mul(v___x_2107_, v_size_2101_);
                v___x_2109_ = lean_nat_dec_lt(v_size_2102_, v___x_2108_);
                leanh::lean_dec(v___x_2108_);
                if v___x_2109_ == 0 {
                    leanh::lean_inc(v_r_2106_);
                    leanh::lean_inc(v_l_2105_);
                    leanh::lean_inc(v_v_2104_);
                    leanh::lean_inc(v_k_2103_);
                    v_isSharedCheck_2138_ = (!leanh::lean_is_exclusive(v_r_2089_)) as u8;
                    if v_isSharedCheck_2138_ == 0 {
                        v_unused_2139_ = leanh::lean_ctor_get(v_r_2089_, 4);
                        leanh::lean_dec(v_unused_2139_);
                        v_unused_2140_ = leanh::lean_ctor_get(v_r_2089_, 3);
                        leanh::lean_dec(v_unused_2140_);
                        v_unused_2141_ = leanh::lean_ctor_get(v_r_2089_, 2);
                        leanh::lean_dec(v_unused_2141_);
                        v_unused_2142_ = leanh::lean_ctor_get(v_r_2089_, 1);
                        leanh::lean_dec(v_unused_2142_);
                        v_unused_2143_ = leanh::lean_ctor_get(v_r_2089_, 0);
                        leanh::lean_dec(v_unused_2143_);
                        v___x_2111_ = v_r_2089_;
                        v_isShared_2112_ = v_isSharedCheck_2138_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2089_);
                        v___x_2111_ = leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2138_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2079_);
                    v___x_2144_ = lean_nat_add(v___x_2083_, v_size_2085_);
                    leanh::lean_dec(v_size_2085_);
                    v___x_2145_ = lean_nat_add(v___x_2144_, v_size_2084_);
                    leanh::lean_dec(v___x_2144_);
                    v___x_2146_ = lean_nat_add(v___x_2083_, v_size_2084_);
                    v___x_2147_ = lean_nat_add(v___x_2146_, v_size_2102_);
                    leanh::lean_dec(v___x_2146_);
                    leanh::lean_inc_ref(v_r_2077_);
                    if v_isShared_2100_ == 0 {
                        leanh::lean_ctor_set(v___x_2099_, 4, v_r_2077_);
                        leanh::lean_ctor_set(v___x_2099_, 3, v_r_2089_);
                        leanh::lean_ctor_set(v___x_2099_, 2, v_v_2075_);
                        leanh::lean_ctor_set(v___x_2099_, 1, v_k_2074_);
                        leanh::lean_ctor_set(v___x_2099_, 0, v___x_2147_);
                        v___x_2149_ = v___x_2099_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2162_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2147_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_k_2074_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_v_2075_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_r_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_r_2077_);
                        v___x_2149_ = v_reuseFailAlloc_2162_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2113_ = lean_nat_add(v___x_2083_, v_size_2085_);
                leanh::lean_dec(v_size_2085_);
                v___x_2114_ = lean_nat_add(v___x_2113_, v_size_2084_);
                leanh::lean_dec(v___x_2113_);
                v___x_2126_ = lean_nat_add(v___x_2083_, v_size_2101_);
                if leanh::lean_obj_tag(v_l_2105_) == 0 {
                    v_size_2136_ = leanh::lean_ctor_get(v_l_2105_, 0);
                    leanh::lean_inc(v_size_2136_);
                    v___y_2128_ = v_size_2136_;
                    state = 8;
                    continue;
                } else {
                    v___x_2137_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2128_ = v___x_2137_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2119_ = lean_nat_add(v___y_2116_, v___y_2118_);
                leanh::lean_dec(v___y_2118_);
                leanh::lean_dec(v___y_2116_);
                if v_isShared_2112_ == 0 {
                    leanh::lean_ctor_set(v___x_2111_, 4, v_r_2077_);
                    leanh::lean_ctor_set(v___x_2111_, 3, v_r_2106_);
                    leanh::lean_ctor_set(v___x_2111_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v___x_2111_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v___x_2111_, 0, v___x_2119_);
                    v___x_2121_ = v___x_2111_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_r_2106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_r_2077_);
                    v___x_2121_ = v_reuseFailAlloc_2125_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2100_ == 0 {
                    leanh::lean_ctor_set(v___x_2099_, 4, v___x_2121_);
                    leanh::lean_ctor_set(v___x_2099_, 3, v___y_2117_);
                    leanh::lean_ctor_set(v___x_2099_, 2, v_v_2104_);
                    leanh::lean_ctor_set(v___x_2099_, 1, v_k_2103_);
                    leanh::lean_ctor_set(v___x_2099_, 0, v___x_2114_);
                    v___x_2123_ = v___x_2099_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_2103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_2104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 3, v___y_2117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 4, v___x_2121_);
                    v___x_2123_ = v_reuseFailAlloc_2124_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2123_;
            }
            8 => {
                v___x_2129_ = lean_nat_add(v___x_2126_, v___y_2128_);
                leanh::lean_dec(v___y_2128_);
                leanh::lean_dec(v___x_2126_);
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v_l_2105_);
                    leanh::lean_ctor_set(v___x_2079_, 3, v_l_2088_);
                    leanh::lean_ctor_set(v___x_2079_, 2, v_v_2087_);
                    leanh::lean_ctor_set(v___x_2079_, 1, v_k_2086_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2079_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_l_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_l_2105_);
                    v___x_2131_ = v_reuseFailAlloc_2135_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2132_ = lean_nat_add(v___x_2083_, v_size_2084_);
                if leanh::lean_obj_tag(v_r_2106_) == 0 {
                    v_size_2133_ = leanh::lean_ctor_get(v_r_2106_, 0);
                    leanh::lean_inc(v_size_2133_);
                    v___y_2116_ = v___x_2132_;
                    v___y_2117_ = v___x_2131_;
                    v___y_2118_ = v_size_2133_;
                    state = 5;
                    continue;
                } else {
                    v___x_2134_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2116_ = v___x_2132_;
                    v___y_2117_ = v___x_2131_;
                    v___y_2118_ = v___x_2134_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2156_ = (!leanh::lean_is_exclusive(v_r_2077_)) as u8;
                if v_isSharedCheck_2156_ == 0 {
                    v_unused_2157_ = leanh::lean_ctor_get(v_r_2077_, 4);
                    leanh::lean_dec(v_unused_2157_);
                    v_unused_2158_ = leanh::lean_ctor_get(v_r_2077_, 3);
                    leanh::lean_dec(v_unused_2158_);
                    v_unused_2159_ = leanh::lean_ctor_get(v_r_2077_, 2);
                    leanh::lean_dec(v_unused_2159_);
                    v_unused_2160_ = leanh::lean_ctor_get(v_r_2077_, 1);
                    leanh::lean_dec(v_unused_2160_);
                    v_unused_2161_ = leanh::lean_ctor_get(v_r_2077_, 0);
                    leanh::lean_dec(v_unused_2161_);
                    v___x_2151_ = v_r_2077_;
                    v_isShared_2152_ = v_isSharedCheck_2156_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_2077_);
                    v___x_2151_ = leanh::lean_box(0);
                    v_isShared_2152_ = v_isSharedCheck_2156_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2152_ == 0 {
                    leanh::lean_ctor_set(v___x_2151_, 4, v___x_2149_);
                    leanh::lean_ctor_set(v___x_2151_, 3, v_l_2088_);
                    leanh::lean_ctor_set(v___x_2151_, 2, v_v_2087_);
                    leanh::lean_ctor_set(v___x_2151_, 1, v_k_2086_);
                    leanh::lean_ctor_set(v___x_2151_, 0, v___x_2145_);
                    v___x_2154_ = v___x_2151_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_l_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2154_;
            }
            13 => {
                v___x_2176_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_2170_);
                if v_isShared_2175_ == 0 {
                    leanh::lean_ctor_set(v___x_2174_, 3, v_r_2170_);
                    leanh::lean_ctor_set(v___x_2174_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v___x_2174_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v___x_2174_, 0, v___x_2083_);
                    v___x_2178_ = v___x_2174_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2182_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_r_2170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_r_2170_);
                    v___x_2178_ = v_reuseFailAlloc_2182_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v___x_2178_);
                    leanh::lean_ctor_set(v___x_2079_, 3, v_l_2169_);
                    leanh::lean_ctor_set(v___x_2079_, 2, v_v_2172_);
                    leanh::lean_ctor_set(v___x_2079_, 1, v_k_2171_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2176_);
                    v___x_2180_ = v___x_2079_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_l_2169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 4, v___x_2178_);
                    v___x_2180_ = v_reuseFailAlloc_2181_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2180_;
            }
            16 => {
                v_k_2192_ = leanh::lean_ctor_get(v_r_2186_, 1);
                v_v_2193_ = leanh::lean_ctor_get(v_r_2186_, 2);
                v_isSharedCheck_2207_ = (!leanh::lean_is_exclusive(v_r_2186_)) as u8;
                if v_isSharedCheck_2207_ == 0 {
                    v_unused_2208_ = leanh::lean_ctor_get(v_r_2186_, 4);
                    leanh::lean_dec(v_unused_2208_);
                    v_unused_2209_ = leanh::lean_ctor_get(v_r_2186_, 3);
                    leanh::lean_dec(v_unused_2209_);
                    v_unused_2210_ = leanh::lean_ctor_get(v_r_2186_, 0);
                    leanh::lean_dec(v_unused_2210_);
                    v___x_2195_ = v_r_2186_;
                    v_isShared_2196_ = v_isSharedCheck_2207_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2193_);
                    leanh::lean_inc(v_k_2192_);
                    leanh::lean_dec(v_r_2186_);
                    v___x_2195_ = leanh::lean_box(0);
                    v_isShared_2196_ = v_isSharedCheck_2207_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2197_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2196_ == 0 {
                    leanh::lean_ctor_set(v___x_2195_, 4, v_l_2169_);
                    leanh::lean_ctor_set(v___x_2195_, 3, v_l_2169_);
                    leanh::lean_ctor_set(v___x_2195_, 2, v_v_2188_);
                    leanh::lean_ctor_set(v___x_2195_, 1, v_k_2187_);
                    leanh::lean_ctor_set(v___x_2195_, 0, v___x_2083_);
                    v___x_2199_ = v___x_2195_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_l_2169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_l_2169_);
                    v___x_2199_ = v_reuseFailAlloc_2206_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2191_ == 0 {
                    leanh::lean_ctor_set(v___x_2190_, 4, v_l_2169_);
                    leanh::lean_ctor_set(v___x_2190_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v___x_2190_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v___x_2190_, 0, v___x_2083_);
                    v___x_2201_ = v___x_2190_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2205_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_l_2169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_l_2169_);
                    v___x_2201_ = v_reuseFailAlloc_2205_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v___x_2201_);
                    leanh::lean_ctor_set(v___x_2079_, 3, v___x_2199_);
                    leanh::lean_ctor_set(v___x_2079_, 2, v_v_2193_);
                    leanh::lean_ctor_set(v___x_2079_, 1, v_k_2192_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2197_);
                    v___x_2203_ = v___x_2079_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_k_2192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_v_2193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 3, v___x_2199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 4, v___x_2201_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2203_;
            }
            21 => {
                return v___x_2217_;
            }
            22 => {
                return v___x_2220_;
            }
            23 => {
                return v___x_2236_;
            }
            24 => {
                v_size_2241_ = leanh::lean_ctor_get(v_l_2228_, 0);
                v_k_2242_ = leanh::lean_ctor_get(v_l_2228_, 1);
                v_v_2243_ = leanh::lean_ctor_get(v_l_2228_, 2);
                v_l_2244_ = leanh::lean_ctor_get(v_l_2228_, 3);
                v_r_2245_ = leanh::lean_ctor_get(v_l_2228_, 4);
                v_size_2246_ = leanh::lean_ctor_get(v_r_2229_, 0);
                v___x_2247_ = leanh::lean_unsigned_to_nat(2);
                v___x_2248_ = lean_nat_mul(v___x_2247_, v_size_2246_);
                v___x_2249_ = lean_nat_dec_lt(v_size_2241_, v___x_2248_);
                leanh::lean_dec(v___x_2248_);
                if v___x_2249_ == 0 {
                    leanh::lean_inc(v_r_2245_);
                    leanh::lean_inc(v_l_2244_);
                    leanh::lean_inc(v_v_2243_);
                    leanh::lean_inc(v_k_2242_);
                    v_isSharedCheck_2277_ = (!leanh::lean_is_exclusive(v_l_2228_)) as u8;
                    if v_isSharedCheck_2277_ == 0 {
                        v_unused_2278_ = leanh::lean_ctor_get(v_l_2228_, 4);
                        leanh::lean_dec(v_unused_2278_);
                        v_unused_2279_ = leanh::lean_ctor_get(v_l_2228_, 3);
                        leanh::lean_dec(v_unused_2279_);
                        v_unused_2280_ = leanh::lean_ctor_get(v_l_2228_, 2);
                        leanh::lean_dec(v_unused_2280_);
                        v_unused_2281_ = leanh::lean_ctor_get(v_l_2228_, 1);
                        leanh::lean_dec(v_unused_2281_);
                        v_unused_2282_ = leanh::lean_ctor_get(v_l_2228_, 0);
                        leanh::lean_dec(v_unused_2282_);
                        v___x_2251_ = v_l_2228_;
                        v_isShared_2252_ = v_isSharedCheck_2277_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2228_);
                        v___x_2251_ = leanh::lean_box(0);
                        v_isShared_2252_ = v_isSharedCheck_2277_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2079_);
                    v___x_2283_ = lean_nat_add(v___x_2223_, v_size_2224_);
                    v___x_2284_ = lean_nat_add(v___x_2283_, v_size_2225_);
                    leanh::lean_dec(v_size_2225_);
                    v___x_2285_ = lean_nat_add(v___x_2283_, v_size_2241_);
                    leanh::lean_dec(v___x_2283_);
                    leanh::lean_inc_ref(v_l_2076_);
                    if v_isShared_2240_ == 0 {
                        leanh::lean_ctor_set(v___x_2239_, 4, v_l_2228_);
                        leanh::lean_ctor_set(v___x_2239_, 3, v_l_2076_);
                        leanh::lean_ctor_set(v___x_2239_, 2, v_v_2075_);
                        leanh::lean_ctor_set(v___x_2239_, 1, v_k_2074_);
                        leanh::lean_ctor_set(v___x_2239_, 0, v___x_2285_);
                        v___x_2287_ = v___x_2239_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2300_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2285_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2074_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2075_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_2076_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_l_2228_);
                        v___x_2287_ = v_reuseFailAlloc_2300_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2253_ = lean_nat_add(v___x_2223_, v_size_2224_);
                v___x_2254_ = lean_nat_add(v___x_2253_, v_size_2225_);
                leanh::lean_dec(v_size_2225_);
                if leanh::lean_obj_tag(v_l_2244_) == 0 {
                    v_size_2275_ = leanh::lean_ctor_get(v_l_2244_, 0);
                    leanh::lean_inc(v_size_2275_);
                    v___y_2267_ = v_size_2275_;
                    state = 29;
                    continue;
                } else {
                    v___x_2276_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2267_ = v___x_2276_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2259_ = lean_nat_add(v___y_2257_, v___y_2258_);
                leanh::lean_dec(v___y_2258_);
                leanh::lean_dec(v___y_2257_);
                if v_isShared_2252_ == 0 {
                    leanh::lean_ctor_set(v___x_2251_, 4, v_r_2229_);
                    leanh::lean_ctor_set(v___x_2251_, 3, v_r_2245_);
                    leanh::lean_ctor_set(v___x_2251_, 2, v_v_2227_);
                    leanh::lean_ctor_set(v___x_2251_, 1, v_k_2226_);
                    leanh::lean_ctor_set(v___x_2251_, 0, v___x_2259_);
                    v___x_2261_ = v___x_2251_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_r_2245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_r_2229_);
                    v___x_2261_ = v_reuseFailAlloc_2265_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2240_ == 0 {
                    leanh::lean_ctor_set(v___x_2239_, 4, v___x_2261_);
                    leanh::lean_ctor_set(v___x_2239_, 3, v___y_2256_);
                    leanh::lean_ctor_set(v___x_2239_, 2, v_v_2243_);
                    leanh::lean_ctor_set(v___x_2239_, 1, v_k_2242_);
                    leanh::lean_ctor_set(v___x_2239_, 0, v___x_2254_);
                    v___x_2263_ = v___x_2239_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_k_2242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_v_2243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 3, v___y_2256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 4, v___x_2261_);
                    v___x_2263_ = v_reuseFailAlloc_2264_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2263_;
            }
            29 => {
                v___x_2268_ = lean_nat_add(v___x_2253_, v___y_2267_);
                leanh::lean_dec(v___y_2267_);
                leanh::lean_dec(v___x_2253_);
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v_l_2244_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2268_);
                    v___x_2270_ = v___x_2079_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_l_2076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_l_2244_);
                    v___x_2270_ = v_reuseFailAlloc_2274_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2271_ = lean_nat_add(v___x_2223_, v_size_2246_);
                if leanh::lean_obj_tag(v_r_2245_) == 0 {
                    v_size_2272_ = leanh::lean_ctor_get(v_r_2245_, 0);
                    leanh::lean_inc(v_size_2272_);
                    v___y_2256_ = v___x_2270_;
                    v___y_2257_ = v___x_2271_;
                    v___y_2258_ = v_size_2272_;
                    state = 26;
                    continue;
                } else {
                    v___x_2273_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2256_ = v___x_2270_;
                    v___y_2257_ = v___x_2271_;
                    v___y_2258_ = v___x_2273_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2294_ = (!leanh::lean_is_exclusive(v_l_2076_)) as u8;
                if v_isSharedCheck_2294_ == 0 {
                    v_unused_2295_ = leanh::lean_ctor_get(v_l_2076_, 4);
                    leanh::lean_dec(v_unused_2295_);
                    v_unused_2296_ = leanh::lean_ctor_get(v_l_2076_, 3);
                    leanh::lean_dec(v_unused_2296_);
                    v_unused_2297_ = leanh::lean_ctor_get(v_l_2076_, 2);
                    leanh::lean_dec(v_unused_2297_);
                    v_unused_2298_ = leanh::lean_ctor_get(v_l_2076_, 1);
                    leanh::lean_dec(v_unused_2298_);
                    v_unused_2299_ = leanh::lean_ctor_get(v_l_2076_, 0);
                    leanh::lean_dec(v_unused_2299_);
                    v___x_2289_ = v_l_2076_;
                    v_isShared_2290_ = v_isSharedCheck_2294_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_2076_);
                    v___x_2289_ = leanh::lean_box(0);
                    v_isShared_2290_ = v_isSharedCheck_2294_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2290_ == 0 {
                    leanh::lean_ctor_set(v___x_2289_, 4, v_r_2229_);
                    leanh::lean_ctor_set(v___x_2289_, 3, v___x_2287_);
                    leanh::lean_ctor_set(v___x_2289_, 2, v_v_2227_);
                    leanh::lean_ctor_set(v___x_2289_, 1, v_k_2226_);
                    leanh::lean_ctor_set(v___x_2289_, 0, v___x_2284_);
                    v___x_2292_ = v___x_2289_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_2226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_2227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 3, v___x_2287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_r_2229_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2292_;
            }
            34 => {
                v_k_2314_ = leanh::lean_ctor_get(v_l_2307_, 1);
                v_v_2315_ = leanh::lean_ctor_get(v_l_2307_, 2);
                v_isSharedCheck_2329_ = (!leanh::lean_is_exclusive(v_l_2307_)) as u8;
                if v_isSharedCheck_2329_ == 0 {
                    v_unused_2330_ = leanh::lean_ctor_get(v_l_2307_, 4);
                    leanh::lean_dec(v_unused_2330_);
                    v_unused_2331_ = leanh::lean_ctor_get(v_l_2307_, 3);
                    leanh::lean_dec(v_unused_2331_);
                    v_unused_2332_ = leanh::lean_ctor_get(v_l_2307_, 0);
                    leanh::lean_dec(v_unused_2332_);
                    v___x_2317_ = v_l_2307_;
                    v_isShared_2318_ = v_isSharedCheck_2329_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2315_);
                    leanh::lean_inc(v_k_2314_);
                    leanh::lean_dec(v_l_2307_);
                    v___x_2317_ = leanh::lean_box(0);
                    v_isShared_2318_ = v_isSharedCheck_2329_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2319_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_2308_, 2);
                if v_isShared_2318_ == 0 {
                    leanh::lean_ctor_set(v___x_2317_, 4, v_r_2308_);
                    leanh::lean_ctor_set(v___x_2317_, 3, v_r_2308_);
                    leanh::lean_ctor_set(v___x_2317_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v___x_2317_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v___x_2317_, 0, v___x_2223_);
                    v___x_2321_ = v___x_2317_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_r_2308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_r_2308_);
                    v___x_2321_ = v_reuseFailAlloc_2328_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_2308_);
                if v_isShared_2313_ == 0 {
                    leanh::lean_ctor_set(v___x_2312_, 3, v_r_2308_);
                    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2223_);
                    v___x_2323_ = v___x_2312_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2309_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_r_2308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_r_2308_);
                    v___x_2323_ = v_reuseFailAlloc_2327_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v___x_2323_);
                    leanh::lean_ctor_set(v___x_2079_, 3, v___x_2321_);
                    leanh::lean_ctor_set(v___x_2079_, 2, v_v_2315_);
                    leanh::lean_ctor_set(v___x_2079_, 1, v_k_2314_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2319_);
                    v___x_2325_ = v___x_2079_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_k_2314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_v_2315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 3, v___x_2321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 4, v___x_2323_);
                    v___x_2325_ = v_reuseFailAlloc_2326_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2325_;
            }
            39 => {
                v___x_2342_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2341_ == 0 {
                    leanh::lean_ctor_set(v___x_2340_, 4, v_l_2307_);
                    leanh::lean_ctor_set(v___x_2340_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v___x_2340_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v___x_2340_, 0, v___x_2223_);
                    v___x_2344_ = v___x_2340_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_l_2307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_l_2307_);
                    v___x_2344_ = v_reuseFailAlloc_2348_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2080_ == 0 {
                    leanh::lean_ctor_set(v___x_2079_, 4, v_r_2336_);
                    leanh::lean_ctor_set(v___x_2079_, 3, v___x_2344_);
                    leanh::lean_ctor_set(v___x_2079_, 2, v_v_2338_);
                    leanh::lean_ctor_set(v___x_2079_, 1, v_k_2337_);
                    leanh::lean_ctor_set(v___x_2079_, 0, v___x_2342_);
                    v___x_2346_ = v___x_2079_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 3, v___x_2344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2336_);
                    v___x_2346_ = v_reuseFailAlloc_2347_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2346_;
            }
            42 => {
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_versionTagPresets___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = leanh::lean_box(1);
    v___x_2361_ = l_Lake_StrPat_verLike;
    v___x_2362_ = l_Lake_StrPat_verLike___closed__2;
    v___x_2363_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v___x_2362_,
        v___x_2361_,
        v___x_2360_,
    );
    return v___x_2363_;
}
pub unsafe fn _init_l_Lake_versionTagPresets___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__0),
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__0_once),
        _init_l_Lake_versionTagPresets___closed__0,
    );
    v___x_2365_ = l_Lake_defaultVersionTags;
    v___x_2366_ = l_Lake_defaultVersionTags___closed__1;
    v___x_2367_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(
            v___x_2366_,
            v___x_2365_,
            v___x_2364_,
        );
    return v___x_2367_;
}
pub unsafe fn _init_l_Lake_versionTagPresets() -> *mut leanh::LeanObject {
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__1),
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__1_once),
        _init_l_Lake_versionTagPresets___closed__1,
    );
    return v___x_2368_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(
    mut v_00_u03b2_2369_: *mut leanh::LeanObject,
    mut v_k_2370_: *mut leanh::LeanObject,
    mut v_v_2371_: *mut leanh::LeanObject,
    mut v_t_2372_: *mut leanh::LeanObject,
    mut v_hl_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(
            v_k_2370_, v_v_2371_, v_t_2372_,
        );
    return v___x_2374_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Pattern(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_instInhabitedPathPatDescr_default = _init_l_Lake_instInhabitedPathPatDescr_default();
    leanh::lean_mark_persistent(l_Lake_instInhabitedPathPatDescr_default);
    l_Lake_instInhabitedPathPatDescr = _init_l_Lake_instInhabitedPathPatDescr();
    leanh::lean_mark_persistent(l_Lake_instInhabitedPathPatDescr);
    l_Lake_versionTagPresets = _init_l_Lake_versionTagPresets();
    leanh::lean_mark_persistent(l_Lake_versionTagPresets);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Pattern(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Pattern(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Pattern(builtin);
}
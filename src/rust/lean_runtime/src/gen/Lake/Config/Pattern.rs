// Lean compiler output
// Module: Lake.Config.Pattern
// Imports: Init.System.FilePath Std.Data.TreeMap.Basic Lean.Data.Name Lake.Util.Name Init.Data.String.TakeDrop Init.Data.String.Basic Init.Data.Option.Coe Init.Omega
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_get_fast;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
pub static l_Lake_term___x3d_x7e___00__closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_term___x3d_x7e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 101, 114, 109, 95, 61, 126, 95, 0],
    };
static mut l_Lake_term___x3d_x7e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_term___x3d_x7e___00__closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_term___x3d_x7e___00__closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            7154965323529718077 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_term___x3d_x7e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 126, 32, 0],
    };
static mut l_Lake_term___x3d_x7e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_term___x3d_x7e___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_term___x3d_x7e___00__closed__11_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_term___x3d_x7e___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_term___x3d_x7e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [73, 115, 80, 97, 116, 116, 101, 114, 110, 46, 115, 97, 116, 105, 115, 102, 105, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 115, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 97, 116, 105, 115, 102, 105, 101, 115, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut crate::leanh::LeanObject,9728926758818137547 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut crate::leanh::LeanObject,17326574432564351101 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_term___x3d_x7e___00__closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value) as *mut crate::leanh::LeanObject,13480139565922167655 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value) as *mut crate::leanh::LeanObject,9215142959186488649 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPattern_default__1___closed__0_value:
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
    m_fun: l_Lake_instInhabitedPattern_default__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedPattern_default__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPattern_default__1___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedPattern_default__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPattern_default__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPattern___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPatternDescr_default__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedPatternDescr_default__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPatternDescr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPatternDescr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instCoePatternDescr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoePatternDescr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoePatternDescr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoePatternDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instIsPatternPattern___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instIsPatternPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instIsPatternPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__2_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__3_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__4_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__5_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__6_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lake_PatternDescr_matches___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_matches___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_matches___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_matches___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeForallBoolPattern___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeForallBoolPattern___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeForallBoolPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeForallBoolPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_PatternDescr_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PatternDescr_empty___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Pattern_empty___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [101, 109, 112, 116, 121, 0],
    };
static mut l_Lake_Pattern_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Pattern_empty___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Pattern_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7601931857476342375 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Pattern_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_empty___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Pattern_empty___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_empty___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_empty___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_empty___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instEmptyCollectionPattern___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instEmptyCollectionPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_PatternDescr_star___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PatternDescr_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PatternDescr_star___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PatternDescr_star___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Pattern_star___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Pattern_star___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 116, 97, 114, 0],
    };
static mut l_Lake_Pattern_star___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Pattern_star___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Pattern_star___closed__1_value)
                as *mut crate::leanh::LeanObject,
            3121916218220129135 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Pattern_star___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Pattern_star___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Pattern_star___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_star___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Pattern_star___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Pattern_star___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedStrPatDescr_default___closed__0_value:
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
static mut l_Lake_instInhabitedStrPatDescr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedStrPatDescr_default___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedStrPatDescr_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedStrPatDescr_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedStrPatDescr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStrPatDescr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instIsPatternStrPatDescrString___closed__0_value:
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
    m_fun: l_Lake_StrPatDescr_matches___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instIsPatternStrPatDescrString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instIsPatternStrPatDescrString___closed__1_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_flip as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instIsPatternStrPatDescrString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instIsPatternStrPatDescrString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternStrPatDescrString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeArrayStringStrPatDescr___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instCoeArrayStringStrPatDescr___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instCoeArrayStringStrPatDescr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPatDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeArrayStringStrPatDescr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPatDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeArrayStringStrPat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPat_mem as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeArrayStringStrPat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeArrayStringStrPat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeArrayStringStrPat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_beq___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [98, 101, 113, 0],
    };
static mut l_Lake_StrPat_beq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_beq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_beq___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_StrPat_beq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5562882229368833754 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_beq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_beq___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeStringStrPatDescr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPatDescr_beq as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStringStrPatDescr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPatDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeStringStrPatDescr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPatDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeStringStrPat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_StrPat_beq as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStringStrPat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeStringStrPat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStringStrPat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPathPatDescr_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPathPatDescr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPathPatDescr_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPathPatDescr_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPathPatDescr_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPathPatDescr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value:
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
    m_fun: l_Lake_PathPatDescr_matches___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instIsPatternPathPatDescrFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_flip as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instIsPatternPathPatDescrFilePath___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instIsPatternPathPatDescrFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_isVerLike___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_StrPat_verLike___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [118, 101, 114, 76, 105, 107, 101, 0],
    };
static mut l_Lake_StrPat_verLike___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5548260973545959018 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_verLike___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_StrPat_verLike___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_StrPat_verLike___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_StrPat_verLike: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lake_defaultVersionTags___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9666231177748665885 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_defaultVersionTags___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_defaultVersionTags___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_StrPat_verLike___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_defaultVersionTags___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_defaultVersionTags: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultVersionTags___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_versionTagPresets___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionTagPresets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionTagPresets___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionTagPresets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_versionTagPresets: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5;
    v___x_1226_ = l_String_toRawSubstring_x27(v___x_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    v___x_1248_ = l_Lake_term___x3d_x7e___00__closed__2;
    crate::leanh::lean_inc(v_x_1245_);
    v___x_1249_ = l_Lean_Syntax_isOfKind(v_x_1245_, v___x_1248_);
    if v___x_1249_ == 0 {
        let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1245_);
        v___x_1250_ = crate::leanh::lean_box(1);
        v___x_1251_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
        crate::leanh::lean_ctor_set(v___x_1251_, 1, v_a_1247_);
        return v___x_1251_;
    } else {
        let mut v_quotContext_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: u8 = 0;
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1252_ = crate::leanh::lean_ctor_get(v_a_1246_, 1);
        v_currMacroScope_1253_ = crate::leanh::lean_ctor_get(v_a_1246_, 2);
        v_ref_1254_ = crate::leanh::lean_ctor_get(v_a_1246_, 5);
        v___x_1255_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1256_ = l_Lean_Syntax_getArg(v_x_1245_, v___x_1255_);
        v___x_1257_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1258_ = l_Lean_Syntax_getArg(v_x_1245_, v___x_1257_);
        crate::leanh::lean_dec(v_x_1245_);
        v___x_1259_ = 0;
        v___x_1260_ = l_Lean_SourceInfo_fromRef(v_ref_1254_, v___x_1259_);
        v___x_1261_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4;
        v___x_1262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once), _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6);
        v___x_1263_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9;
        crate::leanh::lean_inc(v_currMacroScope_1253_);
        crate::leanh::lean_inc(v_quotContext_1252_);
        v___x_1264_ =
            l_Lean_addMacroScope(v_quotContext_1252_, v___x_1263_, v_currMacroScope_1253_);
        v___x_1265_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12;
        crate::leanh::lean_inc_n(v___x_1260_, 2);
        v___x_1266_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1266_, 0, v___x_1260_);
        crate::leanh::lean_ctor_set(v___x_1266_, 1, v___x_1262_);
        crate::leanh::lean_ctor_set(v___x_1266_, 2, v___x_1264_);
        crate::leanh::lean_ctor_set(v___x_1266_, 3, v___x_1265_);
        v___x_1267_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14;
        v___x_1268_ = l_Lean_Syntax_node2(v___x_1260_, v___x_1267_, v___x_1256_, v___x_1258_);
        v___x_1269_ = l_Lean_Syntax_node2(v___x_1260_, v___x_1261_, v___x_1266_, v___x_1268_);
        v___x_1270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
        crate::leanh::lean_ctor_set(v___x_1270_, 1, v_a_1247_);
        return v___x_1270_;
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___boxed(
    mut v_x_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(
        v_x_1271_, v_a_1272_, v_a_1273_,
    );
    crate::leanh::lean_dec_ref(v_a_1272_);
    return v_res_1274_;
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(
    mut v_x_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    v___x_1281_ =
        l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4;
    crate::leanh::lean_inc(v_x_1278_);
    v___x_1282_ = l_Lean_Syntax_isOfKind(v_x_1278_, v___x_1281_);
    if v___x_1282_ == 0 {
        let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1278_);
        v___x_1283_ = crate::leanh::lean_box(0);
        v___x_1284_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
        crate::leanh::lean_ctor_set(v___x_1284_, 1, v_a_1280_);
        return v___x_1284_;
    } else {
        let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: u8 = 0;
        v___x_1285_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1286_ = l_Lean_Syntax_getArg(v_x_1278_, v___x_1285_);
        v___x_1287_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1;
        crate::leanh::lean_inc(v___x_1286_);
        v___x_1288_ = l_Lean_Syntax_isOfKind(v___x_1286_, v___x_1287_);
        if v___x_1288_ == 0 {
            let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1286_);
            crate::leanh::lean_dec(v_x_1278_);
            v___x_1289_ = crate::leanh::lean_box(0);
            v___x_1290_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
            crate::leanh::lean_ctor_set(v___x_1290_, 1, v_a_1280_);
            return v___x_1290_;
        } else {
            let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1294_: u8 = 0;
            v___x_1291_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1292_ = l_Lean_Syntax_getArg(v_x_1278_, v___x_1291_);
            crate::leanh::lean_dec(v_x_1278_);
            v___x_1293_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1292_);
            v___x_1294_ = l_Lean_Syntax_matchesNull(v___x_1292_, v___x_1293_);
            if v___x_1294_ == 0 {
                let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1292_);
                crate::leanh::lean_dec(v___x_1286_);
                v___x_1295_ = crate::leanh::lean_box(0);
                v___x_1296_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1295_);
                crate::leanh::lean_ctor_set(v___x_1296_, 1, v_a_1280_);
                return v___x_1296_;
            } else {
                let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1300_: u8 = 0;
                let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1297_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1285_);
                v___x_1298_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1291_);
                crate::leanh::lean_dec(v___x_1292_);
                v_ref_1299_ = l_Lean_replaceRef(v___x_1286_, v_a_1279_);
                crate::leanh::lean_dec(v___x_1286_);
                v___x_1300_ = 0;
                v___x_1301_ = l_Lean_SourceInfo_fromRef(v_ref_1299_, v___x_1300_);
                crate::leanh::lean_dec(v_ref_1299_);
                v___x_1302_ = l_Lake_term___x3d_x7e___00__closed__2;
                v___x_1303_ = l_Lake_term___x3d_x7e___00__closed__5;
                crate::leanh::lean_inc(v___x_1301_);
                v___x_1304_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1301_);
                crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                v___x_1305_ = l_Lean_Syntax_node3(
                    v___x_1301_,
                    v___x_1302_,
                    v___x_1297_,
                    v___x_1304_,
                    v___x_1298_,
                );
                v___x_1306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                crate::leanh::lean_ctor_set(v___x_1306_, 1, v_a_1280_);
                return v___x_1306_;
            }
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___boxed(
    mut v_x_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(
        v_x_1307_, v_a_1308_, v_a_1309_,
    );
    crate::leanh::lean_dec(v_a_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___redArg(
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1311_) {
        0 => {
            let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1312_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1312_;
        }
        1 => {
            let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1313_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1313_;
        }
        2 => {
            let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1314_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1314_;
        }
        _ => {
            let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1315_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1315_;
        }
    }
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___redArg___boxed(
    mut v_x_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_1316_);
    crate::leanh::lean_dec_ref(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx(
    mut v_00_u03b1_1318_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_Lake_PatternDescr_ctorIdx___boxed(
    mut v_00_u03b1_1322_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1323_: *mut crate::leanh::LeanObject,
    mut v_x_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lake_PatternDescr_ctorIdx(v_00_u03b1_1322_, v_00_u03b2_1323_, v_x_1324_);
    crate::leanh::lean_dec_ref(v_x_1324_);
    return v_res_1325_;
}
pub unsafe fn l_Lake_PatternDescr_ctorElim___redArg(
    mut v_t_1326_: *mut crate::leanh::LeanObject,
    mut v_k_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1326_) == 3 {
        let mut v_p_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_1328_ = crate::leanh::lean_ctor_get(v_t_1326_, 0);
        crate::leanh::lean_inc(v_p_1328_);
        crate::leanh::lean_dec_ref_known(v_t_1326_, 1);
        v___x_1329_ = crate::leanh::lean_apply_1(v_k_1327_, v_p_1328_);
        return v___x_1329_;
    } else {
        let mut v_p_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_1330_ = crate::leanh::lean_ctor_get(v_t_1326_, 0);
        crate::leanh::lean_inc_ref(v_p_1330_);
        crate::leanh::lean_dec_ref(v_t_1326_);
        v___x_1331_ = crate::leanh::lean_apply_1(v_k_1327_, v_p_1330_);
        return v___x_1331_;
    }
}
pub unsafe fn l_Lake_PatternDescr_ctorElim(
    mut v_00_u03b1_1332_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1333_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1334_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1335_: *mut crate::leanh::LeanObject,
    mut v_t_1336_: *mut crate::leanh::LeanObject,
    mut v_h_1337_: *mut crate::leanh::LeanObject,
    mut v_k_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1336_, v_k_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Lake_PatternDescr_ctorElim___boxed(
    mut v_00_u03b1_1340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1341_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1342_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1343_: *mut crate::leanh::LeanObject,
    mut v_t_1344_: *mut crate::leanh::LeanObject,
    mut v_h_1345_: *mut crate::leanh::LeanObject,
    mut v_k_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l_Lake_PatternDescr_ctorElim(
        v_00_u03b1_1340_,
        v_00_u03b2_1341_,
        v_motive__2_1342_,
        v_ctorIdx_1343_,
        v_t_1344_,
        v_h_1345_,
        v_k_1346_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1343_);
    return v_res_1347_;
}
pub unsafe fn l_Lake_PatternDescr_not_elim___redArg(
    mut v_t_1348_: *mut crate::leanh::LeanObject,
    mut v_not_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1348_, v_not_1349_);
    return v___x_1350_;
}
pub unsafe fn l_Lake_PatternDescr_not_elim(
    mut v_00_u03b1_1351_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1352_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1353_: *mut crate::leanh::LeanObject,
    mut v_t_1354_: *mut crate::leanh::LeanObject,
    mut v_h_1355_: *mut crate::leanh::LeanObject,
    mut v_not_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1354_, v_not_1356_);
    return v___x_1357_;
}
pub unsafe fn l_Lake_PatternDescr_all_elim___redArg(
    mut v_t_1358_: *mut crate::leanh::LeanObject,
    mut v_all_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1358_, v_all_1359_);
    return v___x_1360_;
}
pub unsafe fn l_Lake_PatternDescr_all_elim(
    mut v_00_u03b1_1361_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1362_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1363_: *mut crate::leanh::LeanObject,
    mut v_t_1364_: *mut crate::leanh::LeanObject,
    mut v_h_1365_: *mut crate::leanh::LeanObject,
    mut v_all_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1364_, v_all_1366_);
    return v___x_1367_;
}
pub unsafe fn l_Lake_PatternDescr_any_elim___redArg(
    mut v_t_1368_: *mut crate::leanh::LeanObject,
    mut v_any_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1368_, v_any_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Lake_PatternDescr_any_elim(
    mut v_00_u03b1_1371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1373_: *mut crate::leanh::LeanObject,
    mut v_t_1374_: *mut crate::leanh::LeanObject,
    mut v_h_1375_: *mut crate::leanh::LeanObject,
    mut v_any_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1374_, v_any_1376_);
    return v___x_1377_;
}
pub unsafe fn l_Lake_PatternDescr_coe_elim___redArg(
    mut v_t_1378_: *mut crate::leanh::LeanObject,
    mut v_coe_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1378_, v_coe_1379_);
    return v___x_1380_;
}
pub unsafe fn l_Lake_PatternDescr_coe_elim(
    mut v_00_u03b1_1381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1382_: *mut crate::leanh::LeanObject,
    mut v_motive__2_1383_: *mut crate::leanh::LeanObject,
    mut v_t_1384_: *mut crate::leanh::LeanObject,
    mut v_h_1385_: *mut crate::leanh::LeanObject,
    mut v_coe_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_1384_, v_coe_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1___lam__0(
    mut v_x_1388_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1389_: u8 = 0;
    v___x_1389_ = 0;
    return v___x_1389_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1___lam__0___boxed(
    mut v_x_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: u8 = 0;
    let mut v_r_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Lake_instInhabitedPattern_default__1___lam__0(v_x_1390_);
    crate::leanh::lean_dec(v_x_1390_);
    v_r_1392_ = crate::leanh::lean_box((v_res_1391_) as usize);
    return v_r_1392_;
}
pub unsafe fn l_Lake_instInhabitedPattern_default__1(
    mut v_00_u03b1_1398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l_Lake_instInhabitedPattern_default__1___closed__1;
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_instInhabitedPattern___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lake_instInhabitedPattern_default__1(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1401_;
}
pub unsafe fn l_Lake_instInhabitedPattern(
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0_once),
        _init_l_Lake_instInhabitedPattern___closed__0,
    );
    return v___x_1404_;
}
pub unsafe fn _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPattern___closed__0_once),
        _init_l_Lake_instInhabitedPattern___closed__0,
    );
    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Lake_instInhabitedPatternDescr_default__1(
    mut v_00_u03b1_1407_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr_default__1___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr_default__1___closed__0_once),
        _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0,
    );
    return v___x_1409_;
}
pub unsafe fn _init_l_Lake_instInhabitedPatternDescr___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lake_instInhabitedPatternDescr_default__1(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1410_;
}
pub unsafe fn l_Lake_instInhabitedPatternDescr(
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPatternDescr___closed__0_once),
        _init_l_Lake_instInhabitedPatternDescr___closed__0,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lake_instCoePatternDescr___lam__0(
    mut v_p_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1415_, 0, v_p_1414_);
    return v___x_1415_;
}
pub unsafe fn l_Lake_instCoePatternDescr(
    mut v_00_u03b2_1417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1419_ = l_Lake_instCoePatternDescr___closed__0;
    return v___f_1419_;
}
pub unsafe fn l_Lake_Pattern_matches___redArg(
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_self_1421_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_filter_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    v_filter_1422_ = crate::leanh::lean_ctor_get(v_self_1421_, 0);
    crate::leanh::lean_inc_ref(v_filter_1422_);
    crate::leanh::lean_dec_ref(v_self_1421_);
    v___x_1423_ = crate::leanh::lean_apply_1(v_filter_1422_, v_a_1420_);
    v___x_1424_ = (crate::leanh::lean_unbox(v___x_1423_) as u8);
    return v___x_1424_;
}
pub unsafe fn l_Lake_Pattern_matches___redArg___boxed(
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_self_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lake_Pattern_matches___redArg(v_a_1425_, v_self_1426_);
    v_r_1428_ = crate::leanh::lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Lake_Pattern_matches(
    mut v_00_u03b1_1429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_self_1432_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_filter_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    v_filter_1433_ = crate::leanh::lean_ctor_get(v_self_1432_, 0);
    crate::leanh::lean_inc_ref(v_filter_1433_);
    crate::leanh::lean_dec_ref(v_self_1432_);
    v___x_1434_ = crate::leanh::lean_apply_1(v_filter_1433_, v_a_1431_);
    v___x_1435_ = (crate::leanh::lean_unbox(v___x_1434_) as u8);
    return v___x_1435_;
}
pub unsafe fn l_Lake_Pattern_matches___boxed(
    mut v_00_u03b1_1436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_self_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: u8 = 0;
    let mut v_r_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ =
        l_Lake_Pattern_matches(v_00_u03b1_1436_, v_00_u03b2_1437_, v_a_1438_, v_self_1439_);
    v_r_1441_ = crate::leanh::lean_box((v_res_1440_) as usize);
    return v_r_1441_;
}
pub unsafe fn l_Lake_instIsPatternPattern___lam__0(
    mut v_self_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_filter_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    v_filter_1444_ = crate::leanh::lean_ctor_get(v_self_1442_, 0);
    crate::leanh::lean_inc_ref(v_filter_1444_);
    crate::leanh::lean_dec_ref(v_self_1442_);
    v___x_1445_ = crate::leanh::lean_apply_1(v_filter_1444_, v___y_1443_);
    v___x_1446_ = (crate::leanh::lean_unbox(v___x_1445_) as u8);
    return v___x_1446_;
}
pub unsafe fn l_Lake_instIsPatternPattern___lam__0___boxed(
    mut v_self_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1449_: u8 = 0;
    let mut v_r_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Lake_instIsPatternPattern___lam__0(v_self_1447_, v___y_1448_);
    v_r_1450_ = crate::leanh::lean_box((v_res_1449_) as usize);
    return v_r_1450_;
}
pub unsafe fn l_Lake_instIsPatternPattern(
    mut v_00_u03b1_1452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1454_ = l_Lake_instIsPatternPattern___closed__0;
    return v___f_1454_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__0(
    mut v_val_1455_: *mut crate::leanh::LeanObject,
    mut v___x_1456_: u8,
    mut v_v_1457_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_filter_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    v_filter_1458_ = crate::leanh::lean_ctor_get(v_v_1457_, 0);
    crate::leanh::lean_inc_ref(v_filter_1458_);
    crate::leanh::lean_dec_ref(v_v_1457_);
    v___x_1459_ = crate::leanh::lean_apply_1(v_filter_1458_, v_val_1455_);
    v___x_1460_ = (crate::leanh::lean_unbox(v___x_1459_) as u8);
    if v___x_1460_ == 0 {
        return v___x_1456_;
    } else {
        let mut v___x_1461_: u8 = 0;
        v___x_1461_ = 0;
        return v___x_1461_;
    }
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__0___boxed(
    mut v_val_1462_: *mut crate::leanh::LeanObject,
    mut v___x_1463_: *mut crate::leanh::LeanObject,
    mut v_v_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_220__boxed_1465_: u8 = 0;
    let mut v_res_1466_: u8 = 0;
    let mut v_r_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_220__boxed_1465_ = (crate::leanh::lean_unbox(v___x_1463_) as u8);
    v_res_1466_ = l_Lake_PatternDescr_matches___redArg___lam__0(
        v_val_1462_,
        v___x_220__boxed_1465_,
        v_v_1464_,
    );
    v_r_1467_ = crate::leanh::lean_box((v_res_1466_) as usize);
    return v_r_1467_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__1(
    mut v_val_1468_: *mut crate::leanh::LeanObject,
    mut v_x_1469_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_filter_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: u8 = 0;
    v_filter_1470_ = crate::leanh::lean_ctor_get(v_x_1469_, 0);
    crate::leanh::lean_inc_ref(v_filter_1470_);
    crate::leanh::lean_dec_ref(v_x_1469_);
    v___x_1471_ = crate::leanh::lean_apply_1(v_filter_1470_, v_val_1468_);
    v___x_1472_ = (crate::leanh::lean_unbox(v___x_1471_) as u8);
    return v___x_1472_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___lam__1___boxed(
    mut v_val_1473_: *mut crate::leanh::LeanObject,
    mut v_x_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: u8 = 0;
    let mut v_r_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_1473_, v_x_1474_);
    v_r_1476_ = crate::leanh::lean_box((v_res_1475_) as usize);
    return v_r_1476_;
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg(
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_val_1497_: *mut crate::leanh::LeanObject,
    mut v_self_1498_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_self_1498_) {
        0 => {
            let mut v_p_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_filter_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1502_: u8 = 0;
            crate::leanh::lean_dec_ref(v_inst_1496_);
            v_p_1499_ = crate::leanh::lean_ctor_get(v_self_1498_, 0);
            crate::leanh::lean_inc_ref(v_p_1499_);
            crate::leanh::lean_dec_ref_known(v_self_1498_, 1);
            v_filter_1500_ = crate::leanh::lean_ctor_get(v_p_1499_, 0);
            crate::leanh::lean_inc_ref(v_filter_1500_);
            crate::leanh::lean_dec_ref(v_p_1499_);
            v___x_1501_ = crate::leanh::lean_apply_1(v_filter_1500_, v_val_1497_);
            v___x_1502_ = (crate::leanh::lean_unbox(v___x_1501_) as u8);
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
            let mut v_ps_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1509_: u8 = 0;
            crate::leanh::lean_dec_ref(v_inst_1496_);
            v_ps_1505_ = crate::leanh::lean_ctor_get(v_self_1498_, 0);
            crate::leanh::lean_inc_ref(v_ps_1505_);
            crate::leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1506_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1507_ = lean_array_get_size(v_ps_1505_);
            v___x_1508_ = l_Lake_PatternDescr_matches___redArg___closed__9;
            v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
            if v___x_1509_ == 0 {
                let mut v___x_1510_: u8 = 0;
                crate::leanh::lean_dec_ref(v_ps_1505_);
                crate::leanh::lean_dec(v_val_1497_);
                v___x_1510_ = 1;
                return v___x_1510_;
            } else {
                if v___x_1509_ == 0 {
                    crate::leanh::lean_dec_ref(v_ps_1505_);
                    crate::leanh::lean_dec(v_val_1497_);
                    return v___x_1509_;
                } else {
                    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1513_: usize = 0;
                    let mut v___x_1514_: usize = 0;
                    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1516_: u8 = 0;
                    v___x_1511_ = crate::leanh::lean_box((v___x_1509_) as usize);
                    v___f_1512_ = crate::leanh::lean_alloc_closure(
                        l_Lake_PatternDescr_matches___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1512_, 0, v_val_1497_);
                    crate::leanh::lean_closure_set(v___f_1512_, 1, v___x_1511_);
                    v___x_1513_ = 0usize;
                    v___x_1514_ = lean_usize_of_nat(v___x_1507_);
                    v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1508_,
                        v___f_1512_,
                        v_ps_1505_,
                        v___x_1513_,
                        v___x_1514_,
                    );
                    v___x_1516_ = (crate::leanh::lean_unbox(v___x_1515_) as u8);
                    crate::leanh::lean_dec(v___x_1515_);
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
            let mut v_ps_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1522_: u8 = 0;
            crate::leanh::lean_dec_ref(v_inst_1496_);
            v_ps_1518_ = crate::leanh::lean_ctor_get(v_self_1498_, 0);
            crate::leanh::lean_inc_ref(v_ps_1518_);
            crate::leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1519_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1520_ = lean_array_get_size(v_ps_1518_);
            v___x_1521_ = l_Lake_PatternDescr_matches___redArg___closed__9;
            v___x_1522_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
            if v___x_1522_ == 0 {
                crate::leanh::lean_dec_ref(v_ps_1518_);
                crate::leanh::lean_dec(v_val_1497_);
                return v___x_1522_;
            } else {
                if v___x_1522_ == 0 {
                    crate::leanh::lean_dec_ref(v_ps_1518_);
                    crate::leanh::lean_dec(v_val_1497_);
                    return v___x_1522_;
                } else {
                    let mut v___f_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1524_: usize = 0;
                    let mut v___x_1525_: usize = 0;
                    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1527_: u8 = 0;
                    v___f_1523_ = crate::leanh::lean_alloc_closure(
                        l_Lake_PatternDescr_matches___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1523_, 0, v_val_1497_);
                    v___x_1524_ = 0usize;
                    v___x_1525_ = lean_usize_of_nat(v___x_1520_);
                    v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1521_,
                        v___f_1523_,
                        v_ps_1518_,
                        v___x_1524_,
                        v___x_1525_,
                    );
                    v___x_1527_ = (crate::leanh::lean_unbox(v___x_1526_) as u8);
                    crate::leanh::lean_dec(v___x_1526_);
                    return v___x_1527_;
                }
            }
        }
        _ => {
            let mut v_p_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1530_: u8 = 0;
            v_p_1528_ = crate::leanh::lean_ctor_get(v_self_1498_, 0);
            crate::leanh::lean_inc(v_p_1528_);
            crate::leanh::lean_dec_ref_known(v_self_1498_, 1);
            v___x_1529_ = crate::leanh::lean_apply_2(v_inst_1496_, v_p_1528_, v_val_1497_);
            v___x_1530_ = (crate::leanh::lean_unbox(v___x_1529_) as u8);
            return v___x_1530_;
        }
    }
}
pub unsafe fn l_Lake_PatternDescr_matches___redArg___boxed(
    mut v_inst_1531_: *mut crate::leanh::LeanObject,
    mut v_val_1532_: *mut crate::leanh::LeanObject,
    mut v_self_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: u8 = 0;
    let mut v_r_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lake_PatternDescr_matches___redArg(v_inst_1531_, v_val_1532_, v_self_1533_);
    v_r_1535_ = crate::leanh::lean_box((v_res_1534_) as usize);
    return v_r_1535_;
}
pub unsafe fn l_Lake_PatternDescr_matches(
    mut v_00_u03b2_1536_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1537_: *mut crate::leanh::LeanObject,
    mut v_inst_1538_: *mut crate::leanh::LeanObject,
    mut v_val_1539_: *mut crate::leanh::LeanObject,
    mut v_self_1540_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1541_: u8 = 0;
    v___x_1541_ = l_Lake_PatternDescr_matches___redArg(v_inst_1538_, v_val_1539_, v_self_1540_);
    return v___x_1541_;
}
pub unsafe fn l_Lake_PatternDescr_matches___boxed(
    mut v_00_u03b2_1542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_val_1545_: *mut crate::leanh::LeanObject,
    mut v_self_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1547_: u8 = 0;
    let mut v_r_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_Lake_PatternDescr_matches(
        v_00_u03b2_1542_,
        v_00_u03b1_1543_,
        v_inst_1544_,
        v_val_1545_,
        v_self_1546_,
    );
    v_r_1548_ = crate::leanh::lean_box((v_res_1547_) as usize);
    return v_r_1548_;
}
pub unsafe fn l_Lake_instIsPatternPatternDescr___redArg(
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1550_ = crate::leanh::lean_alloc_closure(
        l_Lake_PatternDescr_matches___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1550_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1550_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1550_, 2, v_inst_1549_);
    v___x_1551_ = crate::leanh::lean_alloc_closure(l_flip as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1551_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1551_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1551_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1551_, 3, v___x_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Lake_instIsPatternPatternDescr(
    mut v_00_u03b2_1552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1553_: *mut crate::leanh::LeanObject,
    mut v_inst_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lake_Pattern_ofFn___redArg(
    mut v_f_1556_: *mut crate::leanh::LeanObject,
    mut v_name_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = crate::leanh::lean_box(0);
    v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1559_, 0, v_f_1556_);
    crate::leanh::lean_ctor_set(v___x_1559_, 1, v_name_1557_);
    crate::leanh::lean_ctor_set(v___x_1559_, 2, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_Pattern_ofFn(
    mut v_00_u03b1_1560_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1561_: *mut crate::leanh::LeanObject,
    mut v_f_1562_: *mut crate::leanh::LeanObject,
    mut v_name_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = crate::leanh::lean_box(0);
    v___x_1565_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1565_, 0, v_f_1562_);
    crate::leanh::lean_ctor_set(v___x_1565_, 1, v_name_1563_);
    crate::leanh::lean_ctor_set(v___x_1565_, 2, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lake_instCoeForallBoolPattern___lam__0(
    mut v_f_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = crate::leanh::lean_box(0);
    v___x_1568_ = crate::leanh::lean_box(0);
    v___x_1569_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1569_, 0, v_f_1566_);
    crate::leanh::lean_ctor_set(v___x_1569_, 1, v___x_1567_);
    crate::leanh::lean_ctor_set(v___x_1569_, 2, v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Lake_instCoeForallBoolPattern(
    mut v_00_u03b1_1571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1573_ = l_Lake_instCoeForallBoolPattern___closed__0;
    return v___f_1573_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg___lam__0(
    mut v_inst_1574_: *mut crate::leanh::LeanObject,
    mut v_descr_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1577_: u8 = 0;
    v___x_1577_ = l_Lake_PatternDescr_matches___redArg(v_inst_1574_, v_x_1576_, v_descr_1575_);
    return v___x_1577_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_descr_1579_: *mut crate::leanh::LeanObject,
    mut v_x_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1581_: u8 = 0;
    let mut v_r_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_1578_, v_descr_1579_, v_x_1580_);
    v_r_1582_ = crate::leanh::lean_box((v_res_1581_) as usize);
    return v_r_1582_;
}
pub unsafe fn l_Lake_Pattern_ofDescr___redArg(
    mut v_inst_1583_: *mut crate::leanh::LeanObject,
    mut v_descr_1584_: *mut crate::leanh::LeanObject,
    mut v_name_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_descr_1584_);
    v___f_1586_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_ofDescr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1586_, 0, v_inst_1583_);
    crate::leanh::lean_closure_set(v___f_1586_, 1, v_descr_1584_);
    v___x_1587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1587_, 0, v_descr_1584_);
    v___x_1588_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1588_, 0, v___f_1586_);
    crate::leanh::lean_ctor_set(v___x_1588_, 1, v_name_1585_);
    crate::leanh::lean_ctor_set(v___x_1588_, 2, v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Lake_Pattern_ofDescr(
    mut v_00_u03b2_1589_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1590_: *mut crate::leanh::LeanObject,
    mut v_inst_1591_: *mut crate::leanh::LeanObject,
    mut v_descr_1592_: *mut crate::leanh::LeanObject,
    mut v_name_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_descr_1592_);
    v___f_1594_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_ofDescr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1594_, 0, v_inst_1591_);
    crate::leanh::lean_closure_set(v___f_1594_, 1, v_descr_1592_);
    v___x_1595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1595_, 0, v_descr_1592_);
    v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1596_, 0, v___f_1594_);
    crate::leanh::lean_ctor_set(v___x_1596_, 1, v_name_1593_);
    crate::leanh::lean_ctor_set(v___x_1596_, 2, v___x_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(
    mut v_inst_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1600_: u8 = 0;
    v___x_1600_ = l_Lake_PatternDescr_matches___redArg(v_inst_1597_, v_x_1599_, v_x_1598_);
    return v___x_1600_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(
    mut v_inst_1601_: *mut crate::leanh::LeanObject,
    mut v_x_1602_: *mut crate::leanh::LeanObject,
    mut v_x_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: u8 = 0;
    let mut v_r_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(
        v_inst_1601_,
        v_x_1602_,
        v_x_1603_,
    );
    v_r_1605_ = crate::leanh::lean_box((v_res_1604_) as usize);
    return v_r_1605_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_x_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_1607_);
    v___f_1608_ = crate::leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1608_, 0, v_inst_1606_);
    crate::leanh::lean_closure_set(v___f_1608_, 1, v_x_1607_);
    v___x_1609_ = crate::leanh::lean_box(0);
    v___x_1610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1610_, 0, v_x_1607_);
    v___x_1611_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1611_, 0, v___f_1608_);
    crate::leanh::lean_ctor_set(v___x_1611_, 1, v___x_1609_);
    crate::leanh::lean_ctor_set(v___x_1611_, 2, v___x_1610_);
    return v___x_1611_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(
    mut v_inst_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1613_ = crate::leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1613_, 0, v_inst_1612_);
    return v___f_1613_;
}
pub unsafe fn l_Lake_instCoePatternDescrPatternOfIsPattern(
    mut v_00_u03b2_1614_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1615_: *mut crate::leanh::LeanObject,
    mut v_inst_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1617_ = crate::leanh::lean_alloc_closure(
        l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1617_, 0, v_inst_1616_);
    return v___f_1617_;
}
pub unsafe fn l_Lake_Pattern_not___redArg___lam__0(
    mut v_inst_1618_: *mut crate::leanh::LeanObject,
    mut v___x_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1621_: u8 = 0;
    v___x_1621_ = l_Lake_PatternDescr_matches___redArg(v_inst_1618_, v_x_1620_, v___x_1619_);
    return v___x_1621_;
}
pub unsafe fn l_Lake_Pattern_not___redArg___lam__0___boxed(
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v___x_1623_: *mut crate::leanh::LeanObject,
    mut v_x_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: u8 = 0;
    let mut v_r_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_1622_, v___x_1623_, v_x_1624_);
    v_r_1626_ = crate::leanh::lean_box((v_res_1625_) as usize);
    return v_r_1626_;
}
pub unsafe fn l_Lake_Pattern_not___redArg(
    mut v_inst_1627_: *mut crate::leanh::LeanObject,
    mut v_p_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1629_, 0, v_p_1628_);
    crate::leanh::lean_inc_ref(v___x_1629_);
    v___f_1630_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1630_, 0, v_inst_1627_);
    crate::leanh::lean_closure_set(v___f_1630_, 1, v___x_1629_);
    v___x_1631_ = crate::leanh::lean_box(0);
    v___x_1632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1632_, 0, v___x_1629_);
    v___x_1633_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1633_, 0, v___f_1630_);
    crate::leanh::lean_ctor_set(v___x_1633_, 1, v___x_1631_);
    crate::leanh::lean_ctor_set(v___x_1633_, 2, v___x_1632_);
    return v___x_1633_;
}
pub unsafe fn l_Lake_Pattern_not(
    mut v_00_u03b2_1634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1635_: *mut crate::leanh::LeanObject,
    mut v_inst_1636_: *mut crate::leanh::LeanObject,
    mut v_p_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1638_, 0, v_p_1637_);
    crate::leanh::lean_inc_ref(v___x_1638_);
    v___f_1639_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1639_, 0, v_inst_1636_);
    crate::leanh::lean_closure_set(v___f_1639_, 1, v___x_1638_);
    v___x_1640_ = crate::leanh::lean_box(0);
    v___x_1641_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1638_);
    v___x_1642_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1642_, 0, v___f_1639_);
    crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1640_);
    crate::leanh::lean_ctor_set(v___x_1642_, 2, v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lake_Pattern_all___redArg(
    mut v_inst_1643_: *mut crate::leanh::LeanObject,
    mut v_ps_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1645_, 0, v_ps_1644_);
    crate::leanh::lean_inc_ref(v___x_1645_);
    v___f_1646_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1646_, 0, v_inst_1643_);
    crate::leanh::lean_closure_set(v___f_1646_, 1, v___x_1645_);
    v___x_1647_ = crate::leanh::lean_box(0);
    v___x_1648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1645_);
    v___x_1649_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1649_, 0, v___f_1646_);
    crate::leanh::lean_ctor_set(v___x_1649_, 1, v___x_1647_);
    crate::leanh::lean_ctor_set(v___x_1649_, 2, v___x_1648_);
    return v___x_1649_;
}
pub unsafe fn l_Lake_Pattern_all(
    mut v_00_u03b2_1650_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_ps_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1654_, 0, v_ps_1653_);
    crate::leanh::lean_inc_ref(v___x_1654_);
    v___f_1655_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1655_, 0, v_inst_1652_);
    crate::leanh::lean_closure_set(v___f_1655_, 1, v___x_1654_);
    v___x_1656_ = crate::leanh::lean_box(0);
    v___x_1657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1654_);
    v___x_1658_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1658_, 0, v___f_1655_);
    crate::leanh::lean_ctor_set(v___x_1658_, 1, v___x_1656_);
    crate::leanh::lean_ctor_set(v___x_1658_, 2, v___x_1657_);
    return v___x_1658_;
}
pub unsafe fn l_Lake_Pattern_any___redArg(
    mut v_inst_1659_: *mut crate::leanh::LeanObject,
    mut v_ps_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1661_, 0, v_ps_1660_);
    crate::leanh::lean_inc_ref(v___x_1661_);
    v___f_1662_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1662_, 0, v_inst_1659_);
    crate::leanh::lean_closure_set(v___f_1662_, 1, v___x_1661_);
    v___x_1663_ = crate::leanh::lean_box(0);
    v___x_1664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1661_);
    v___x_1665_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___f_1662_);
    crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1663_);
    crate::leanh::lean_ctor_set(v___x_1665_, 2, v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn l_Lake_Pattern_any(
    mut v_00_u03b2_1666_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_ps_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1670_, 0, v_ps_1669_);
    crate::leanh::lean_inc_ref(v___x_1670_);
    v___f_1671_ = crate::leanh::lean_alloc_closure(
        l_Lake_Pattern_not___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1671_, 0, v_inst_1668_);
    crate::leanh::lean_closure_set(v___f_1671_, 1, v___x_1670_);
    v___x_1672_ = crate::leanh::lean_box(0);
    v___x_1673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1673_, 0, v___x_1670_);
    v___x_1674_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1674_, 0, v___f_1671_);
    crate::leanh::lean_ctor_set(v___x_1674_, 1, v___x_1672_);
    crate::leanh::lean_ctor_set(v___x_1674_, 2, v___x_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Lake_PatternDescr_empty(
    mut v_00_u03b1_1679_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lake_PatternDescr_empty___closed__1;
    return v___x_1681_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Lake_PatternDescr_empty(crate::leanh::lean_box(0), crate::leanh::lean_box(0));
    return v___x_1685_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2_once),
        _init_l_Lake_Pattern_empty___closed__2,
    );
    v___x_1687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn _init_l_Lake_Pattern_empty___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__3_once),
        _init_l_Lake_Pattern_empty___closed__3,
    );
    v___x_1689_ = l_Lake_Pattern_empty___closed__1;
    v___f_1690_ = l_Lake_instInhabitedPattern_default__1___closed__0;
    v___x_1691_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___f_1690_);
    crate::leanh::lean_ctor_set(v___x_1691_, 1, v___x_1689_);
    crate::leanh::lean_ctor_set(v___x_1691_, 2, v___x_1688_);
    return v___x_1691_;
}
pub unsafe fn l_Lake_Pattern_empty(
    mut v_00_u03b1_1692_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__4_once),
        _init_l_Lake_Pattern_empty___closed__4,
    );
    return v___x_1694_;
}
pub unsafe fn l_Lake_instEmptyCollectionPatternDescr(
    mut v_00_u03b1_1695_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Pattern_empty___closed__2_once),
        _init_l_Lake_Pattern_empty___closed__2,
    );
    return v___x_1697_;
}
pub unsafe fn _init_l_Lake_instEmptyCollectionPattern___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lake_Pattern_empty(crate::leanh::lean_box(0), crate::leanh::lean_box(0));
    return v___x_1698_;
}
pub unsafe fn l_Lake_instEmptyCollectionPattern(
    mut v_00_u03b1_1699_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instEmptyCollectionPattern___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instEmptyCollectionPattern___closed__0_once),
        _init_l_Lake_instEmptyCollectionPattern___closed__0,
    );
    return v___x_1701_;
}
pub unsafe fn l_Lake_PatternDescr_star(
    mut v_00_u03b1_1704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lake_PatternDescr_star___closed__0;
    return v___x_1706_;
}
pub unsafe fn l_Lake_Pattern_star___lam__0(mut v_x_1707_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1708_: u8 = 0;
    v___x_1708_ = 1;
    return v___x_1708_;
}
pub unsafe fn l_Lake_Pattern_star___lam__0___boxed(
    mut v_x_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1710_: u8 = 0;
    let mut v_r_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lake_Pattern_star___lam__0(v_x_1709_);
    crate::leanh::lean_dec(v_x_1709_);
    v_r_1711_ = crate::leanh::lean_box((v_res_1710_) as usize);
    return v_r_1711_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Lake_PatternDescr_star(crate::leanh::lean_box(0), crate::leanh::lean_box(0));
    return v___x_1716_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__3_once),
        _init_l_Lake_Pattern_star___closed__3,
    );
    v___x_1718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lake_Pattern_star___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__4_once),
        _init_l_Lake_Pattern_star___closed__4,
    );
    v___x_1720_ = l_Lake_Pattern_star___closed__2;
    v___f_1721_ = l_Lake_Pattern_star___closed__0;
    v___x_1722_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1722_, 0, v___f_1721_);
    crate::leanh::lean_ctor_set(v___x_1722_, 1, v___x_1720_);
    crate::leanh::lean_ctor_set(v___x_1722_, 2, v___x_1719_);
    return v___x_1722_;
}
pub unsafe fn l_Lake_Pattern_star(
    mut v_00_u03b1_1723_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Pattern_star___closed__5_once),
        _init_l_Lake_Pattern_star___closed__5,
    );
    return v___x_1725_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorIdx(
    mut v_x_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1726_) {
        0 => {
            let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1727_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1727_;
        }
        1 => {
            let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1728_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1728_;
        }
        _ => {
            let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1729_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1729_;
        }
    }
}
pub unsafe fn l_Lake_StrPatDescr_ctorIdx___boxed(
    mut v_x_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lake_StrPatDescr_ctorIdx(v_x_1730_);
    crate::leanh::lean_dec_ref(v_x_1730_);
    return v_res_1731_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim___redArg(
    mut v_t_1732_: *mut crate::leanh::LeanObject,
    mut v_k_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_xs_1734_ = crate::leanh::lean_ctor_get(v_t_1732_, 0);
    crate::leanh::lean_inc_ref(v_xs_1734_);
    crate::leanh::lean_dec_ref(v_t_1732_);
    v___x_1735_ = crate::leanh::lean_apply_1(v_k_1733_, v_xs_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim(
    mut v_motive_1736_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1737_: *mut crate::leanh::LeanObject,
    mut v_t_1738_: *mut crate::leanh::LeanObject,
    mut v_h_1739_: *mut crate::leanh::LeanObject,
    mut v_k_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1738_, v_k_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Lake_StrPatDescr_ctorElim___boxed(
    mut v_motive_1742_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1743_: *mut crate::leanh::LeanObject,
    mut v_t_1744_: *mut crate::leanh::LeanObject,
    mut v_h_1745_: *mut crate::leanh::LeanObject,
    mut v_k_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lake_StrPatDescr_ctorElim(
        v_motive_1742_,
        v_ctorIdx_1743_,
        v_t_1744_,
        v_h_1745_,
        v_k_1746_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1743_);
    return v_res_1747_;
}
pub unsafe fn l_Lake_StrPatDescr_mem_elim___redArg(
    mut v_t_1748_: *mut crate::leanh::LeanObject,
    mut v_mem_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1748_, v_mem_1749_);
    return v___x_1750_;
}
pub unsafe fn l_Lake_StrPatDescr_mem_elim(
    mut v_motive_1751_: *mut crate::leanh::LeanObject,
    mut v_t_1752_: *mut crate::leanh::LeanObject,
    mut v_h_1753_: *mut crate::leanh::LeanObject,
    mut v_mem_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1752_, v_mem_1754_);
    return v___x_1755_;
}
pub unsafe fn l_Lake_StrPatDescr_startsWith_elim___redArg(
    mut v_t_1756_: *mut crate::leanh::LeanObject,
    mut v_startsWith_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1756_, v_startsWith_1757_);
    return v___x_1758_;
}
pub unsafe fn l_Lake_StrPatDescr_startsWith_elim(
    mut v_motive_1759_: *mut crate::leanh::LeanObject,
    mut v_t_1760_: *mut crate::leanh::LeanObject,
    mut v_h_1761_: *mut crate::leanh::LeanObject,
    mut v_startsWith_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1760_, v_startsWith_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Lake_StrPatDescr_endsWith_elim___redArg(
    mut v_t_1764_: *mut crate::leanh::LeanObject,
    mut v_endsWith_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1764_, v_endsWith_1765_);
    return v___x_1766_;
}
pub unsafe fn l_Lake_StrPatDescr_endsWith_elim(
    mut v_motive_1767_: *mut crate::leanh::LeanObject,
    mut v_t_1768_: *mut crate::leanh::LeanObject,
    mut v_h_1769_: *mut crate::leanh::LeanObject,
    mut v_endsWith_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_1768_, v_endsWith_1770_);
    return v___x_1771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_as_1779_: *mut crate::leanh::LeanObject,
    mut v_i_1780_: usize,
    mut v_stop_1781_: usize,
) -> u8 {
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_as_1790_: *mut crate::leanh::LeanObject,
    mut v_i_1791_: *mut crate::leanh::LeanObject,
    mut v_stop_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1793_: usize = 0;
    let mut v_stop_boxed_1794_: usize = 0;
    let mut v_res_1795_: u8 = 0;
    let mut v_r_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1793_ = crate::leanh::lean_unbox_usize(v_i_1791_);
    crate::leanh::lean_dec(v_i_1791_);
    v_stop_boxed_1794_ = crate::leanh::lean_unbox_usize(v_stop_1792_);
    crate::leanh::lean_dec(v_stop_1792_);
    v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_1789_, v_as_1790_, v_i_boxed_1793_, v_stop_boxed_1794_);
    crate::leanh::lean_dec_ref(v_as_1790_);
    crate::leanh::lean_dec_ref(v_a_1789_);
    v_r_1796_ = crate::leanh::lean_box((v_res_1795_) as usize);
    return v_r_1796_;
}
pub unsafe fn l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(
    mut v_as_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    v___x_1799_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_as_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1807_: u8 = 0;
    let mut v_r_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_1805_, v_a_1806_);
    crate::leanh::lean_dec_ref(v_a_1806_);
    crate::leanh::lean_dec_ref(v_as_1805_);
    v_r_1808_ = crate::leanh::lean_box((v_res_1807_) as usize);
    return v_r_1808_;
}
pub unsafe fn l_Lake_StrPatDescr_matches(
    mut v_s_1809_: *mut crate::leanh::LeanObject,
    mut v_self_1810_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_self_1810_) {
        0 => {
            let mut v_xs_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1812_: u8 = 0;
            v_xs_1811_ = crate::leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1812_ =
                l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_1811_, v_s_1809_);
            return v___x_1812_;
        }
        1 => {
            let mut v_affix_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1816_: u8 = 0;
            v_affix_1813_ = crate::leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1814_ = lean_string_utf8_byte_size(v_s_1809_);
            v___x_1815_ = lean_string_utf8_byte_size(v_affix_1813_);
            v___x_1816_ = lean_nat_dec_le(v___x_1815_, v___x_1814_);
            if v___x_1816_ == 0 {
                return v___x_1816_;
            } else {
                let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1818_: u8 = 0;
                v___x_1817_ = crate::leanh::lean_unsigned_to_nat(0);
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
            let mut v_affix_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1822_: u8 = 0;
            v_affix_1819_ = crate::leanh::lean_ctor_get(v_self_1810_, 0);
            v___x_1820_ = lean_string_utf8_byte_size(v_s_1809_);
            v___x_1821_ = lean_string_utf8_byte_size(v_affix_1819_);
            v___x_1822_ = lean_nat_dec_le(v___x_1821_, v___x_1820_);
            if v___x_1822_ == 0 {
                return v___x_1822_;
            } else {
                let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1825_: u8 = 0;
                v___x_1823_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1824_ = lean_nat_sub(v___x_1820_, v___x_1821_);
                v___x_1825_ = lean_string_memcmp(
                    v_s_1809_,
                    v_affix_1819_,
                    v___x_1824_,
                    v___x_1823_,
                    v___x_1821_,
                );
                crate::leanh::lean_dec(v___x_1824_);
                return v___x_1825_;
            }
        }
    }
}
pub unsafe fn l_Lake_StrPatDescr_matches___boxed(
    mut v_s_1826_: *mut crate::leanh::LeanObject,
    mut v_self_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1828_: u8 = 0;
    let mut v_r_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lake_StrPatDescr_matches(v_s_1826_, v_self_1827_);
    crate::leanh::lean_dec_ref(v_self_1827_);
    crate::leanh::lean_dec_ref(v_s_1826_);
    v_r_1829_ = crate::leanh::lean_box((v_res_1828_) as usize);
    return v_r_1829_;
}
pub unsafe fn l_Lake_StrPat_mem___lam__0(
    mut v___x_1834_: *mut crate::leanh::LeanObject,
    mut v___x_1835_: *mut crate::leanh::LeanObject,
    mut v_x_1836_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1837_: u8 = 0;
    v___x_1837_ = l_Lake_PatternDescr_matches___redArg(v___x_1834_, v_x_1836_, v___x_1835_);
    return v___x_1837_;
}
pub unsafe fn l_Lake_StrPat_mem___lam__0___boxed(
    mut v___x_1838_: *mut crate::leanh::LeanObject,
    mut v___x_1839_: *mut crate::leanh::LeanObject,
    mut v_x_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: u8 = 0;
    let mut v_r_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Lake_StrPat_mem___lam__0(v___x_1838_, v___x_1839_, v_x_1840_);
    v_r_1842_ = crate::leanh::lean_box((v_res_1841_) as usize);
    return v_r_1842_;
}
pub unsafe fn l_Lake_StrPat_mem(
    mut v_xs_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1845_, 0, v_xs_1843_);
    v___x_1846_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1846_, 0, v___x_1845_);
    crate::leanh::lean_inc_ref(v___x_1846_);
    v___f_1847_ = crate::leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1847_, 0, v___x_1844_);
    crate::leanh::lean_closure_set(v___f_1847_, 1, v___x_1846_);
    v___x_1848_ = crate::leanh::lean_box(0);
    v___x_1849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1846_);
    v___x_1850_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1850_, 0, v___f_1847_);
    crate::leanh::lean_ctor_set(v___x_1850_, 1, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1850_, 2, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Lake_instCoeArrayStringStrPatDescr___lam__0(
    mut v_xs_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1852_, 0, v_xs_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lake_StrPat_startsWith(
    mut v_affix_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1859_, 0, v_affix_1857_);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    crate::leanh::lean_inc_ref(v___x_1860_);
    v___f_1861_ = crate::leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1861_, 0, v___x_1858_);
    crate::leanh::lean_closure_set(v___f_1861_, 1, v___x_1860_);
    v___x_1862_ = crate::leanh::lean_box(0);
    v___x_1863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1860_);
    v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1864_, 0, v___f_1861_);
    crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l_Lake_StrPat_endsWith(
    mut v_affix_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lake_instIsPatternStrPatDescrString;
    v___x_1867_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1867_, 0, v_affix_1865_);
    v___x_1868_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    crate::leanh::lean_inc_ref(v___x_1868_);
    v___f_1869_ = crate::leanh::lean_alloc_closure(
        l_Lake_StrPat_mem___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1869_, 0, v___x_1866_);
    crate::leanh::lean_closure_set(v___f_1869_, 1, v___x_1868_);
    v___x_1870_ = crate::leanh::lean_box(0);
    v___x_1871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1868_);
    v___x_1872_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1872_, 0, v___f_1869_);
    crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1870_);
    crate::leanh::lean_ctor_set(v___x_1872_, 2, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn l_Lake_StrPatDescr_beq(
    mut v_s_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1874_);
    v___x_1876_ = lean_array_push(v___x_1875_, v_s_1873_);
    v___x_1877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1877_, 0, v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn l_Lake_StrPat_beq___lam__0(
    mut v_s_1878_: *mut crate::leanh::LeanObject,
    mut v_x_1879_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1880_: u8 = 0;
    v___x_1880_ = lean_string_dec_eq(v_x_1879_, v_s_1878_);
    return v___x_1880_;
}
pub unsafe fn l_Lake_StrPat_beq___lam__0___boxed(
    mut v_s_1881_: *mut crate::leanh::LeanObject,
    mut v_x_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: u8 = 0;
    let mut v_r_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lake_StrPat_beq___lam__0(v_s_1881_, v_x_1882_);
    crate::leanh::lean_dec_ref(v_x_1882_);
    crate::leanh::lean_dec_ref(v_s_1881_);
    v_r_1884_ = crate::leanh::lean_box((v_res_1883_) as usize);
    return v_r_1884_;
}
pub unsafe fn l_Lake_StrPat_beq(
    mut v_s_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_1888_);
    v___f_1889_ = crate::leanh::lean_alloc_closure(
        l_Lake_StrPat_beq___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1889_, 0, v_s_1888_);
    v___x_1890_ = l_Lake_StrPat_beq___closed__1;
    v___x_1891_ = l_Lake_StrPatDescr_beq(v_s_1888_);
    v___x_1892_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    v___x_1893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
    v___x_1894_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1894_, 0, v___f_1889_);
    crate::leanh::lean_ctor_set(v___x_1894_, 1, v___x_1890_);
    crate::leanh::lean_ctor_set(v___x_1894_, 2, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorIdx(
    mut v_x_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1899_) {
        0 => {
            let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1900_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1900_;
        }
        1 => {
            let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1901_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1901_;
        }
        _ => {
            let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1902_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1902_;
        }
    }
}
pub unsafe fn l_Lake_PathPatDescr_ctorIdx___boxed(
    mut v_x_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_Lake_PathPatDescr_ctorIdx(v_x_1903_);
    crate::leanh::lean_dec_ref(v_x_1903_);
    return v_res_1904_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim___redArg(
    mut v_t_1905_: *mut crate::leanh::LeanObject,
    mut v_k_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_1907_ = crate::leanh::lean_ctor_get(v_t_1905_, 0);
    crate::leanh::lean_inc_ref(v_p_1907_);
    crate::leanh::lean_dec_ref(v_t_1905_);
    v___x_1908_ = crate::leanh::lean_apply_1(v_k_1906_, v_p_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim(
    mut v_motive_1909_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1910_: *mut crate::leanh::LeanObject,
    mut v_t_1911_: *mut crate::leanh::LeanObject,
    mut v_h_1912_: *mut crate::leanh::LeanObject,
    mut v_k_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1911_, v_k_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lake_PathPatDescr_ctorElim___boxed(
    mut v_motive_1915_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1916_: *mut crate::leanh::LeanObject,
    mut v_t_1917_: *mut crate::leanh::LeanObject,
    mut v_h_1918_: *mut crate::leanh::LeanObject,
    mut v_k_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lake_PathPatDescr_ctorElim(
        v_motive_1915_,
        v_ctorIdx_1916_,
        v_t_1917_,
        v_h_1918_,
        v_k_1919_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Lake_PathPatDescr_path_elim___redArg(
    mut v_t_1921_: *mut crate::leanh::LeanObject,
    mut v_path_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1921_, v_path_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Lake_PathPatDescr_path_elim(
    mut v_motive_1924_: *mut crate::leanh::LeanObject,
    mut v_t_1925_: *mut crate::leanh::LeanObject,
    mut v_h_1926_: *mut crate::leanh::LeanObject,
    mut v_path_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1925_, v_path_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lake_PathPatDescr_extension_elim___redArg(
    mut v_t_1929_: *mut crate::leanh::LeanObject,
    mut v_extension_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1929_, v_extension_1930_);
    return v___x_1931_;
}
pub unsafe fn l_Lake_PathPatDescr_extension_elim(
    mut v_motive_1932_: *mut crate::leanh::LeanObject,
    mut v_t_1933_: *mut crate::leanh::LeanObject,
    mut v_h_1934_: *mut crate::leanh::LeanObject,
    mut v_extension_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1933_, v_extension_1935_);
    return v___x_1936_;
}
pub unsafe fn l_Lake_PathPatDescr_fileName_elim___redArg(
    mut v_t_1937_: *mut crate::leanh::LeanObject,
    mut v_fileName_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1937_, v_fileName_1938_);
    return v___x_1939_;
}
pub unsafe fn l_Lake_PathPatDescr_fileName_elim(
    mut v_motive_1940_: *mut crate::leanh::LeanObject,
    mut v_t_1941_: *mut crate::leanh::LeanObject,
    mut v_h_1942_: *mut crate::leanh::LeanObject,
    mut v_fileName_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_1941_, v_fileName_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lake_instInhabitedPattern_default__1(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1945_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__0_once),
        _init_l_Lake_instInhabitedPathPatDescr_default___closed__0,
    );
    v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1947_, 0, v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPathPatDescr_default___closed__1_once),
        _init_l_Lake_instInhabitedPathPatDescr_default___closed__1,
    );
    return v___x_1948_;
}
pub unsafe fn _init_l_Lake_instInhabitedPathPatDescr() -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lake_instInhabitedPathPatDescr_default;
    return v___x_1949_;
}
pub unsafe fn l_Lake_PathPatDescr_eq___lam__0(
    mut v_p_1950_: *mut crate::leanh::LeanObject,
    mut v_x_1951_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1952_: u8 = 0;
    v___x_1952_ = lean_string_dec_eq(v_x_1951_, v_p_1950_);
    return v___x_1952_;
}
pub unsafe fn l_Lake_PathPatDescr_eq___lam__0___boxed(
    mut v_p_1953_: *mut crate::leanh::LeanObject,
    mut v_x_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: u8 = 0;
    let mut v_r_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lake_PathPatDescr_eq___lam__0(v_p_1953_, v_x_1954_);
    crate::leanh::lean_dec_ref(v_x_1954_);
    crate::leanh::lean_dec_ref(v_p_1953_);
    v_r_1956_ = crate::leanh::lean_box((v_res_1955_) as usize);
    return v_r_1956_;
}
pub unsafe fn l_Lake_PathPatDescr_eq(
    mut v_p_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_p_1957_);
    v___f_1958_ = crate::leanh::lean_alloc_closure(
        l_Lake_PathPatDescr_eq___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1958_, 0, v_p_1957_);
    v___x_1959_ = l_Lake_StrPat_beq___closed__1;
    v___x_1960_ = l_Lake_StrPatDescr_beq(v_p_1957_);
    v___x_1961_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1960_);
    v___x_1962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    v___x_1963_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1963_, 0, v___f_1958_);
    crate::leanh::lean_ctor_set(v___x_1963_, 1, v___x_1959_);
    crate::leanh::lean_ctor_set(v___x_1963_, 2, v___x_1962_);
    v___x_1964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1964_, 0, v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn l_Lake_PathPatDescr_matches(
    mut v_path_1965_: *mut crate::leanh::LeanObject,
    mut v_self_1966_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_self_1966_) {
        0 => {
            let mut v_p_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_filter_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1971_: u8 = 0;
            v_p_1967_ = crate::leanh::lean_ctor_get(v_self_1966_, 0);
            crate::leanh::lean_inc_ref(v_p_1967_);
            crate::leanh::lean_dec_ref_known(v_self_1966_, 1);
            v_filter_1968_ = crate::leanh::lean_ctor_get(v_p_1967_, 0);
            crate::leanh::lean_inc_ref(v_filter_1968_);
            crate::leanh::lean_dec_ref(v_p_1967_);
            v___x_1969_ = l_System_FilePath_normalize(v_path_1965_);
            v___x_1970_ = crate::leanh::lean_apply_1(v_filter_1968_, v___x_1969_);
            v___x_1971_ = (crate::leanh::lean_unbox(v___x_1970_) as u8);
            return v___x_1971_;
        }
        1 => {
            let mut v_p_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_p_1972_ = crate::leanh::lean_ctor_get(v_self_1966_, 0);
            crate::leanh::lean_inc_ref(v_p_1972_);
            crate::leanh::lean_dec_ref_known(v_self_1966_, 1);
            v___x_1973_ = l_System_FilePath_extension(v_path_1965_);
            if crate::leanh::lean_obj_tag(v___x_1973_) == 0 {
                let mut v___x_1974_: u8 = 0;
                crate::leanh::lean_dec_ref(v_p_1972_);
                v___x_1974_ = 0;
                return v___x_1974_;
            } else {
                let mut v_val_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_filter_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1978_: u8 = 0;
                v_val_1975_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                crate::leanh::lean_inc(v_val_1975_);
                crate::leanh::lean_dec_ref_known(v___x_1973_, 1);
                v_filter_1976_ = crate::leanh::lean_ctor_get(v_p_1972_, 0);
                crate::leanh::lean_inc_ref(v_filter_1976_);
                crate::leanh::lean_dec_ref(v_p_1972_);
                v___x_1977_ = crate::leanh::lean_apply_1(v_filter_1976_, v_val_1975_);
                v___x_1978_ = (crate::leanh::lean_unbox(v___x_1977_) as u8);
                return v___x_1978_;
            }
        }
        _ => {
            let mut v_p_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_p_1979_ = crate::leanh::lean_ctor_get(v_self_1966_, 0);
            crate::leanh::lean_inc_ref(v_p_1979_);
            crate::leanh::lean_dec_ref_known(v_self_1966_, 1);
            v___x_1980_ = l_System_FilePath_fileName(v_path_1965_);
            if crate::leanh::lean_obj_tag(v___x_1980_) == 0 {
                let mut v___x_1981_: u8 = 0;
                crate::leanh::lean_dec_ref(v_p_1979_);
                v___x_1981_ = 0;
                return v___x_1981_;
            } else {
                let mut v_val_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_filter_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1985_: u8 = 0;
                v_val_1982_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                crate::leanh::lean_inc(v_val_1982_);
                crate::leanh::lean_dec_ref_known(v___x_1980_, 1);
                v_filter_1983_ = crate::leanh::lean_ctor_get(v_p_1979_, 0);
                crate::leanh::lean_inc_ref(v_filter_1983_);
                crate::leanh::lean_dec_ref(v_p_1979_);
                v___x_1984_ = crate::leanh::lean_apply_1(v_filter_1983_, v_val_1982_);
                v___x_1985_ = (crate::leanh::lean_unbox(v___x_1984_) as u8);
                return v___x_1985_;
            }
        }
    }
}
pub unsafe fn l_Lake_PathPatDescr_matches___boxed(
    mut v_path_1986_: *mut crate::leanh::LeanObject,
    mut v_self_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1988_: u8 = 0;
    let mut v_r_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1988_ = l_Lake_PathPatDescr_matches(v_path_1986_, v_self_1987_);
    v_r_1989_ = crate::leanh::lean_box((v_res_1988_) as usize);
    return v_r_1989_;
}
pub unsafe fn l_Lake_PathPat_path___lam__0(
    mut v___x_1994_: *mut crate::leanh::LeanObject,
    mut v___x_1995_: *mut crate::leanh::LeanObject,
    mut v_x_1996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1997_: u8 = 0;
    v___x_1997_ = l_Lake_PatternDescr_matches___redArg(v___x_1994_, v_x_1996_, v___x_1995_);
    return v___x_1997_;
}
pub unsafe fn l_Lake_PathPat_path___lam__0___boxed(
    mut v___x_1998_: *mut crate::leanh::LeanObject,
    mut v___x_1999_: *mut crate::leanh::LeanObject,
    mut v_x_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2001_: u8 = 0;
    let mut v_r_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Lake_PathPat_path___lam__0(v___x_1998_, v___x_1999_, v_x_2000_);
    v_r_2002_ = crate::leanh::lean_box((v_res_2001_) as usize);
    return v_r_2002_;
}
pub unsafe fn l_Lake_PathPat_path(
    mut v_p_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2005_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2005_, 0, v_p_2003_);
    v___x_2006_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2006_, 0, v___x_2005_);
    crate::leanh::lean_inc_ref(v___x_2006_);
    v___f_2007_ = crate::leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2007_, 0, v___x_2004_);
    crate::leanh::lean_closure_set(v___f_2007_, 1, v___x_2006_);
    v___x_2008_ = crate::leanh::lean_box(0);
    v___x_2009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2006_);
    v___x_2010_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2010_, 0, v___f_2007_);
    crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2008_);
    crate::leanh::lean_ctor_set(v___x_2010_, 2, v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn l_Lake_PathPat_extension(
    mut v_p_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2013_, 0, v_p_2011_);
    v___x_2014_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2014_, 0, v___x_2013_);
    crate::leanh::lean_inc_ref(v___x_2014_);
    v___f_2015_ = crate::leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2015_, 0, v___x_2012_);
    crate::leanh::lean_closure_set(v___f_2015_, 1, v___x_2014_);
    v___x_2016_ = crate::leanh::lean_box(0);
    v___x_2017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2014_);
    v___x_2018_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2018_, 0, v___f_2015_);
    crate::leanh::lean_ctor_set(v___x_2018_, 1, v___x_2016_);
    crate::leanh::lean_ctor_set(v___x_2018_, 2, v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lake_PathPat_fileName(
    mut v_p_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lake_instIsPatternPathPatDescrFilePath;
    v___x_2021_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2021_, 0, v_p_2019_);
    v___x_2022_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
    crate::leanh::lean_inc_ref(v___x_2022_);
    v___f_2023_ = crate::leanh::lean_alloc_closure(
        l_Lake_PathPat_path___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2023_, 0, v___x_2020_);
    crate::leanh::lean_closure_set(v___f_2023_, 1, v___x_2022_);
    v___x_2024_ = crate::leanh::lean_box(0);
    v___x_2025_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2022_);
    v___x_2026_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2026_, 0, v___f_2023_);
    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2026_, 2, v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_2027_: *mut crate::leanh::LeanObject,
    mut v_x_2028_: *mut crate::leanh::LeanObject,
    mut v_h__1_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = crate::leanh::lean_apply_2(v_h__1_2029_, v_x_2027_, v_x_2028_);
    return v___x_2030_;
}
pub unsafe fn l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_2031_: *mut crate::leanh::LeanObject,
    mut v_x_2032_: *mut crate::leanh::LeanObject,
    mut v_x_2033_: *mut crate::leanh::LeanObject,
    mut v_h__1_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = crate::leanh::lean_apply_2(v_h__1_2034_, v_x_2032_, v_x_2033_);
    return v___x_2035_;
}
pub unsafe fn l_Lake_isVerLike(mut v_s_2036_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    v___x_2037_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2038_ = lean_string_utf8_byte_size(v_s_2036_);
    v___x_2039_ = lean_nat_dec_le(v___x_2037_, v___x_2038_);
    if v___x_2039_ == 0 {
        return v___x_2039_;
    } else {
        let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: u32 = 0;
        let mut v___x_2042_: u32 = 0;
        let mut v___x_2043_: u8 = 0;
        v___x_2040_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2041_ = lean_string_utf8_get_fast(v_s_2036_, v___x_2040_);
        v___x_2042_ = 118;
        v___x_2043_ = lean_uint32_dec_eq(v___x_2041_, v___x_2042_);
        if v___x_2043_ == 0 {
            return v___x_2043_;
        } else {
            let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2045_: u32 = 0;
            let mut v___x_2046_: u32 = 0;
            let mut v___x_2047_: u8 = 0;
            v___x_2044_ = crate::leanh::lean_unsigned_to_nat(1);
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
    mut v_s_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: u8 = 0;
    let mut v_r_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lake_isVerLike(v_s_2050_);
    crate::leanh::lean_dec_ref(v_s_2050_);
    v_r_2052_ = crate::leanh::lean_box((v_res_2051_) as usize);
    return v_r_2052_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(
    mut v_k_2070_: *mut crate::leanh::LeanObject,
    mut v_v_2071_: *mut crate::leanh::LeanObject,
    mut v_t_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v_impl_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v_size_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v_unused_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut v_unused_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_unused_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v_k_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_unused_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v_size_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_unused_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v_unused_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut v_unused_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v_k_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_unused_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_unused_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2341_: u8 = 0;
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_unused_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2072_) == 0 {
                    v_size_2073_ = crate::leanh::lean_ctor_get(v_t_2072_, 0);
                    v_k_2074_ = crate::leanh::lean_ctor_get(v_t_2072_, 1);
                    v_v_2075_ = crate::leanh::lean_ctor_get(v_t_2072_, 2);
                    v_l_2076_ = crate::leanh::lean_ctor_get(v_t_2072_, 3);
                    v_r_2077_ = crate::leanh::lean_ctor_get(v_t_2072_, 4);
                    v_isSharedCheck_2357_ = (!crate::leanh::lean_is_exclusive(v_t_2072_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2079_ = v_t_2072_;
                        v_isShared_2080_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2077_);
                        crate::leanh::lean_inc(v_l_2076_);
                        crate::leanh::lean_inc(v_v_2075_);
                        crate::leanh::lean_inc(v_k_2074_);
                        crate::leanh::lean_inc(v_size_2073_);
                        crate::leanh::lean_dec(v_t_2072_);
                        v___x_2079_ = crate::leanh::lean_box(0);
                        v_isShared_2080_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2358_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2359_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2358_);
                    crate::leanh::lean_ctor_set(v___x_2359_, 1, v_k_2070_);
                    crate::leanh::lean_ctor_set(v___x_2359_, 2, v_v_2071_);
                    crate::leanh::lean_ctor_set(v___x_2359_, 3, v_t_2072_);
                    crate::leanh::lean_ctor_set(v___x_2359_, 4, v_t_2072_);
                    return v___x_2359_;
                }
            }
            1 => {
                v___x_2081_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2070_, v_k_2074_);
                match v___x_2081_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2073_);
                        v_impl_2082_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_2070_, v_v_2071_, v_l_2076_);
                        v___x_2083_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_2077_) == 0 {
                            v_size_2084_ = crate::leanh::lean_ctor_get(v_r_2077_, 0);
                            v_size_2085_ = crate::leanh::lean_ctor_get(v_impl_2082_, 0);
                            crate::leanh::lean_inc(v_size_2085_);
                            v_k_2086_ = crate::leanh::lean_ctor_get(v_impl_2082_, 1);
                            crate::leanh::lean_inc(v_k_2086_);
                            v_v_2087_ = crate::leanh::lean_ctor_get(v_impl_2082_, 2);
                            crate::leanh::lean_inc(v_v_2087_);
                            v_l_2088_ = crate::leanh::lean_ctor_get(v_impl_2082_, 3);
                            crate::leanh::lean_inc(v_l_2088_);
                            v_r_2089_ = crate::leanh::lean_ctor_get(v_impl_2082_, 4);
                            crate::leanh::lean_inc(v_r_2089_);
                            v___x_2090_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2091_ = lean_nat_mul(v___x_2090_, v_size_2084_);
                            v___x_2092_ = lean_nat_dec_lt(v___x_2091_, v_size_2085_);
                            crate::leanh::lean_dec(v___x_2091_);
                            if v___x_2092_ == 0 {
                                crate::leanh::lean_dec(v_r_2089_);
                                crate::leanh::lean_dec(v_l_2088_);
                                crate::leanh::lean_dec(v_v_2087_);
                                crate::leanh::lean_dec(v_k_2086_);
                                v___x_2093_ = lean_nat_add(v___x_2083_, v_size_2085_);
                                crate::leanh::lean_dec(v_size_2085_);
                                v___x_2094_ = lean_nat_add(v___x_2093_, v_size_2084_);
                                crate::leanh::lean_dec(v___x_2093_);
                                if v_isShared_2080_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v_impl_2082_);
                                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2094_);
                                    v___x_2096_ = v___x_2079_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2097_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        0,
                                        v___x_2094_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        1,
                                        v_k_2074_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        2,
                                        v_v_2075_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2097_,
                                        3,
                                        v_impl_2082_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                if v_isSharedCheck_2163_ == 0 {
                                    v_unused_2164_ = crate::leanh::lean_ctor_get(v_impl_2082_, 4);
                                    crate::leanh::lean_dec(v_unused_2164_);
                                    v_unused_2165_ = crate::leanh::lean_ctor_get(v_impl_2082_, 3);
                                    crate::leanh::lean_dec(v_unused_2165_);
                                    v_unused_2166_ = crate::leanh::lean_ctor_get(v_impl_2082_, 2);
                                    crate::leanh::lean_dec(v_unused_2166_);
                                    v_unused_2167_ = crate::leanh::lean_ctor_get(v_impl_2082_, 1);
                                    crate::leanh::lean_dec(v_unused_2167_);
                                    v_unused_2168_ = crate::leanh::lean_ctor_get(v_impl_2082_, 0);
                                    crate::leanh::lean_dec(v_unused_2168_);
                                    v___x_2099_ = v_impl_2082_;
                                    v_isShared_2100_ = v_isSharedCheck_2163_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2082_);
                                    v___x_2099_ = crate::leanh::lean_box(0);
                                    v_isShared_2100_ = v_isSharedCheck_2163_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2169_ = crate::leanh::lean_ctor_get(v_impl_2082_, 3);
                            crate::leanh::lean_inc(v_l_2169_);
                            if crate::leanh::lean_obj_tag(v_l_2169_) == 0 {
                                v_r_2170_ = crate::leanh::lean_ctor_get(v_impl_2082_, 4);
                                v_k_2171_ = crate::leanh::lean_ctor_get(v_impl_2082_, 1);
                                v_v_2172_ = crate::leanh::lean_ctor_get(v_impl_2082_, 2);
                                v_isSharedCheck_2183_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                if v_isSharedCheck_2183_ == 0 {
                                    v_unused_2184_ = crate::leanh::lean_ctor_get(v_impl_2082_, 3);
                                    crate::leanh::lean_dec(v_unused_2184_);
                                    v_unused_2185_ = crate::leanh::lean_ctor_get(v_impl_2082_, 0);
                                    crate::leanh::lean_dec(v_unused_2185_);
                                    v___x_2174_ = v_impl_2082_;
                                    v_isShared_2175_ = v_isSharedCheck_2183_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2170_);
                                    crate::leanh::lean_inc(v_v_2172_);
                                    crate::leanh::lean_inc(v_k_2171_);
                                    crate::leanh::lean_dec(v_impl_2082_);
                                    v___x_2174_ = crate::leanh::lean_box(0);
                                    v_isShared_2175_ = v_isSharedCheck_2183_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2186_ = crate::leanh::lean_ctor_get(v_impl_2082_, 4);
                                crate::leanh::lean_inc(v_r_2186_);
                                if crate::leanh::lean_obj_tag(v_r_2186_) == 0 {
                                    v_k_2187_ = crate::leanh::lean_ctor_get(v_impl_2082_, 1);
                                    v_v_2188_ = crate::leanh::lean_ctor_get(v_impl_2082_, 2);
                                    v_isSharedCheck_2211_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2082_)) as u8;
                                    if v_isSharedCheck_2211_ == 0 {
                                        v_unused_2212_ =
                                            crate::leanh::lean_ctor_get(v_impl_2082_, 4);
                                        crate::leanh::lean_dec(v_unused_2212_);
                                        v_unused_2213_ =
                                            crate::leanh::lean_ctor_get(v_impl_2082_, 3);
                                        crate::leanh::lean_dec(v_unused_2213_);
                                        v_unused_2214_ =
                                            crate::leanh::lean_ctor_get(v_impl_2082_, 0);
                                        crate::leanh::lean_dec(v_unused_2214_);
                                        v___x_2190_ = v_impl_2082_;
                                        v_isShared_2191_ = v_isSharedCheck_2211_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2188_);
                                        crate::leanh::lean_inc(v_k_2187_);
                                        crate::leanh::lean_dec(v_impl_2082_);
                                        v___x_2190_ = crate::leanh::lean_box(0);
                                        v_isShared_2191_ = v_isSharedCheck_2211_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2215_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2080_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2079_, 4, v_r_2186_);
                                        crate::leanh::lean_ctor_set(v___x_2079_, 3, v_impl_2082_);
                                        crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2215_);
                                        v___x_2217_ = v___x_2079_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2218_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            0,
                                            v___x_2215_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            1,
                                            v_k_2074_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            2,
                                            v_v_2075_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2218_,
                                            3,
                                            v_impl_2082_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_2075_);
                        crate::leanh::lean_dec(v_k_2074_);
                        if v_isShared_2080_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2071_);
                            crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2070_);
                            v___x_2220_ = v___x_2079_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2221_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_size_2073_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2070_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2071_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_l_2076_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_r_2077_);
                            v___x_2220_ = v_reuseFailAlloc_2221_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2073_);
                        v_impl_2222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_2070_, v_v_2071_, v_r_2077_);
                        v___x_2223_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_2076_) == 0 {
                            v_size_2224_ = crate::leanh::lean_ctor_get(v_l_2076_, 0);
                            v_size_2225_ = crate::leanh::lean_ctor_get(v_impl_2222_, 0);
                            crate::leanh::lean_inc(v_size_2225_);
                            v_k_2226_ = crate::leanh::lean_ctor_get(v_impl_2222_, 1);
                            crate::leanh::lean_inc(v_k_2226_);
                            v_v_2227_ = crate::leanh::lean_ctor_get(v_impl_2222_, 2);
                            crate::leanh::lean_inc(v_v_2227_);
                            v_l_2228_ = crate::leanh::lean_ctor_get(v_impl_2222_, 3);
                            crate::leanh::lean_inc(v_l_2228_);
                            v_r_2229_ = crate::leanh::lean_ctor_get(v_impl_2222_, 4);
                            crate::leanh::lean_inc(v_r_2229_);
                            v___x_2230_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2231_ = lean_nat_mul(v___x_2230_, v_size_2224_);
                            v___x_2232_ = lean_nat_dec_lt(v___x_2231_, v_size_2225_);
                            crate::leanh::lean_dec(v___x_2231_);
                            if v___x_2232_ == 0 {
                                crate::leanh::lean_dec(v_r_2229_);
                                crate::leanh::lean_dec(v_l_2228_);
                                crate::leanh::lean_dec(v_v_2227_);
                                crate::leanh::lean_dec(v_k_2226_);
                                v___x_2233_ = lean_nat_add(v___x_2223_, v_size_2224_);
                                v___x_2234_ = lean_nat_add(v___x_2233_, v_size_2225_);
                                crate::leanh::lean_dec(v_size_2225_);
                                crate::leanh::lean_dec(v___x_2233_);
                                if v_isShared_2080_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v_impl_2222_);
                                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2234_);
                                    v___x_2236_ = v___x_2079_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2237_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        0,
                                        v___x_2234_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        1,
                                        v_k_2074_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        2,
                                        v_v_2075_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2237_,
                                        3,
                                        v_l_2076_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                if v_isSharedCheck_2301_ == 0 {
                                    v_unused_2302_ = crate::leanh::lean_ctor_get(v_impl_2222_, 4);
                                    crate::leanh::lean_dec(v_unused_2302_);
                                    v_unused_2303_ = crate::leanh::lean_ctor_get(v_impl_2222_, 3);
                                    crate::leanh::lean_dec(v_unused_2303_);
                                    v_unused_2304_ = crate::leanh::lean_ctor_get(v_impl_2222_, 2);
                                    crate::leanh::lean_dec(v_unused_2304_);
                                    v_unused_2305_ = crate::leanh::lean_ctor_get(v_impl_2222_, 1);
                                    crate::leanh::lean_dec(v_unused_2305_);
                                    v_unused_2306_ = crate::leanh::lean_ctor_get(v_impl_2222_, 0);
                                    crate::leanh::lean_dec(v_unused_2306_);
                                    v___x_2239_ = v_impl_2222_;
                                    v_isShared_2240_ = v_isSharedCheck_2301_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2222_);
                                    v___x_2239_ = crate::leanh::lean_box(0);
                                    v_isShared_2240_ = v_isSharedCheck_2301_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2307_ = crate::leanh::lean_ctor_get(v_impl_2222_, 3);
                            crate::leanh::lean_inc(v_l_2307_);
                            if crate::leanh::lean_obj_tag(v_l_2307_) == 0 {
                                v_r_2308_ = crate::leanh::lean_ctor_get(v_impl_2222_, 4);
                                v_k_2309_ = crate::leanh::lean_ctor_get(v_impl_2222_, 1);
                                v_v_2310_ = crate::leanh::lean_ctor_get(v_impl_2222_, 2);
                                v_isSharedCheck_2333_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                if v_isSharedCheck_2333_ == 0 {
                                    v_unused_2334_ = crate::leanh::lean_ctor_get(v_impl_2222_, 3);
                                    crate::leanh::lean_dec(v_unused_2334_);
                                    v_unused_2335_ = crate::leanh::lean_ctor_get(v_impl_2222_, 0);
                                    crate::leanh::lean_dec(v_unused_2335_);
                                    v___x_2312_ = v_impl_2222_;
                                    v_isShared_2313_ = v_isSharedCheck_2333_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2308_);
                                    crate::leanh::lean_inc(v_v_2310_);
                                    crate::leanh::lean_inc(v_k_2309_);
                                    crate::leanh::lean_dec(v_impl_2222_);
                                    v___x_2312_ = crate::leanh::lean_box(0);
                                    v_isShared_2313_ = v_isSharedCheck_2333_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_2336_ = crate::leanh::lean_ctor_get(v_impl_2222_, 4);
                                crate::leanh::lean_inc(v_r_2336_);
                                if crate::leanh::lean_obj_tag(v_r_2336_) == 0 {
                                    v_k_2337_ = crate::leanh::lean_ctor_get(v_impl_2222_, 1);
                                    v_v_2338_ = crate::leanh::lean_ctor_get(v_impl_2222_, 2);
                                    v_isSharedCheck_2349_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2222_)) as u8;
                                    if v_isSharedCheck_2349_ == 0 {
                                        v_unused_2350_ =
                                            crate::leanh::lean_ctor_get(v_impl_2222_, 4);
                                        crate::leanh::lean_dec(v_unused_2350_);
                                        v_unused_2351_ =
                                            crate::leanh::lean_ctor_get(v_impl_2222_, 3);
                                        crate::leanh::lean_dec(v_unused_2351_);
                                        v_unused_2352_ =
                                            crate::leanh::lean_ctor_get(v_impl_2222_, 0);
                                        crate::leanh::lean_dec(v_unused_2352_);
                                        v___x_2340_ = v_impl_2222_;
                                        v_isShared_2341_ = v_isSharedCheck_2349_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2338_);
                                        crate::leanh::lean_inc(v_k_2337_);
                                        crate::leanh::lean_dec(v_impl_2222_);
                                        v___x_2340_ = crate::leanh::lean_box(0);
                                        v_isShared_2341_ = v_isSharedCheck_2349_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_2353_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2080_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2079_, 4, v_impl_2222_);
                                        crate::leanh::lean_ctor_set(v___x_2079_, 3, v_r_2336_);
                                        crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2353_);
                                        v___x_2355_ = v___x_2079_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2356_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            0,
                                            v___x_2353_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            1,
                                            v_k_2074_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            2,
                                            v_v_2075_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2356_,
                                            3,
                                            v_r_2336_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                v_size_2101_ = crate::leanh::lean_ctor_get(v_l_2088_, 0);
                v_size_2102_ = crate::leanh::lean_ctor_get(v_r_2089_, 0);
                v_k_2103_ = crate::leanh::lean_ctor_get(v_r_2089_, 1);
                v_v_2104_ = crate::leanh::lean_ctor_get(v_r_2089_, 2);
                v_l_2105_ = crate::leanh::lean_ctor_get(v_r_2089_, 3);
                v_r_2106_ = crate::leanh::lean_ctor_get(v_r_2089_, 4);
                v___x_2107_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2108_ = lean_nat_mul(v___x_2107_, v_size_2101_);
                v___x_2109_ = lean_nat_dec_lt(v_size_2102_, v___x_2108_);
                crate::leanh::lean_dec(v___x_2108_);
                if v___x_2109_ == 0 {
                    crate::leanh::lean_inc(v_r_2106_);
                    crate::leanh::lean_inc(v_l_2105_);
                    crate::leanh::lean_inc(v_v_2104_);
                    crate::leanh::lean_inc(v_k_2103_);
                    v_isSharedCheck_2138_ = (!crate::leanh::lean_is_exclusive(v_r_2089_)) as u8;
                    if v_isSharedCheck_2138_ == 0 {
                        v_unused_2139_ = crate::leanh::lean_ctor_get(v_r_2089_, 4);
                        crate::leanh::lean_dec(v_unused_2139_);
                        v_unused_2140_ = crate::leanh::lean_ctor_get(v_r_2089_, 3);
                        crate::leanh::lean_dec(v_unused_2140_);
                        v_unused_2141_ = crate::leanh::lean_ctor_get(v_r_2089_, 2);
                        crate::leanh::lean_dec(v_unused_2141_);
                        v_unused_2142_ = crate::leanh::lean_ctor_get(v_r_2089_, 1);
                        crate::leanh::lean_dec(v_unused_2142_);
                        v_unused_2143_ = crate::leanh::lean_ctor_get(v_r_2089_, 0);
                        crate::leanh::lean_dec(v_unused_2143_);
                        v___x_2111_ = v_r_2089_;
                        v_isShared_2112_ = v_isSharedCheck_2138_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2089_);
                        v___x_2111_ = crate::leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2138_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2079_);
                    v___x_2144_ = lean_nat_add(v___x_2083_, v_size_2085_);
                    crate::leanh::lean_dec(v_size_2085_);
                    v___x_2145_ = lean_nat_add(v___x_2144_, v_size_2084_);
                    crate::leanh::lean_dec(v___x_2144_);
                    v___x_2146_ = lean_nat_add(v___x_2083_, v_size_2084_);
                    v___x_2147_ = lean_nat_add(v___x_2146_, v_size_2102_);
                    crate::leanh::lean_dec(v___x_2146_);
                    crate::leanh::lean_inc_ref(v_r_2077_);
                    if v_isShared_2100_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2099_, 4, v_r_2077_);
                        crate::leanh::lean_ctor_set(v___x_2099_, 3, v_r_2089_);
                        crate::leanh::lean_ctor_set(v___x_2099_, 2, v_v_2075_);
                        crate::leanh::lean_ctor_set(v___x_2099_, 1, v_k_2074_);
                        crate::leanh::lean_ctor_set(v___x_2099_, 0, v___x_2147_);
                        v___x_2149_ = v___x_2099_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2162_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2147_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_k_2074_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_v_2075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_r_2089_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_r_2077_);
                        v___x_2149_ = v_reuseFailAlloc_2162_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2113_ = lean_nat_add(v___x_2083_, v_size_2085_);
                crate::leanh::lean_dec(v_size_2085_);
                v___x_2114_ = lean_nat_add(v___x_2113_, v_size_2084_);
                crate::leanh::lean_dec(v___x_2113_);
                v___x_2126_ = lean_nat_add(v___x_2083_, v_size_2101_);
                if crate::leanh::lean_obj_tag(v_l_2105_) == 0 {
                    v_size_2136_ = crate::leanh::lean_ctor_get(v_l_2105_, 0);
                    crate::leanh::lean_inc(v_size_2136_);
                    v___y_2128_ = v_size_2136_;
                    state = 8;
                    continue;
                } else {
                    v___x_2137_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2128_ = v___x_2137_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2119_ = lean_nat_add(v___y_2116_, v___y_2118_);
                crate::leanh::lean_dec(v___y_2118_);
                crate::leanh::lean_dec(v___y_2116_);
                if v_isShared_2112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2111_, 4, v_r_2077_);
                    crate::leanh::lean_ctor_set(v___x_2111_, 3, v_r_2106_);
                    crate::leanh::lean_ctor_set(v___x_2111_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v___x_2111_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2119_);
                    v___x_2121_ = v___x_2111_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_r_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_r_2077_);
                    v___x_2121_ = v_reuseFailAlloc_2125_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2100_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2099_, 4, v___x_2121_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 3, v___y_2117_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 2, v_v_2104_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 1, v_k_2103_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 0, v___x_2114_);
                    v___x_2123_ = v___x_2099_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_2103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 3, v___y_2117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 4, v___x_2121_);
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
                crate::leanh::lean_dec(v___y_2128_);
                crate::leanh::lean_dec(v___x_2126_);
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v_l_2105_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v_l_2088_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2087_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2086_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2079_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_2087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_l_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_l_2105_);
                    v___x_2131_ = v_reuseFailAlloc_2135_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2132_ = lean_nat_add(v___x_2083_, v_size_2084_);
                if crate::leanh::lean_obj_tag(v_r_2106_) == 0 {
                    v_size_2133_ = crate::leanh::lean_ctor_get(v_r_2106_, 0);
                    crate::leanh::lean_inc(v_size_2133_);
                    v___y_2116_ = v___x_2132_;
                    v___y_2117_ = v___x_2131_;
                    v___y_2118_ = v_size_2133_;
                    state = 5;
                    continue;
                } else {
                    v___x_2134_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2116_ = v___x_2132_;
                    v___y_2117_ = v___x_2131_;
                    v___y_2118_ = v___x_2134_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2156_ = (!crate::leanh::lean_is_exclusive(v_r_2077_)) as u8;
                if v_isSharedCheck_2156_ == 0 {
                    v_unused_2157_ = crate::leanh::lean_ctor_get(v_r_2077_, 4);
                    crate::leanh::lean_dec(v_unused_2157_);
                    v_unused_2158_ = crate::leanh::lean_ctor_get(v_r_2077_, 3);
                    crate::leanh::lean_dec(v_unused_2158_);
                    v_unused_2159_ = crate::leanh::lean_ctor_get(v_r_2077_, 2);
                    crate::leanh::lean_dec(v_unused_2159_);
                    v_unused_2160_ = crate::leanh::lean_ctor_get(v_r_2077_, 1);
                    crate::leanh::lean_dec(v_unused_2160_);
                    v_unused_2161_ = crate::leanh::lean_ctor_get(v_r_2077_, 0);
                    crate::leanh::lean_dec(v_unused_2161_);
                    v___x_2151_ = v_r_2077_;
                    v_isShared_2152_ = v_isSharedCheck_2156_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2077_);
                    v___x_2151_ = crate::leanh::lean_box(0);
                    v_isShared_2152_ = v_isSharedCheck_2156_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2151_, 4, v___x_2149_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 3, v_l_2088_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 2, v_v_2087_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 1, v_k_2086_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2145_);
                    v___x_2154_ = v___x_2151_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_l_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2154_;
            }
            13 => {
                v___x_2176_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_2170_);
                if v_isShared_2175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2174_, 3, v_r_2170_);
                    crate::leanh::lean_ctor_set(v___x_2174_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v___x_2174_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2083_);
                    v___x_2178_ = v___x_2174_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2182_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_r_2170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_r_2170_);
                    v___x_2178_ = v_reuseFailAlloc_2182_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v___x_2178_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v_l_2169_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2172_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2171_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2176_);
                    v___x_2180_ = v___x_2079_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_l_2169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 4, v___x_2178_);
                    v___x_2180_ = v_reuseFailAlloc_2181_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2180_;
            }
            16 => {
                v_k_2192_ = crate::leanh::lean_ctor_get(v_r_2186_, 1);
                v_v_2193_ = crate::leanh::lean_ctor_get(v_r_2186_, 2);
                v_isSharedCheck_2207_ = (!crate::leanh::lean_is_exclusive(v_r_2186_)) as u8;
                if v_isSharedCheck_2207_ == 0 {
                    v_unused_2208_ = crate::leanh::lean_ctor_get(v_r_2186_, 4);
                    crate::leanh::lean_dec(v_unused_2208_);
                    v_unused_2209_ = crate::leanh::lean_ctor_get(v_r_2186_, 3);
                    crate::leanh::lean_dec(v_unused_2209_);
                    v_unused_2210_ = crate::leanh::lean_ctor_get(v_r_2186_, 0);
                    crate::leanh::lean_dec(v_unused_2210_);
                    v___x_2195_ = v_r_2186_;
                    v_isShared_2196_ = v_isSharedCheck_2207_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2193_);
                    crate::leanh::lean_inc(v_k_2192_);
                    crate::leanh::lean_dec(v_r_2186_);
                    v___x_2195_ = crate::leanh::lean_box(0);
                    v_isShared_2196_ = v_isSharedCheck_2207_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2197_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2195_, 4, v_l_2169_);
                    crate::leanh::lean_ctor_set(v___x_2195_, 3, v_l_2169_);
                    crate::leanh::lean_ctor_set(v___x_2195_, 2, v_v_2188_);
                    crate::leanh::lean_ctor_set(v___x_2195_, 1, v_k_2187_);
                    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2083_);
                    v___x_2199_ = v___x_2195_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_l_2169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_l_2169_);
                    v___x_2199_ = v_reuseFailAlloc_2206_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2190_, 4, v_l_2169_);
                    crate::leanh::lean_ctor_set(v___x_2190_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v___x_2190_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2083_);
                    v___x_2201_ = v___x_2190_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2205_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_l_2169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_l_2169_);
                    v___x_2201_ = v_reuseFailAlloc_2205_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v___x_2201_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v___x_2199_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2193_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2192_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2197_);
                    v___x_2203_ = v___x_2079_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_k_2192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_v_2193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 3, v___x_2199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 4, v___x_2201_);
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
                v_size_2241_ = crate::leanh::lean_ctor_get(v_l_2228_, 0);
                v_k_2242_ = crate::leanh::lean_ctor_get(v_l_2228_, 1);
                v_v_2243_ = crate::leanh::lean_ctor_get(v_l_2228_, 2);
                v_l_2244_ = crate::leanh::lean_ctor_get(v_l_2228_, 3);
                v_r_2245_ = crate::leanh::lean_ctor_get(v_l_2228_, 4);
                v_size_2246_ = crate::leanh::lean_ctor_get(v_r_2229_, 0);
                v___x_2247_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2248_ = lean_nat_mul(v___x_2247_, v_size_2246_);
                v___x_2249_ = lean_nat_dec_lt(v_size_2241_, v___x_2248_);
                crate::leanh::lean_dec(v___x_2248_);
                if v___x_2249_ == 0 {
                    crate::leanh::lean_inc(v_r_2245_);
                    crate::leanh::lean_inc(v_l_2244_);
                    crate::leanh::lean_inc(v_v_2243_);
                    crate::leanh::lean_inc(v_k_2242_);
                    v_isSharedCheck_2277_ = (!crate::leanh::lean_is_exclusive(v_l_2228_)) as u8;
                    if v_isSharedCheck_2277_ == 0 {
                        v_unused_2278_ = crate::leanh::lean_ctor_get(v_l_2228_, 4);
                        crate::leanh::lean_dec(v_unused_2278_);
                        v_unused_2279_ = crate::leanh::lean_ctor_get(v_l_2228_, 3);
                        crate::leanh::lean_dec(v_unused_2279_);
                        v_unused_2280_ = crate::leanh::lean_ctor_get(v_l_2228_, 2);
                        crate::leanh::lean_dec(v_unused_2280_);
                        v_unused_2281_ = crate::leanh::lean_ctor_get(v_l_2228_, 1);
                        crate::leanh::lean_dec(v_unused_2281_);
                        v_unused_2282_ = crate::leanh::lean_ctor_get(v_l_2228_, 0);
                        crate::leanh::lean_dec(v_unused_2282_);
                        v___x_2251_ = v_l_2228_;
                        v_isShared_2252_ = v_isSharedCheck_2277_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2228_);
                        v___x_2251_ = crate::leanh::lean_box(0);
                        v_isShared_2252_ = v_isSharedCheck_2277_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2079_);
                    v___x_2283_ = lean_nat_add(v___x_2223_, v_size_2224_);
                    v___x_2284_ = lean_nat_add(v___x_2283_, v_size_2225_);
                    crate::leanh::lean_dec(v_size_2225_);
                    v___x_2285_ = lean_nat_add(v___x_2283_, v_size_2241_);
                    crate::leanh::lean_dec(v___x_2283_);
                    crate::leanh::lean_inc_ref(v_l_2076_);
                    if v_isShared_2240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2239_, 4, v_l_2228_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 3, v_l_2076_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 2, v_v_2075_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 1, v_k_2074_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2285_);
                        v___x_2287_ = v___x_2239_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2300_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2285_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2074_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2075_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_2076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_l_2228_);
                        v___x_2287_ = v_reuseFailAlloc_2300_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2253_ = lean_nat_add(v___x_2223_, v_size_2224_);
                v___x_2254_ = lean_nat_add(v___x_2253_, v_size_2225_);
                crate::leanh::lean_dec(v_size_2225_);
                if crate::leanh::lean_obj_tag(v_l_2244_) == 0 {
                    v_size_2275_ = crate::leanh::lean_ctor_get(v_l_2244_, 0);
                    crate::leanh::lean_inc(v_size_2275_);
                    v___y_2267_ = v_size_2275_;
                    state = 29;
                    continue;
                } else {
                    v___x_2276_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2267_ = v___x_2276_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2259_ = lean_nat_add(v___y_2257_, v___y_2258_);
                crate::leanh::lean_dec(v___y_2258_);
                crate::leanh::lean_dec(v___y_2257_);
                if v_isShared_2252_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2251_, 4, v_r_2229_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 3, v_r_2245_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 2, v_v_2227_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 1, v_k_2226_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2259_);
                    v___x_2261_ = v___x_2251_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_r_2245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_r_2229_);
                    v___x_2261_ = v_reuseFailAlloc_2265_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2239_, 4, v___x_2261_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 3, v___y_2256_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 2, v_v_2243_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 1, v_k_2242_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2254_);
                    v___x_2263_ = v___x_2239_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_k_2242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_v_2243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 3, v___y_2256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 4, v___x_2261_);
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
                crate::leanh::lean_dec(v___y_2267_);
                crate::leanh::lean_dec(v___x_2253_);
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v_l_2244_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2268_);
                    v___x_2270_ = v___x_2079_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_l_2076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_l_2244_);
                    v___x_2270_ = v_reuseFailAlloc_2274_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2271_ = lean_nat_add(v___x_2223_, v_size_2246_);
                if crate::leanh::lean_obj_tag(v_r_2245_) == 0 {
                    v_size_2272_ = crate::leanh::lean_ctor_get(v_r_2245_, 0);
                    crate::leanh::lean_inc(v_size_2272_);
                    v___y_2256_ = v___x_2270_;
                    v___y_2257_ = v___x_2271_;
                    v___y_2258_ = v_size_2272_;
                    state = 26;
                    continue;
                } else {
                    v___x_2273_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2256_ = v___x_2270_;
                    v___y_2257_ = v___x_2271_;
                    v___y_2258_ = v___x_2273_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2294_ = (!crate::leanh::lean_is_exclusive(v_l_2076_)) as u8;
                if v_isSharedCheck_2294_ == 0 {
                    v_unused_2295_ = crate::leanh::lean_ctor_get(v_l_2076_, 4);
                    crate::leanh::lean_dec(v_unused_2295_);
                    v_unused_2296_ = crate::leanh::lean_ctor_get(v_l_2076_, 3);
                    crate::leanh::lean_dec(v_unused_2296_);
                    v_unused_2297_ = crate::leanh::lean_ctor_get(v_l_2076_, 2);
                    crate::leanh::lean_dec(v_unused_2297_);
                    v_unused_2298_ = crate::leanh::lean_ctor_get(v_l_2076_, 1);
                    crate::leanh::lean_dec(v_unused_2298_);
                    v_unused_2299_ = crate::leanh::lean_ctor_get(v_l_2076_, 0);
                    crate::leanh::lean_dec(v_unused_2299_);
                    v___x_2289_ = v_l_2076_;
                    v_isShared_2290_ = v_isSharedCheck_2294_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2076_);
                    v___x_2289_ = crate::leanh::lean_box(0);
                    v_isShared_2290_ = v_isSharedCheck_2294_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 4, v_r_2229_);
                    crate::leanh::lean_ctor_set(v___x_2289_, 3, v___x_2287_);
                    crate::leanh::lean_ctor_set(v___x_2289_, 2, v_v_2227_);
                    crate::leanh::lean_ctor_set(v___x_2289_, 1, v_k_2226_);
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2284_);
                    v___x_2292_ = v___x_2289_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_2226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_2227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 3, v___x_2287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_r_2229_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2292_;
            }
            34 => {
                v_k_2314_ = crate::leanh::lean_ctor_get(v_l_2307_, 1);
                v_v_2315_ = crate::leanh::lean_ctor_get(v_l_2307_, 2);
                v_isSharedCheck_2329_ = (!crate::leanh::lean_is_exclusive(v_l_2307_)) as u8;
                if v_isSharedCheck_2329_ == 0 {
                    v_unused_2330_ = crate::leanh::lean_ctor_get(v_l_2307_, 4);
                    crate::leanh::lean_dec(v_unused_2330_);
                    v_unused_2331_ = crate::leanh::lean_ctor_get(v_l_2307_, 3);
                    crate::leanh::lean_dec(v_unused_2331_);
                    v_unused_2332_ = crate::leanh::lean_ctor_get(v_l_2307_, 0);
                    crate::leanh::lean_dec(v_unused_2332_);
                    v___x_2317_ = v_l_2307_;
                    v_isShared_2318_ = v_isSharedCheck_2329_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2315_);
                    crate::leanh::lean_inc(v_k_2314_);
                    crate::leanh::lean_dec(v_l_2307_);
                    v___x_2317_ = crate::leanh::lean_box(0);
                    v_isShared_2318_ = v_isSharedCheck_2329_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2319_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_2308_, 2);
                if v_isShared_2318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2317_, 4, v_r_2308_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 3, v_r_2308_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2223_);
                    v___x_2321_ = v___x_2317_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_r_2308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_r_2308_);
                    v___x_2321_ = v_reuseFailAlloc_2328_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_2308_);
                if v_isShared_2313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2312_, 3, v_r_2308_);
                    crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2223_);
                    v___x_2323_ = v___x_2312_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_r_2308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_r_2308_);
                    v___x_2323_ = v_reuseFailAlloc_2327_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v___x_2323_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v___x_2321_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2315_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2314_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2319_);
                    v___x_2325_ = v___x_2079_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_k_2314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_v_2315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 3, v___x_2321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 4, v___x_2323_);
                    v___x_2325_ = v_reuseFailAlloc_2326_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2325_;
            }
            39 => {
                v___x_2342_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2340_, 4, v_l_2307_);
                    crate::leanh::lean_ctor_set(v___x_2340_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v___x_2340_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v___x_2340_, 0, v___x_2223_);
                    v___x_2344_ = v___x_2340_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_l_2307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_l_2307_);
                    v___x_2344_ = v_reuseFailAlloc_2348_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2079_, 4, v_r_2336_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 3, v___x_2344_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 2, v_v_2338_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v_k_2337_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2342_);
                    v___x_2346_ = v___x_2079_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 3, v___x_2344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2336_);
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
pub unsafe fn _init_l_Lake_versionTagPresets___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = crate::leanh::lean_box(1);
    v___x_2361_ = l_Lake_StrPat_verLike;
    v___x_2362_ = l_Lake_StrPat_verLike___closed__2;
    v___x_2363_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v___x_2362_,
        v___x_2361_,
        v___x_2360_,
    );
    return v___x_2363_;
}
pub unsafe fn _init_l_Lake_versionTagPresets___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lake_versionTagPresets() -> *mut crate::leanh::LeanObject {
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__1),
        core::ptr::addr_of_mut!(l_Lake_versionTagPresets___closed__1_once),
        _init_l_Lake_versionTagPresets___closed__1,
    );
    return v___x_2368_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(
    mut v_00_u03b2_2369_: *mut crate::leanh::LeanObject,
    mut v_k_2370_: *mut crate::leanh::LeanObject,
    mut v_v_2371_: *mut crate::leanh::LeanObject,
    mut v_t_2372_: *mut crate::leanh::LeanObject,
    mut v_hl_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(
            v_k_2370_, v_v_2371_, v_t_2372_,
        );
    return v___x_2374_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Pattern(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedPathPatDescr_default = _init_l_Lake_instInhabitedPathPatDescr_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPathPatDescr_default);
    l_Lake_instInhabitedPathPatDescr = _init_l_Lake_instInhabitedPathPatDescr();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPathPatDescr);
    l_Lake_versionTagPresets = _init_l_Lake_versionTagPresets();
    crate::leanh::lean_mark_persistent(l_Lake_versionTagPresets);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Pattern(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Pattern(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Pattern(builtin);
}

// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: Lake.Config.Lang Lake.Config.Package Lean.PrettyPrinter Lake.CLI.Translate.Toml Lake.CLI.Translate.Lean Lake.Load.Lean.Elab
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_io_get_num_heartbeats, lean_mk_empty_array_with_capacity, lean_nat_add, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Prelude::{l_Lean_firstFrontendMacroScope, lean_erase_macro_scopes};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lake::CLI::Translate::Lean::{
    initialize_Lake_CLI_Translate_Lean, l_Lake_Package_mkLeanConfig,
    runtime_initialize_Lake_CLI_Translate_Lean,
};
use crate::r#gen::Lake::CLI::Translate::Toml::{
    initialize_Lake_CLI_Translate_Toml, l_Lake_Package_mkTomlConfig,
    runtime_initialize_Lake_CLI_Translate_Toml,
};
use crate::r#gen::Lake::Config::Lang::{
    initialize_Lake_Config_Lang, runtime_initialize_Lake_Config_Lang,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Load::Lean::Elab::{
    initialize_Lake_Load_Lean_Elab, l_Lake_importModulesUsingCache,
    runtime_initialize_Lake_Load_Lean_Elab,
};
use crate::r#gen::Lake::Toml::Data::Dict::l_Lake_Toml_RBDict_empty;
use crate::r#gen::Lake::Toml::Data::Value::l_Lake_Toml_ppTable;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_getMaxHeartbeats, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_toString;
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, l_Lean_PrettyPrinter_ppModule,
    runtime_initialize_Lean_PrettyPrinter,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l_Lean_inheritedTraceOptions;
pub static l_Lake_Package_mkConfigString___closed__0_value: crate::leanh::LeanStringObject<55> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 55,
        m_capacity: 55,
        m_length: 54,
        m_data: [
            40, 105, 110, 116, 101, 114, 110, 97, 108, 41, 32, 102, 97, 105, 108, 101, 100, 32,
            116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 32, 76, 101,
            97, 110, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 58, 32, 0,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__1_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_Package_mkConfigString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__2_value)
                as *mut crate::leanh::LeanObject,
            256 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__4_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [
            core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_mkConfigString___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_mkConfigString___closed__12_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [95, 117, 110, 105, 113, 0],
    };
static mut l_Lake_Package_mkConfigString___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__12_value)
                as *mut crate::leanh::LeanObject,
            3978731030111751661 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__13_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_mkConfigString___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_mkConfigString___closed__18_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_mkConfigString___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__19_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lake_Package_mkConfigString___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_mkConfigString___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_mkConfigString___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__21: u8 = 0;
static mut l_Lake_Package_mkConfigString___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_mkConfigString___closed__23_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [10, 0],
    };
static mut l_Lake_Package_mkConfigString___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__24_value: crate::leanh::LeanStringObject<21> =
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
            105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110,
            32, 35, 0,
        ],
    };
static mut l_Lake_Package_mkConfigString___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_mkConfigString___closed__25_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_mkConfigString___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_mkConfigString___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_mkConfigString___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_mkConfigString___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(
    mut v_sz_270_: usize,
    mut v_i_271_: usize,
    mut v_bs_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_273_: u8 = 0;
    let mut v_v_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: usize = 0;
    let mut v___x_279_: usize = 0;
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_273_ = lean_usize_dec_lt(v_i_271_, v_sz_270_);
                if v___x_273_ == 0 {
                    return v_bs_272_;
                } else {
                    v_v_274_ = lean_array_uget(v_bs_272_, v_i_271_);
                    v___x_275_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_276_ = lean_array_uset(v_bs_272_, v_i_271_, v___x_275_);
                    v___x_277_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_v_274_);
                    v___x_278_ = 1usize;
                    v___x_279_ = lean_usize_add(v_i_271_, v___x_278_);
                    v___x_280_ = lean_array_uset(v_bs_x27_276_, v_i_271_, v___x_277_);
                    v_i_271_ = v___x_279_;
                    v_bs_272_ = v___x_280_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(
    mut v_x_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_289_: u8 = 0;
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_294_: u8 = 0;
    let mut v_info_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_300_: u8 = 0;
    let mut v_sz_301_: usize = 0;
    let mut v___x_302_: usize = 0;
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_282_) {
                3 => {
                    v_info_283_ = crate::leanh::lean_ctor_get(v_x_282_, 0);
                    v_rawVal_284_ = crate::leanh::lean_ctor_get(v_x_282_, 1);
                    v_val_285_ = crate::leanh::lean_ctor_get(v_x_282_, 2);
                    v_preresolved_286_ = crate::leanh::lean_ctor_get(v_x_282_, 3);
                    v_isSharedCheck_294_ = (!crate::leanh::lean_is_exclusive(v_x_282_)) as u8;
                    if v_isSharedCheck_294_ == 0 {
                        v___x_288_ = v_x_282_;
                        v_isShared_289_ = v_isSharedCheck_294_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_preresolved_286_);
                        crate::leanh::lean_inc(v_val_285_);
                        crate::leanh::lean_inc(v_rawVal_284_);
                        crate::leanh::lean_inc(v_info_283_);
                        crate::leanh::lean_dec(v_x_282_);
                        v___x_288_ = crate::leanh::lean_box(0);
                        v_isShared_289_ = v_isSharedCheck_294_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_info_295_ = crate::leanh::lean_ctor_get(v_x_282_, 0);
                    v_kind_296_ = crate::leanh::lean_ctor_get(v_x_282_, 1);
                    v_args_297_ = crate::leanh::lean_ctor_get(v_x_282_, 2);
                    v_isSharedCheck_307_ = (!crate::leanh::lean_is_exclusive(v_x_282_)) as u8;
                    if v_isSharedCheck_307_ == 0 {
                        v___x_299_ = v_x_282_;
                        v_isShared_300_ = v_isSharedCheck_307_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_297_);
                        crate::leanh::lean_inc(v_kind_296_);
                        crate::leanh::lean_inc(v_info_295_);
                        crate::leanh::lean_dec(v_x_282_);
                        v___x_299_ = crate::leanh::lean_box(0);
                        v_isShared_300_ = v_isSharedCheck_307_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    return v_x_282_;
                }
            },
            1 => {
                v___x_290_ = lean_erase_macro_scopes(v_val_285_);
                if v_isShared_289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_288_, 2, v___x_290_);
                    v___x_292_ = v___x_288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_293_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_293_, 0, v_info_283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_293_, 1, v_rawVal_284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_293_, 2, v___x_290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_293_, 3, v_preresolved_286_);
                    v___x_292_ = v_reuseFailAlloc_293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_292_;
            }
            3 => {
                v_sz_301_ = lean_array_size(v_args_297_);
                v___x_302_ = 0usize;
                v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_301_, v___x_302_, v_args_297_);
                if v_isShared_300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_299_, 2, v___x_303_);
                    v___x_305_ = v___x_299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_306_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 0, v_info_295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 1, v_kind_296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_303_);
                    v___x_305_ = v_reuseFailAlloc_306_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(
    mut v_sz_308_: *mut crate::leanh::LeanObject,
    mut v_i_309_: *mut crate::leanh::LeanObject,
    mut v_bs_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_311_: usize = 0;
    let mut v_i_boxed_312_: usize = 0;
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_311_ = crate::leanh::lean_unbox_usize(v_sz_308_);
    crate::leanh::lean_dec(v_sz_308_);
    v_i_boxed_312_ = crate::leanh::lean_unbox_usize(v_i_309_);
    crate::leanh::lean_dec(v_i_309_);
    v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_boxed_311_, v_i_boxed_312_, v_bs_310_);
    return v_res_313_;
}
pub unsafe fn l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(
    mut v_stx_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_314_);
    return v___x_315_;
}
pub unsafe fn l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(
    mut v_k_316_: *mut crate::leanh::LeanObject,
    mut v_stx_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_317_);
    return v___x_318_;
}
pub unsafe fn l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(
    mut v_k_319_: *mut crate::leanh::LeanObject,
    mut v_stx_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(v_k_319_, v_stx_320_);
    crate::leanh::lean_dec(v_k_319_);
    return v_res_321_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(
    mut v_opts_322_: *mut crate::leanh::LeanObject,
    mut v_opt_323_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_324_ = crate::leanh::lean_ctor_get(v_opt_323_, 0);
    v_defValue_325_ = crate::leanh::lean_ctor_get(v_opt_323_, 1);
    v_map_326_ = crate::leanh::lean_ctor_get(v_opts_322_, 0);
    v___x_327_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_326_,
            v_name_324_,
        );
    if crate::leanh::lean_obj_tag(v___x_327_) == 0 {
        let mut v___x_328_: u8 = 0;
        v___x_328_ = (crate::leanh::lean_unbox(v_defValue_325_) as u8);
        return v___x_328_;
    } else {
        let mut v_val_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_329_ = crate::leanh::lean_ctor_get(v___x_327_, 0);
        crate::leanh::lean_inc(v_val_329_);
        crate::leanh::lean_dec_ref_known(v___x_327_, 1);
        if crate::leanh::lean_obj_tag(v_val_329_) == 1 {
            let mut v_v_330_: u8 = 0;
            v_v_330_ = crate::leanh::lean_ctor_get_uint8(v_val_329_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_329_, 0);
            return v_v_330_;
        } else {
            let mut v___x_331_: u8 = 0;
            crate::leanh::lean_dec(v_val_329_);
            v___x_331_ = (crate::leanh::lean_unbox(v_defValue_325_) as u8);
            return v___x_331_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(
    mut v_opts_332_: *mut crate::leanh::LeanObject,
    mut v_opt_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_334_: u8 = 0;
    let mut v_r_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ =
        l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v_opts_332_, v_opt_333_);
    crate::leanh::lean_dec_ref(v_opt_333_);
    crate::leanh::lean_dec_ref(v_opts_332_);
    v_r_335_ = crate::leanh::lean_box((v_res_334_) as usize);
    return v_r_335_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(
    mut v_opts_336_: *mut crate::leanh::LeanObject,
    mut v_opt_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_338_ = crate::leanh::lean_ctor_get(v_opt_337_, 0);
    v_defValue_339_ = crate::leanh::lean_ctor_get(v_opt_337_, 1);
    v_map_340_ = crate::leanh::lean_ctor_get(v_opts_336_, 0);
    v___x_341_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_340_,
            v_name_338_,
        );
    if crate::leanh::lean_obj_tag(v___x_341_) == 0 {
        crate::leanh::lean_inc(v_defValue_339_);
        return v_defValue_339_;
    } else {
        let mut v_val_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_342_ = crate::leanh::lean_ctor_get(v___x_341_, 0);
        crate::leanh::lean_inc(v_val_342_);
        crate::leanh::lean_dec_ref_known(v___x_341_, 1);
        if crate::leanh::lean_obj_tag(v_val_342_) == 3 {
            let mut v_v_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_343_ = crate::leanh::lean_ctor_get(v_val_342_, 0);
            crate::leanh::lean_inc(v_v_343_);
            crate::leanh::lean_dec_ref_known(v_val_342_, 1);
            return v_v_343_;
        } else {
            crate::leanh::lean_dec(v_val_342_);
            crate::leanh::lean_inc(v_defValue_339_);
            return v_defValue_339_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1___boxed(
    mut v_opts_344_: *mut crate::leanh::LeanObject,
    mut v_opt_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(v_opts_344_, v_opt_345_);
    crate::leanh::lean_dec_ref(v_opt_345_);
    crate::leanh::lean_dec_ref(v_opts_344_);
    return v_res_346_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
    v___x_361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_361_, 0, v___x_360_);
    return v___x_361_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: usize = 0;
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = 5usize;
    v___x_363_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_364_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_365_ = lean_mk_empty_array_with_capacity(v___x_364_);
    v___x_366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__5_once),
        _init_l_Lake_Package_mkConfigString___closed__5,
    );
    v___x_367_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_367_, 0, v___x_366_);
    crate::leanh::lean_ctor_set(v___x_367_, 1, v___x_365_);
    crate::leanh::lean_ctor_set(v___x_367_, 2, v___x_363_);
    crate::leanh::lean_ctor_set(v___x_367_, 3, v___x_363_);
    crate::leanh::lean_ctor_set_usize(v___x_367_, 4, v___x_362_);
    return v___x_367_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_368_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__7_once),
        _init_l_Lake_Package_mkConfigString___closed__7,
    );
    v___x_370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_370_, 0, v___x_369_);
    return v___x_370_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__8_once),
        _init_l_Lake_Package_mkConfigString___closed__8,
    );
    v___x_372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___x_371_);
    return v___x_372_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = l_Lean_NameSet_empty;
    v___x_374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6_once),
        _init_l_Lake_Package_mkConfigString___closed__6,
    );
    v___x_375_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_375_, 0, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_375_, 1, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_375_, 2, v___x_373_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_377_ = l_Lean_firstFrontendMacroScope;
    v___x_378_ = lean_nat_add(v___x_377_, v___x_376_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: u64 = 0;
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6_once),
        _init_l_Lake_Package_mkConfigString___closed__6,
    );
    v___x_390_ = 0u64;
    v___x_391_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_391_, 0, v___x_389_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_391_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_390_,
    );
    return v___x_391_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__6_once),
        _init_l_Lake_Package_mkConfigString___closed__6,
    );
    v___x_393_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__8_once),
        _init_l_Lake_Package_mkConfigString___closed__8,
    );
    v___x_394_ = 1;
    v___x_395_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_395_, 0, v___x_393_);
    crate::leanh::lean_ctor_set(v___x_395_, 1, v___x_393_);
    crate::leanh::lean_ctor_set(v___x_395_, 2, v___x_392_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_395_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_394_,
    );
    return v___x_395_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_399_ = l_Lean_Options_empty;
    v___x_400_ = l_Lean_Core_getMaxHeartbeats(v___x_399_);
    return v___x_400_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__21() -> u8 {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    v___x_401_ = l_Lean_diagnostics;
    v___x_402_ = l_Lean_Options_empty;
    v___x_403_ =
        l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v___x_402_, v___x_401_);
    return v___x_403_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = l_Lean_maxRecDepth;
    v___x_405_ = l_Lean_Options_empty;
    v___x_406_ =
        l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(v___x_405_, v___x_404_);
    return v___x_406_;
}
pub unsafe fn _init_l_Lake_Package_mkConfigString___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = l_Lake_Package_mkConfigString___closed__25;
    v___x_411_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_410_,
    );
    return v___x_411_;
}
pub unsafe fn l_Lake_Package_mkConfigString(
    mut v_pkg_412_: *mut crate::leanh::LeanObject,
    mut v_lang_413_: u8,
    mut v_a_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: u32 = 0;
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v_fileName_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_471_: u8 = 0;
    let mut v_inheritedTraceOptions_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_unused_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_lang_413_ == 0 {
                    v___x_426_ = 0;
                    v___x_427_ = l_Lake_Package_mkConfigString___closed__4;
                    v___x_428_ = l_Lean_Options_empty;
                    v___x_429_ = 1024;
                    v___x_430_ = l_Lake_importModulesUsingCache(v___x_427_, v___x_428_, v___x_429_);
                    if crate::leanh::lean_obj_tag(v___x_430_) == 0 {
                        v_a_431_ = crate::leanh::lean_ctor_get(v___x_430_, 0);
                        crate::leanh::lean_inc(v_a_431_);
                        crate::leanh::lean_dec_ref_known(v___x_430_, 1);
                        v___x_432_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_433_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__9_once),
                            _init_l_Lake_Package_mkConfigString___closed__9,
                        );
                        v___x_434_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__10_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__10,
                        );
                        v___x_435_ = lean_io_get_num_heartbeats();
                        v___x_436_ = l_Lean_firstFrontendMacroScope;
                        v___x_437_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__11_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__11,
                        );
                        v___x_438_ = l_Lake_Package_mkConfigString___closed__14;
                        v___x_439_ = crate::leanh::lean_box(0);
                        v___x_440_ = crate::leanh::lean_box(0);
                        v___x_441_ = l_Lake_Package_mkConfigString___closed__15;
                        v___x_442_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__16),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__16_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__16,
                        );
                        v___x_443_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__17),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__17_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__17,
                        );
                        v___x_444_ = l_Lake_Package_mkConfigString___closed__18;
                        v___x_445_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_445_, 0, v_a_431_);
                        crate::leanh::lean_ctor_set(v___x_445_, 1, v___x_437_);
                        crate::leanh::lean_ctor_set(v___x_445_, 2, v___x_438_);
                        crate::leanh::lean_ctor_set(v___x_445_, 3, v___x_441_);
                        crate::leanh::lean_ctor_set(v___x_445_, 4, v___x_442_);
                        crate::leanh::lean_ctor_set(v___x_445_, 5, v___x_433_);
                        crate::leanh::lean_ctor_set(v___x_445_, 6, v___x_434_);
                        crate::leanh::lean_ctor_set(v___x_445_, 7, v___x_443_);
                        crate::leanh::lean_ctor_set(v___x_445_, 8, v___x_444_);
                        v___x_446_ = lean_st_mk_ref(v___x_445_);
                        v___x_447_ = l_Lean_inheritedTraceOptions;
                        v___x_448_ = lean_st_ref_get(v___x_447_);
                        v___x_449_ = lean_st_ref_get(v___x_446_);
                        v_env_450_ = crate::leanh::lean_ctor_get(v___x_449_, 0);
                        crate::leanh::lean_inc_ref(v_env_450_);
                        crate::leanh::lean_dec(v___x_449_);
                        v___x_451_ = l_Lake_Package_mkConfigString___closed__19;
                        v___x_452_ = l_Lean_instInhabitedFileMap_default;
                        v___x_453_ = crate::leanh::lean_box(0);
                        v___x_454_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__20),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__20_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__20,
                        );
                        v___x_455_ = crate::leanh::lean_box(0);
                        v___x_456_ = l_Lake_Package_mkLeanConfig(v_pkg_412_);
                        v___x_457_ =
                            l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v___x_456_);
                        v___x_458_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__21),
                            core::ptr::addr_of_mut!(
                                l_Lake_Package_mkConfigString___closed__21_once
                            ),
                            _init_l_Lake_Package_mkConfigString___closed__21,
                        );
                        v___x_521_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_450_);
                        crate::leanh::lean_dec_ref(v_env_450_);
                        if v___x_521_ == 0 {
                            if v___x_458_ == 0 {
                                crate::leanh::lean_inc(v___x_446_);
                                v_fileName_460_ = v___x_451_;
                                v_fileMap_461_ = v___x_452_;
                                v_currRecDepth_462_ = v___x_432_;
                                v_ref_463_ = v___x_453_;
                                v_currNamespace_464_ = v___x_439_;
                                v_openDecls_465_ = v___x_440_;
                                v_initHeartbeats_466_ = v___x_435_;
                                v_maxHeartbeats_467_ = v___x_454_;
                                v_quotContext_468_ = v___x_439_;
                                v_currMacroScope_469_ = v___x_436_;
                                v_cancelTk_x3f_470_ = v___x_455_;
                                v_suppressElabErrors_471_ = v___x_426_;
                                v_inheritedTraceOptions_472_ = v___x_448_;
                                v___y_473_ = v___x_446_;
                                state = 2;
                                continue;
                            } else {
                                v___y_501_ = v___x_521_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___y_501_ = v___x_458_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_pkg_412_);
                        v_a_522_ = crate::leanh::lean_ctor_get(v___x_430_, 0);
                        crate::leanh::lean_inc(v_a_522_);
                        crate::leanh::lean_dec_ref_known(v___x_430_, 1);
                        v___x_523_ = lean_io_error_to_string(v_a_522_);
                        v___x_524_ = 3;
                        v___x_525_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_523_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_525_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_524_,
                        );
                        v___x_526_ = lean_array_get_size(v_a_414_);
                        v___x_527_ = lean_array_push(v_a_414_, v___x_525_);
                        v___x_528_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_528_, 0, v___x_526_);
                        crate::leanh::lean_ctor_set(v___x_528_, 1, v___x_527_);
                        return v___x_528_;
                    }
                } else {
                    v___x_529_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__26),
                        core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__26_once),
                        _init_l_Lake_Package_mkConfigString___closed__26,
                    );
                    v___x_530_ = l_Lake_Package_mkTomlConfig(v_pkg_412_, v___x_529_);
                    v___x_531_ = l_Lake_Toml_ppTable(v___x_530_);
                    crate::leanh::lean_dec_ref(v___x_530_);
                    v___x_532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_531_);
                    crate::leanh::lean_ctor_set(v___x_532_, 1, v_a_414_);
                    return v___x_532_;
                }
            }
            1 => {
                v___x_418_ = l_Lake_Package_mkConfigString___closed__0;
                v___x_419_ = lean_io_error_to_string(v_a_417_);
                v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
                crate::leanh::lean_dec_ref(v___x_419_);
                v___x_421_ = 3;
                v___x_422_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_420_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_422_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_421_,
                );
                v___x_423_ = lean_array_get_size(v_a_414_);
                v___x_424_ = lean_array_push(v_a_414_, v___x_422_);
                v___x_425_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_425_, 0, v___x_423_);
                crate::leanh::lean_ctor_set(v___x_425_, 1, v___x_424_);
                return v___x_425_;
            }
            2 => {
                v___x_474_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__22),
                    core::ptr::addr_of_mut!(l_Lake_Package_mkConfigString___closed__22_once),
                    _init_l_Lake_Package_mkConfigString___closed__22,
                );
                crate::leanh::lean_inc(v_cancelTk_x3f_470_);
                crate::leanh::lean_inc(v_currMacroScope_469_);
                crate::leanh::lean_inc(v_quotContext_468_);
                crate::leanh::lean_inc(v_maxHeartbeats_467_);
                crate::leanh::lean_inc(v_openDecls_465_);
                crate::leanh::lean_inc(v_currNamespace_464_);
                crate::leanh::lean_inc(v_ref_463_);
                crate::leanh::lean_inc_ref(v_fileMap_461_);
                crate::leanh::lean_inc_ref(v_fileName_460_);
                v___x_475_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_475_, 0, v_fileName_460_);
                crate::leanh::lean_ctor_set(v___x_475_, 1, v_fileMap_461_);
                crate::leanh::lean_ctor_set(v___x_475_, 2, v___x_428_);
                crate::leanh::lean_ctor_set(v___x_475_, 3, v_currRecDepth_462_);
                crate::leanh::lean_ctor_set(v___x_475_, 4, v___x_474_);
                crate::leanh::lean_ctor_set(v___x_475_, 5, v_ref_463_);
                crate::leanh::lean_ctor_set(v___x_475_, 6, v_currNamespace_464_);
                crate::leanh::lean_ctor_set(v___x_475_, 7, v_openDecls_465_);
                crate::leanh::lean_ctor_set(v___x_475_, 8, v_initHeartbeats_466_);
                crate::leanh::lean_ctor_set(v___x_475_, 9, v_maxHeartbeats_467_);
                crate::leanh::lean_ctor_set(v___x_475_, 10, v_quotContext_468_);
                crate::leanh::lean_ctor_set(v___x_475_, 11, v_currMacroScope_469_);
                crate::leanh::lean_ctor_set(v___x_475_, 12, v_cancelTk_x3f_470_);
                crate::leanh::lean_ctor_set(v___x_475_, 13, v_inheritedTraceOptions_472_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___x_458_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_471_,
                );
                v___x_476_ = l_Lean_PrettyPrinter_ppModule(v___x_457_, v___x_475_, v___y_473_);
                crate::leanh::lean_dec(v___y_473_);
                crate::leanh::lean_dec_ref_known(v___x_475_, 14);
                if crate::leanh::lean_obj_tag(v___x_476_) == 0 {
                    v_a_477_ = crate::leanh::lean_ctor_get(v___x_476_, 0);
                    crate::leanh::lean_inc(v_a_477_);
                    crate::leanh::lean_dec_ref_known(v___x_476_, 1);
                    v___x_478_ = lean_st_ref_get(v___x_446_);
                    crate::leanh::lean_dec(v___x_446_);
                    crate::leanh::lean_dec(v___x_478_);
                    v___x_479_ = l_Std_Format_defWidth;
                    v___x_480_ = l_Std_Format_pretty(v_a_477_, v___x_479_, v___x_432_, v___x_432_);
                    v___x_481_ = lean_string_utf8_byte_size(v___x_480_);
                    v___x_482_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_482_, 0, v___x_480_);
                    crate::leanh::lean_ctor_set(v___x_482_, 1, v___x_432_);
                    crate::leanh::lean_ctor_set(v___x_482_, 2, v___x_481_);
                    v___x_483_ = l_String_Slice_trimAscii(v___x_482_);
                    v_str_484_ = crate::leanh::lean_ctor_get(v___x_483_, 0);
                    crate::leanh::lean_inc_ref(v_str_484_);
                    v_startInclusive_485_ = crate::leanh::lean_ctor_get(v___x_483_, 1);
                    crate::leanh::lean_inc(v_startInclusive_485_);
                    v_endExclusive_486_ = crate::leanh::lean_ctor_get(v___x_483_, 2);
                    crate::leanh::lean_inc(v_endExclusive_486_);
                    crate::leanh::lean_dec_ref(v___x_483_);
                    v___x_487_ = lean_string_utf8_extract(
                        v_str_484_,
                        v_startInclusive_485_,
                        v_endExclusive_486_,
                    );
                    crate::leanh::lean_dec(v_endExclusive_486_);
                    crate::leanh::lean_dec(v_startInclusive_485_);
                    crate::leanh::lean_dec_ref(v_str_484_);
                    v___x_488_ = l_Lake_Package_mkConfigString___closed__23;
                    v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
                    v___x_490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_490_, 0, v___x_489_);
                    crate::leanh::lean_ctor_set(v___x_490_, 1, v_a_414_);
                    return v___x_490_;
                } else {
                    crate::leanh::lean_dec(v___x_446_);
                    v_a_491_ = crate::leanh::lean_ctor_get(v___x_476_, 0);
                    crate::leanh::lean_inc(v_a_491_);
                    crate::leanh::lean_dec_ref_known(v___x_476_, 1);
                    if crate::leanh::lean_obj_tag(v_a_491_) == 0 {
                        v_msg_492_ = crate::leanh::lean_ctor_get(v_a_491_, 1);
                        crate::leanh::lean_inc_ref(v_msg_492_);
                        crate::leanh::lean_dec_ref_known(v_a_491_, 2);
                        v___x_493_ = l_Lean_MessageData_toString(v_msg_492_);
                        v___x_494_ = lean_mk_io_user_error(v___x_493_);
                        v_a_417_ = v___x_494_;
                        state = 1;
                        continue;
                    } else {
                        v_id_495_ = crate::leanh::lean_ctor_get(v_a_491_, 0);
                        crate::leanh::lean_inc(v_id_495_);
                        crate::leanh::lean_dec_ref_known(v_a_491_, 2);
                        v___x_496_ = l_Lake_Package_mkConfigString___closed__24;
                        v___x_497_ = l_Nat_reprFast(v_id_495_);
                        v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
                        crate::leanh::lean_dec_ref(v___x_497_);
                        v___x_499_ = lean_mk_io_user_error(v___x_498_);
                        v_a_417_ = v___x_499_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_501_ == 0 {
                    v___x_502_ = lean_st_ref_take(v___x_446_);
                    v_env_503_ = crate::leanh::lean_ctor_get(v___x_502_, 0);
                    v_nextMacroScope_504_ = crate::leanh::lean_ctor_get(v___x_502_, 1);
                    v_ngen_505_ = crate::leanh::lean_ctor_get(v___x_502_, 2);
                    v_auxDeclNGen_506_ = crate::leanh::lean_ctor_get(v___x_502_, 3);
                    v_traceState_507_ = crate::leanh::lean_ctor_get(v___x_502_, 4);
                    v_messages_508_ = crate::leanh::lean_ctor_get(v___x_502_, 6);
                    v_infoState_509_ = crate::leanh::lean_ctor_get(v___x_502_, 7);
                    v_snapshotTasks_510_ = crate::leanh::lean_ctor_get(v___x_502_, 8);
                    v_isSharedCheck_519_ = (!crate::leanh::lean_is_exclusive(v___x_502_)) as u8;
                    if v_isSharedCheck_519_ == 0 {
                        v_unused_520_ = crate::leanh::lean_ctor_get(v___x_502_, 5);
                        crate::leanh::lean_dec(v_unused_520_);
                        v___x_512_ = v___x_502_;
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_510_);
                        crate::leanh::lean_inc(v_infoState_509_);
                        crate::leanh::lean_inc(v_messages_508_);
                        crate::leanh::lean_inc(v_traceState_507_);
                        crate::leanh::lean_inc(v_auxDeclNGen_506_);
                        crate::leanh::lean_inc(v_ngen_505_);
                        crate::leanh::lean_inc(v_nextMacroScope_504_);
                        crate::leanh::lean_inc(v_env_503_);
                        crate::leanh::lean_dec(v___x_502_);
                        v___x_512_ = crate::leanh::lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v___x_446_);
                    v_fileName_460_ = v___x_451_;
                    v_fileMap_461_ = v___x_452_;
                    v_currRecDepth_462_ = v___x_432_;
                    v_ref_463_ = v___x_453_;
                    v_currNamespace_464_ = v___x_439_;
                    v_openDecls_465_ = v___x_440_;
                    v_initHeartbeats_466_ = v___x_435_;
                    v_maxHeartbeats_467_ = v___x_454_;
                    v_quotContext_468_ = v___x_439_;
                    v_currMacroScope_469_ = v___x_436_;
                    v_cancelTk_x3f_470_ = v___x_455_;
                    v_suppressElabErrors_471_ = v___x_426_;
                    v_inheritedTraceOptions_472_ = v___x_448_;
                    v___y_473_ = v___x_446_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_514_ = l_Lean_Kernel_enableDiag(v_env_503_, v___x_458_);
                if v_isShared_513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_512_, 5, v___x_433_);
                    crate::leanh::lean_ctor_set(v___x_512_, 0, v___x_514_);
                    v___x_516_ = v___x_512_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 1, v_nextMacroScope_504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 2, v_ngen_505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 3, v_auxDeclNGen_506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 4, v_traceState_507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 5, v___x_433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 6, v_messages_508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 7, v_infoState_509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 8, v_snapshotTasks_510_);
                    v___x_516_ = v_reuseFailAlloc_518_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_517_ = lean_st_ref_set(v___x_446_, v___x_516_);
                crate::leanh::lean_inc(v___x_446_);
                v_fileName_460_ = v___x_451_;
                v_fileMap_461_ = v___x_452_;
                v_currRecDepth_462_ = v___x_432_;
                v_ref_463_ = v___x_453_;
                v_currNamespace_464_ = v___x_439_;
                v_openDecls_465_ = v___x_440_;
                v_initHeartbeats_466_ = v___x_435_;
                v_maxHeartbeats_467_ = v___x_454_;
                v_quotContext_468_ = v___x_439_;
                v_currMacroScope_469_ = v___x_436_;
                v_cancelTk_x3f_470_ = v___x_455_;
                v_suppressElabErrors_471_ = v___x_426_;
                v_inheritedTraceOptions_472_ = v___x_448_;
                v___y_473_ = v___x_446_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_mkConfigString___boxed(
    mut v_pkg_533_: *mut crate::leanh::LeanObject,
    mut v_lang_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lang_boxed_537_: u8 = 0;
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lang_boxed_537_ = (crate::leanh::lean_unbox(v_lang_534_) as u8);
    v_res_538_ = l_Lake_Package_mkConfigString(v_pkg_533_, v_lang_boxed_537_, v_a_535_);
    return v_res_538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Translate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Translate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Translate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_CLI_Translate_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_CLI_Translate_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Translate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_CLI_Translate(builtin);
}

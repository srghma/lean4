// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Lean.Parser.Types Lake.Toml.Data.Value Lake.Toml.Elab Lake.Util.Message Std.Do
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take,
};
use crate::r#gen::Init::Prelude::l_Lean_firstFrontendMacroScope;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lake::Toml::Data::Value::{
    initialize_Lake_Toml_Data_Value, runtime_initialize_Lake_Toml_Data_Value,
};
use crate::r#gen::Lake::Toml::Elab::Expression::l_Lake_Toml_elabToml;
use crate::r#gen::Lake::Toml::Elab::{
    initialize_Lake_Toml_Elab, runtime_initialize_Lake_Toml_Elab,
};
use crate::r#gen::Lake::Toml::Grammar::l_Lake_Toml_toml;
use crate::r#gen::Lake::Util::Message::{
    initialize_Lake_Util_Message, l_Lake_mkExceptionMessage, l_Lake_mkMessageNoPos,
    l_Lake_mkParserErrorMessage, runtime_initialize_Lake_Util_Message,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Core_getMaxHeartbeats, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Trie::l_Lean_Data_Trie_empty;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled, lean_mk_empty_environment,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add, l_Lean_MessageLog_empty,
    l_Lean_MessageLog_hasErrors, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Extension::l_Lean_Parser_mkParserState;
use crate::r#gen::Lean::Parser::Types::{
    initialize_Lean_Parser_Types, l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserFn_run,
    l_Lean_Parser_SyntaxStack_back, runtime_initialize_Lean_Parser_Types,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l_Lean_inheritedTraceOptions;
use crate::r#gen::Std::Do::{initialize_Std_Do, runtime_initialize_Std_Do};
static mut l_Lake_Toml_loadToml___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_loadToml___closed__1_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
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
static mut l_Lake_Toml_loadToml___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__2_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 110, 100, 32, 111, 102, 32, 105, 110, 112, 117, 116, 0],
    };
static mut l_Lake_Toml_loadToml___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__3_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__4_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_loadToml___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_loadToml___closed__6_value: leanh::LeanStringObject<6> =
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
        m_data: [95, 117, 110, 105, 113, 0],
    };
static mut l_Lake_Toml_loadToml___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__6_value)
                as *mut leanh::LeanObject,
            3978731030111751661 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__7_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_loadToml___closed__9_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__9_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_loadToml___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_loadToml___closed__17_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_Toml_loadToml___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__17_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_loadToml___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_loadToml___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__19: u8 = 0;
static mut l_Lake_Toml_loadToml___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_loadToml___closed__21_value: leanh::LeanStringObject<40> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 105, 116, 105, 97, 108, 105,
            122, 101, 32, 84, 79, 77, 76, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110,
            116, 58, 32, 0,
        ],
    };
static mut l_Lake_Toml_loadToml___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_loadToml___closed__21_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_loadToml___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_loadToml___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(
    mut v_opts_230_: *mut leanh::LeanObject,
    mut v_opt_231_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_232_ = leanh::lean_ctor_get(v_opt_231_, 0);
    v_defValue_233_ = leanh::lean_ctor_get(v_opt_231_, 1);
    v_map_234_ = leanh::lean_ctor_get(v_opts_230_, 0);
    v___x_235_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_234_,
            v_name_232_,
        );
    if leanh::lean_obj_tag(v___x_235_) == 0 {
        let mut v___x_236_: u8 = 0;
        v___x_236_ = (leanh::lean_unbox(v_defValue_233_) as u8);
        return v___x_236_;
    } else {
        let mut v_val_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_237_ = leanh::lean_ctor_get(v___x_235_, 0);
        leanh::lean_inc(v_val_237_);
        leanh::lean_dec_ref_known(v___x_235_, 1);
        if leanh::lean_obj_tag(v_val_237_) == 1 {
            let mut v_v_238_: u8 = 0;
            v_v_238_ = leanh::lean_ctor_get_uint8(v_val_237_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_237_, 0);
            return v_v_238_;
        } else {
            let mut v___x_239_: u8 = 0;
            leanh::lean_dec(v_val_237_);
            v___x_239_ = (leanh::lean_unbox(v_defValue_233_) as u8);
            return v___x_239_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(
    mut v_opts_240_: *mut leanh::LeanObject,
    mut v_opt_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: u8 = 0;
    let mut v_r_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v_opts_240_, v_opt_241_);
    leanh::lean_dec_ref(v_opt_241_);
    leanh::lean_dec_ref(v_opts_240_);
    v_r_243_ = leanh::lean_box((v_res_242_) as usize);
    return v_r_243_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(
    mut v_opts_244_: *mut leanh::LeanObject,
    mut v_opt_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_246_ = leanh::lean_ctor_get(v_opt_245_, 0);
    v_defValue_247_ = leanh::lean_ctor_get(v_opt_245_, 1);
    v_map_248_ = leanh::lean_ctor_get(v_opts_244_, 0);
    v___x_249_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_248_,
            v_name_246_,
        );
    if leanh::lean_obj_tag(v___x_249_) == 0 {
        leanh::lean_inc(v_defValue_247_);
        return v_defValue_247_;
    } else {
        let mut v_val_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_250_ = leanh::lean_ctor_get(v___x_249_, 0);
        leanh::lean_inc(v_val_250_);
        leanh::lean_dec_ref_known(v___x_249_, 1);
        if leanh::lean_obj_tag(v_val_250_) == 3 {
            let mut v_v_251_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_251_ = leanh::lean_ctor_get(v_val_250_, 0);
            leanh::lean_inc(v_v_251_);
            leanh::lean_dec_ref_known(v_val_250_, 1);
            return v_v_251_;
        } else {
            leanh::lean_dec(v_val_250_);
            leanh::lean_inc(v_defValue_247_);
            return v_defValue_247_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(
    mut v_opts_252_: *mut leanh::LeanObject,
    mut v_opt_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(v_opts_252_, v_opt_253_);
    leanh::lean_dec_ref(v_opt_253_);
    leanh::lean_dec_ref(v_opts_252_);
    return v_res_254_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Lean_Data_Trie_empty(leanh::lean_box(0));
    return v___x_255_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ = leanh::lean_unsigned_to_nat(1);
    v___x_266_ = l_Lean_firstFrontendMacroScope;
    v___x_267_ = lean_nat_add(v___x_266_, v___x_265_);
    return v___x_267_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = leanh::lean_unsigned_to_nat(32);
    v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
    v___x_280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_280_, 0, v___x_279_);
    return v___x_280_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_281_: usize = 0;
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = 5usize;
    v___x_282_ = leanh::lean_unsigned_to_nat(0);
    v___x_283_ = leanh::lean_unsigned_to_nat(32);
    v___x_284_ = lean_mk_empty_array_with_capacity(v___x_283_);
    v___x_285_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__10),
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__10_once),
        _init_l_Lake_Toml_loadToml___closed__10,
    );
    v___x_286_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_286_, 0, v___x_285_);
    leanh::lean_ctor_set(v___x_286_, 1, v___x_284_);
    leanh::lean_ctor_set(v___x_286_, 2, v___x_282_);
    leanh::lean_ctor_set(v___x_286_, 3, v___x_282_);
    leanh::lean_ctor_set_usize(v___x_286_, 4, v___x_281_);
    return v___x_286_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u64 = 0;
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11_once),
        _init_l_Lake_Toml_loadToml___closed__11,
    );
    v___x_288_ = 0u64;
    v___x_289_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_289_, 0, v___x_287_);
    leanh::lean_ctor_set_uint64(
        v___x_289_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_288_,
    );
    return v___x_289_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_290_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__13_once),
        _init_l_Lake_Toml_loadToml___closed__13,
    );
    v___x_292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_292_, 0, v___x_291_);
    return v___x_292_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__14_once),
        _init_l_Lake_Toml_loadToml___closed__14,
    );
    v___x_294_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_294_, 0, v___x_293_);
    leanh::lean_ctor_set(v___x_294_, 1, v___x_293_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Lean_NameSet_empty;
    v___x_296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11_once),
        _init_l_Lake_Toml_loadToml___closed__11,
    );
    v___x_297_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_297_, 0, v___x_296_);
    leanh::lean_ctor_set(v___x_297_, 1, v___x_296_);
    leanh::lean_ctor_set(v___x_297_, 2, v___x_295_);
    return v___x_297_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Lean_Options_empty;
    v___x_301_ = l_Lean_Core_getMaxHeartbeats(v___x_300_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__19() -> u8 {
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u8 = 0;
    v___x_302_ = l_Lean_diagnostics;
    v___x_303_ = l_Lean_Options_empty;
    v___x_304_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v___x_303_, v___x_302_);
    return v___x_304_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = l_Lean_maxRecDepth;
    v___x_306_ = l_Lean_Options_empty;
    v___x_307_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn _init_l_Lake_Toml_loadToml___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Lake_Toml_loadToml___closed__21;
    v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Lake_Toml_loadToml(
    mut v_ictx_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: u32 = 0;
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: u8 = 0;
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: u8 = 0;
    let mut v_fileName_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_385_: u8 = 0;
    let mut v_inheritedTraceOptions_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: u8 = 0;
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_404_: u8 = 0;
    let mut v_a_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_408_: u8 = 0;
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut v___y_417_: u8 = 0;
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_unused_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    let mut v_isSharedCheck_438_: u8 = 0;
    let mut v_a_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_442_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_313_ = 0;
                v___x_314_ = lean_mk_empty_environment(v___x_313_);
                if leanh::lean_obj_tag(v___x_314_) == 0 {
                    v_a_315_ = leanh::lean_ctor_get(v___x_314_, 0);
                    v_isSharedCheck_438_ = (!leanh::lean_is_exclusive(v___x_314_)) as u8;
                    if v_isSharedCheck_438_ == 0 {
                        v___x_317_ = v___x_314_;
                        v_isShared_318_ = v_isSharedCheck_438_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_315_);
                        leanh::lean_dec(v___x_314_);
                        v___x_317_ = leanh::lean_box(0);
                        v_isShared_318_ = v_isSharedCheck_438_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_439_ = leanh::lean_ctor_get(v___x_314_, 0);
                    v_isSharedCheck_455_ = (!leanh::lean_is_exclusive(v___x_314_)) as u8;
                    if v_isSharedCheck_455_ == 0 {
                        v___x_441_ = v___x_314_;
                        v_isShared_442_ = v_isSharedCheck_455_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_439_);
                        leanh::lean_dec(v___x_314_);
                        v___x_441_ = leanh::lean_box(0);
                        v_isShared_442_ = v_isSharedCheck_455_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_319_ = l_Lake_Toml_toml;
                v_fn_320_ = leanh::lean_ctor_get(v___x_319_, 1);
                v_inputString_321_ = leanh::lean_ctor_get(v_ictx_311_, 0);
                v_fileName_322_ = leanh::lean_ctor_get(v_ictx_311_, 1);
                v_fileMap_323_ = leanh::lean_ctor_get(v_ictx_311_, 2);
                v___x_324_ = l_Lean_Options_empty;
                v___x_325_ = leanh::lean_box(0);
                v___x_326_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_315_);
                v___x_327_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_327_, 0, v_a_315_);
                leanh::lean_ctor_set(v___x_327_, 1, v___x_324_);
                leanh::lean_ctor_set(v___x_327_, 2, v___x_325_);
                leanh::lean_ctor_set(v___x_327_, 3, v___x_326_);
                v___x_328_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__0),
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__0_once),
                    _init_l_Lake_Toml_loadToml___closed__0,
                );
                v___x_329_ = l_Lean_Parser_mkParserState(v_inputString_321_);
                leanh::lean_inc_ref(v_ictx_311_);
                leanh::lean_inc_ref(v_fn_320_);
                v___x_330_ = l_Lean_Parser_ParserFn_run(
                    v_fn_320_,
                    v_ictx_311_,
                    v___x_327_,
                    v___x_328_,
                    v___x_329_,
                );
                v_errorMsg_331_ = leanh::lean_ctor_get(v___x_330_, 4);
                leanh::lean_inc(v_errorMsg_331_);
                if leanh::lean_obj_tag(v_errorMsg_331_) == 1 {
                    leanh::lean_dec(v_a_315_);
                    v_val_332_ = leanh::lean_ctor_get(v_errorMsg_331_, 0);
                    leanh::lean_inc(v_val_332_);
                    leanh::lean_dec_ref_known(v_errorMsg_331_, 1);
                    v___x_333_ = l_Lake_mkParserErrorMessage(v_ictx_311_, v___x_330_, v_val_332_);
                    leanh::lean_dec_ref(v___x_330_);
                    v___x_334_ = l_Lean_MessageLog_empty;
                    v___x_335_ = l_Lean_MessageLog_add(v___x_333_, v___x_334_);
                    if v_isShared_318_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_317_, 1);
                        leanh::lean_ctor_set(v___x_317_, 0, v___x_335_);
                        v___x_337_ = v___x_317_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_338_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
                        v___x_337_ = v_reuseFailAlloc_338_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_errorMsg_331_);
                    v_stxStack_339_ = leanh::lean_ctor_get(v___x_330_, 0);
                    leanh::lean_inc_ref(v_stxStack_339_);
                    v_pos_340_ = leanh::lean_ctor_get(v___x_330_, 2);
                    leanh::lean_inc(v_pos_340_);
                    v___x_341_ = l_Lean_Parser_InputContext_atEnd(v_ictx_311_, v_pos_340_);
                    leanh::lean_dec(v_pos_340_);
                    if v___x_341_ == 0 {
                        leanh::lean_dec_ref(v_stxStack_339_);
                        leanh::lean_dec(v_a_315_);
                        v___x_342_ = l_Lake_Toml_loadToml___closed__4;
                        v___x_343_ =
                            l_Lake_mkParserErrorMessage(v_ictx_311_, v___x_330_, v___x_342_);
                        leanh::lean_dec_ref(v___x_330_);
                        v___x_344_ = l_Lean_MessageLog_empty;
                        v___x_345_ = l_Lean_MessageLog_add(v___x_343_, v___x_344_);
                        if v_isShared_318_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_317_, 1);
                            leanh::lean_ctor_set(v___x_317_, 0, v___x_345_);
                            v___x_347_ = v___x_317_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
                            v___x_347_ = v_reuseFailAlloc_348_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_330_);
                        leanh::lean_del_object(v___x_317_);
                        v___x_349_ = leanh::lean_unsigned_to_nat(0);
                        v___x_350_ = l_Lean_firstFrontendMacroScope;
                        v___x_351_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__5),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__5_once),
                            _init_l_Lake_Toml_loadToml___closed__5,
                        );
                        v___x_352_ = l_Lake_Toml_loadToml___closed__8;
                        v___x_353_ = l_Lake_Toml_loadToml___closed__9;
                        v___x_354_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__11_once),
                            _init_l_Lake_Toml_loadToml___closed__11,
                        );
                        v___x_355_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__12),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__12_once),
                            _init_l_Lake_Toml_loadToml___closed__12,
                        );
                        v___x_356_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__14),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__14_once),
                            _init_l_Lake_Toml_loadToml___closed__14,
                        );
                        v___x_357_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__15),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__15_once),
                            _init_l_Lake_Toml_loadToml___closed__15,
                        );
                        v___x_358_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__16),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__16_once),
                            _init_l_Lake_Toml_loadToml___closed__16,
                        );
                        v___x_359_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        leanh::lean_ctor_set(v___x_359_, 0, v___x_356_);
                        leanh::lean_ctor_set(v___x_359_, 1, v___x_356_);
                        leanh::lean_ctor_set(v___x_359_, 2, v___x_354_);
                        leanh::lean_ctor_set_uint8(
                            v___x_359_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            v___x_341_,
                        );
                        v___x_360_ = l_Lake_Toml_loadToml___closed__17;
                        v___x_361_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                        leanh::lean_ctor_set(v___x_361_, 0, v_a_315_);
                        leanh::lean_ctor_set(v___x_361_, 1, v___x_351_);
                        leanh::lean_ctor_set(v___x_361_, 2, v___x_352_);
                        leanh::lean_ctor_set(v___x_361_, 3, v___x_353_);
                        leanh::lean_ctor_set(v___x_361_, 4, v___x_355_);
                        leanh::lean_ctor_set(v___x_361_, 5, v___x_357_);
                        leanh::lean_ctor_set(v___x_361_, 6, v___x_358_);
                        leanh::lean_ctor_set(v___x_361_, 7, v___x_359_);
                        leanh::lean_ctor_set(v___x_361_, 8, v___x_360_);
                        v___x_362_ = lean_st_mk_ref(v___x_361_);
                        v___x_363_ = l_Lean_inheritedTraceOptions;
                        v___x_364_ = lean_st_ref_get(v___x_363_);
                        v___x_365_ = lean_st_ref_get(v___x_362_);
                        v_env_366_ = leanh::lean_ctor_get(v___x_365_, 0);
                        leanh::lean_inc_ref(v_env_366_);
                        leanh::lean_dec(v___x_365_);
                        v___x_367_ = leanh::lean_box(0);
                        v___x_368_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__18),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__18_once),
                            _init_l_Lake_Toml_loadToml___closed__18,
                        );
                        v___x_369_ = 0;
                        v___x_370_ = leanh::lean_box(0);
                        v___x_371_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_339_);
                        leanh::lean_dec_ref(v_stxStack_339_);
                        v___x_372_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__19),
                            core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__19_once),
                            _init_l_Lake_Toml_loadToml___closed__19,
                        );
                        v___x_437_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_366_);
                        leanh::lean_dec_ref(v_env_366_);
                        if v___x_437_ == 0 {
                            if v___x_372_ == 0 {
                                v___y_417_ = v___x_341_;
                                state = 10;
                                continue;
                            } else {
                                v___y_417_ = v___x_437_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___y_417_ = v___x_372_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_337_;
            }
            3 => {
                return v___x_347_;
            }
            4 => {
                v___x_388_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__20),
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__20_once),
                    _init_l_Lake_Toml_loadToml___closed__20,
                );
                leanh::lean_inc(v_cancelTk_x3f_384_);
                leanh::lean_inc(v_currMacroScope_383_);
                leanh::lean_inc(v_quotContext_382_);
                leanh::lean_inc(v_maxHeartbeats_381_);
                leanh::lean_inc(v_openDecls_379_);
                leanh::lean_inc(v_currNamespace_378_);
                leanh::lean_inc(v_ref_377_);
                v___x_389_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_389_, 0, v_fileName_374_);
                leanh::lean_ctor_set(v___x_389_, 1, v_fileMap_375_);
                leanh::lean_ctor_set(v___x_389_, 2, v___x_324_);
                leanh::lean_ctor_set(v___x_389_, 3, v_currRecDepth_376_);
                leanh::lean_ctor_set(v___x_389_, 4, v___x_388_);
                leanh::lean_ctor_set(v___x_389_, 5, v_ref_377_);
                leanh::lean_ctor_set(v___x_389_, 6, v_currNamespace_378_);
                leanh::lean_ctor_set(v___x_389_, 7, v_openDecls_379_);
                leanh::lean_ctor_set(v___x_389_, 8, v_initHeartbeats_380_);
                leanh::lean_ctor_set(v___x_389_, 9, v_maxHeartbeats_381_);
                leanh::lean_ctor_set(v___x_389_, 10, v_quotContext_382_);
                leanh::lean_ctor_set(v___x_389_, 11, v_currMacroScope_383_);
                leanh::lean_ctor_set(v___x_389_, 12, v_cancelTk_x3f_384_);
                leanh::lean_ctor_set(v___x_389_, 13, v_inheritedTraceOptions_386_);
                leanh::lean_ctor_set_uint8(
                    v___x_389_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_372_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_389_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_385_,
                );
                v___x_390_ = l_Lake_Toml_elabToml(v___x_371_, v___x_389_, v___y_387_);
                leanh::lean_dec(v___y_387_);
                leanh::lean_dec_ref_known(v___x_389_, 14);
                if leanh::lean_obj_tag(v___x_390_) == 0 {
                    leanh::lean_dec_ref(v_ictx_311_);
                    v_a_391_ = leanh::lean_ctor_get(v___x_390_, 0);
                    v_isSharedCheck_404_ = (!leanh::lean_is_exclusive(v___x_390_)) as u8;
                    if v_isSharedCheck_404_ == 0 {
                        v___x_393_ = v___x_390_;
                        v_isShared_394_ = v_isSharedCheck_404_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_391_);
                        leanh::lean_dec(v___x_390_);
                        v___x_393_ = leanh::lean_box(0);
                        v_isShared_394_ = v_isSharedCheck_404_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_362_);
                    v_a_405_ = leanh::lean_ctor_get(v___x_390_, 0);
                    v_isSharedCheck_415_ = (!leanh::lean_is_exclusive(v___x_390_)) as u8;
                    if v_isSharedCheck_415_ == 0 {
                        v___x_407_ = v___x_390_;
                        v_isShared_408_ = v_isSharedCheck_415_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_405_);
                        leanh::lean_dec(v___x_390_);
                        v___x_407_ = leanh::lean_box(0);
                        v_isShared_408_ = v_isSharedCheck_415_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_395_ = lean_st_ref_get(v___x_362_);
                leanh::lean_dec(v___x_362_);
                v_messages_396_ = leanh::lean_ctor_get(v___x_395_, 6);
                leanh::lean_inc_ref(v_messages_396_);
                leanh::lean_dec(v___x_395_);
                v___x_397_ = l_Lean_MessageLog_hasErrors(v_messages_396_);
                if v___x_397_ == 0 {
                    leanh::lean_dec_ref(v_messages_396_);
                    if v_isShared_394_ == 0 {
                        v___x_399_ = v___x_393_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_400_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_391_);
                        v___x_399_ = v_reuseFailAlloc_400_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_391_);
                    if v_isShared_394_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_393_, 1);
                        leanh::lean_ctor_set(v___x_393_, 0, v_messages_396_);
                        v___x_402_ = v___x_393_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_403_, 0, v_messages_396_);
                        v___x_402_ = v_reuseFailAlloc_403_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_399_;
            }
            7 => {
                return v___x_402_;
            }
            8 => {
                v___x_409_ = l_Lake_mkExceptionMessage(v_ictx_311_, v_a_405_);
                v___x_410_ = l_Lean_MessageLog_empty;
                v___x_411_ = l_Lean_MessageLog_add(v___x_409_, v___x_410_);
                if v_isShared_408_ == 0 {
                    leanh::lean_ctor_set(v___x_407_, 0, v___x_411_);
                    v___x_413_ = v___x_407_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
                    v___x_413_ = v_reuseFailAlloc_414_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_413_;
            }
            10 => {
                if v___y_417_ == 0 {
                    v___x_418_ = lean_st_ref_take(v___x_362_);
                    v_env_419_ = leanh::lean_ctor_get(v___x_418_, 0);
                    v_nextMacroScope_420_ = leanh::lean_ctor_get(v___x_418_, 1);
                    v_ngen_421_ = leanh::lean_ctor_get(v___x_418_, 2);
                    v_auxDeclNGen_422_ = leanh::lean_ctor_get(v___x_418_, 3);
                    v_traceState_423_ = leanh::lean_ctor_get(v___x_418_, 4);
                    v_messages_424_ = leanh::lean_ctor_get(v___x_418_, 6);
                    v_infoState_425_ = leanh::lean_ctor_get(v___x_418_, 7);
                    v_snapshotTasks_426_ = leanh::lean_ctor_get(v___x_418_, 8);
                    v_isSharedCheck_435_ = (!leanh::lean_is_exclusive(v___x_418_)) as u8;
                    if v_isSharedCheck_435_ == 0 {
                        v_unused_436_ = leanh::lean_ctor_get(v___x_418_, 5);
                        leanh::lean_dec(v_unused_436_);
                        v___x_428_ = v___x_418_;
                        v_isShared_429_ = v_isSharedCheck_435_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_426_);
                        leanh::lean_inc(v_infoState_425_);
                        leanh::lean_inc(v_messages_424_);
                        leanh::lean_inc(v_traceState_423_);
                        leanh::lean_inc(v_auxDeclNGen_422_);
                        leanh::lean_inc(v_ngen_421_);
                        leanh::lean_inc(v_nextMacroScope_420_);
                        leanh::lean_inc(v_env_419_);
                        leanh::lean_dec(v___x_418_);
                        v___x_428_ = leanh::lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_435_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___x_362_);
                    leanh::lean_inc_ref(v_fileMap_323_);
                    leanh::lean_inc_ref(v_fileName_322_);
                    v_fileName_374_ = v_fileName_322_;
                    v_fileMap_375_ = v_fileMap_323_;
                    v_currRecDepth_376_ = v___x_349_;
                    v_ref_377_ = v___x_367_;
                    v_currNamespace_378_ = v___x_325_;
                    v_openDecls_379_ = v___x_326_;
                    v_initHeartbeats_380_ = v___x_349_;
                    v_maxHeartbeats_381_ = v___x_368_;
                    v_quotContext_382_ = v___x_325_;
                    v_currMacroScope_383_ = v___x_350_;
                    v_cancelTk_x3f_384_ = v___x_370_;
                    v_suppressElabErrors_385_ = v___x_369_;
                    v_inheritedTraceOptions_386_ = v___x_364_;
                    v___y_387_ = v___x_362_;
                    state = 4;
                    continue;
                }
            }
            11 => {
                v___x_430_ = l_Lean_Kernel_enableDiag(v_env_419_, v___x_372_);
                if v_isShared_429_ == 0 {
                    leanh::lean_ctor_set(v___x_428_, 5, v___x_357_);
                    leanh::lean_ctor_set(v___x_428_, 0, v___x_430_);
                    v___x_432_ = v___x_428_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 1, v_nextMacroScope_420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 2, v_ngen_421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 3, v_auxDeclNGen_422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 4, v_traceState_423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 5, v___x_357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 6, v_messages_424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 7, v_infoState_425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 8, v_snapshotTasks_426_);
                    v___x_432_ = v_reuseFailAlloc_434_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_433_ = lean_st_ref_set(v___x_362_, v___x_432_);
                leanh::lean_inc(v___x_362_);
                leanh::lean_inc_ref(v_fileMap_323_);
                leanh::lean_inc_ref(v_fileName_322_);
                v_fileName_374_ = v_fileName_322_;
                v_fileMap_375_ = v_fileMap_323_;
                v_currRecDepth_376_ = v___x_349_;
                v_ref_377_ = v___x_367_;
                v_currNamespace_378_ = v___x_325_;
                v_openDecls_379_ = v___x_326_;
                v_initHeartbeats_380_ = v___x_349_;
                v_maxHeartbeats_381_ = v___x_368_;
                v_quotContext_382_ = v___x_325_;
                v_currMacroScope_383_ = v___x_350_;
                v_cancelTk_x3f_384_ = v___x_370_;
                v_suppressElabErrors_385_ = v___x_369_;
                v_inheritedTraceOptions_386_ = v___x_364_;
                v___y_387_ = v___x_362_;
                state = 4;
                continue;
            }
            13 => {
                v___x_443_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__22),
                    core::ptr::addr_of_mut!(l_Lake_Toml_loadToml___closed__22_once),
                    _init_l_Lake_Toml_loadToml___closed__22,
                );
                v___x_444_ = lean_io_error_to_string(v_a_439_);
                v___x_445_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_445_, 0, v___x_444_);
                v___x_446_ = l_Lean_MessageData_ofFormat(v___x_445_);
                v___x_447_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_447_, 0, v___x_443_);
                leanh::lean_ctor_set(v___x_447_, 1, v___x_446_);
                v___x_448_ = 2;
                v___x_449_ = l_Lake_mkMessageNoPos(v_ictx_311_, v___x_447_, v___x_448_);
                v___x_450_ = l_Lean_MessageLog_empty;
                v___x_451_ = l_Lean_MessageLog_add(v___x_449_, v___x_450_);
                if v_isShared_442_ == 0 {
                    leanh::lean_ctor_set(v___x_441_, 0, v___x_451_);
                    v___x_453_ = v___x_441_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
                    v___x_453_ = v_reuseFailAlloc_454_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_loadToml___boxed(
    mut v_ictx_456_: *mut leanh::LeanObject,
    mut v_a_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = l_Lake_Toml_loadToml(v_ictx_456_);
    return v_res_458_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Load(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Load(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Load(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Data_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Load(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Load(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Load(builtin);
}
// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Config
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub static l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777216 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Config(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Config(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Config(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
}

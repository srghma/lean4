// Lean compiler output
// Module: Lean.Elab.Command.Scope
// Imports: Lean.Parser.Term
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
pub static l_Lean_Elab_Command_instInhabitedScope_default___closed__0_value:
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
static mut l_Lean_Elab_Command_instInhabitedScope_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instInhabitedScope_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_instInhabitedScope_default___closed__1_value:
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
static mut l_Lean_Elab_Command_instInhabitedScope_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instInhabitedScope_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_instInhabitedScope_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_instInhabitedScope_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Command_instInhabitedScope_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Command_instInhabitedScope: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_16_: u8 = 0;
    let mut v___x_17_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_21_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16_ = 0;
    v___x_17_ = l_Lean_Elab_Command_instInhabitedScope_default___closed__1;
    v___x_18_ = leanh::lean_box(0);
    v___x_19_ = leanh::lean_box(0);
    v___x_20_ = l_Lean_Options_empty;
    v___x_21_ = l_Lean_Elab_Command_instInhabitedScope_default___closed__0;
    v___x_22_ = leanh::lean_alloc_ctor(0, 10, (3) as u32);
    leanh::lean_ctor_set(v___x_22_, 0, v___x_21_);
    leanh::lean_ctor_set(v___x_22_, 1, v___x_20_);
    leanh::lean_ctor_set(v___x_22_, 2, v___x_19_);
    leanh::lean_ctor_set(v___x_22_, 3, v___x_18_);
    leanh::lean_ctor_set(v___x_22_, 4, v___x_18_);
    leanh::lean_ctor_set(v___x_22_, 5, v___x_17_);
    leanh::lean_ctor_set(v___x_22_, 6, v___x_17_);
    leanh::lean_ctor_set(v___x_22_, 7, v___x_18_);
    leanh::lean_ctor_set(v___x_22_, 8, v___x_18_);
    leanh::lean_ctor_set(v___x_22_, 9, v___x_18_);
    leanh::lean_ctor_set_uint8(
        v___x_22_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
        v___x_16_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_22_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1) as u32,
        v___x_16_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_22_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2) as u32,
        v___x_16_,
    );
    return v___x_22_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedScope_default() -> *mut leanh::LeanObject
{
    let mut v___x_23_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_23_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_instInhabitedScope_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_instInhabitedScope_default___closed__2_once),
        _init_l_Lean_Elab_Command_instInhabitedScope_default___closed__2,
    );
    return v___x_23_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedScope() -> *mut leanh::LeanObject {
    let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_24_ = l_Lean_Elab_Command_instInhabitedScope_default;
    return v___x_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Command_Scope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Command_instInhabitedScope_default =
        _init_l_Lean_Elab_Command_instInhabitedScope_default();
    leanh::lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope_default);
    l_Lean_Elab_Command_instInhabitedScope = _init_l_Lean_Elab_Command_instInhabitedScope();
    leanh::lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Command_Scope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Command_Scope(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command_Scope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Command_Scope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Command_Scope(builtin);
}
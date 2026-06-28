// Lean compiler output
// Module: Lean.Widget.Basic
// Imports: Lean.Elab.InfoTree Lean.Server.InfoUtils
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Elab::InfoTree::{
    initialize_Lean_Elab_InfoTree, runtime_initialize_Lean_Elab_InfoTree,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, runtime_initialize_Lean_Server_InfoUtils,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
pub static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
pub static l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [73, 110, 102, 111, 87, 105, 116, 104, 67, 116, 120, 0]};
static mut l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
static l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,12741916254065433076 as *mut LeanObject] };
static mut l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instTypeNameInfoWithCtx: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject;
pub static l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 111, 99, 97, 108, 67, 111, 110, 116, 101, 120, 116, 0]};
static mut l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value) as *mut LeanObject;
static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value) as *mut LeanObject,16747314970169516704 as *mut LeanObject] };
static mut l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instTypeNameLocalContext: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_4075166457____hygCtx___hyg_3__value) as *mut LeanObject;
pub static l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 110, 116, 101, 120, 116, 73, 110, 102, 111, 0]};
static mut l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value) as *mut LeanObject;
static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value) as *mut LeanObject,8062899812902133758 as *mut LeanObject] };
static mut l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instTypeNameContextInfo: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3__value) as *mut LeanObject;
pub static l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 101, 114, 109, 73, 110, 102, 111, 0]};
static mut l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value) as *mut LeanObject;
static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value) as *mut LeanObject,7341871237032575061 as *mut LeanObject] };
static mut l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value) as *mut LeanObject;
pub static mut l_Lean_Widget_instTypeNameTermInfo: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3__value) as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Widget_Basic(builtin);
}

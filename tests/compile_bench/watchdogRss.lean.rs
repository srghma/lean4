// Lean compiler output
// Module: watchdogRss
// Imports: public import Init public meta import Init public import Lean.Data.Lsp
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Lean_JsonNumber_fromNat(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_stdin(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_FS_Stream_writeLspMessage(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_Structured_fromJson_x3f(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_int_neg(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_stdout(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_FS_Stream_readLspMessage(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_JsonRpc_instBEqRequestID_beq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Lean_JsonNumber_toString(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_instFromJsonInitializeResult_fromJson(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_compress(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_List_appendTR___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_mkObj(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_JsonNumber_fromInt(_: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_instToJsonInitializeParams_toJson(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_waitForWatchdogILeans(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_shutdown(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_waitForExit(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_runWith___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
static mut l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__0_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 32, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__1_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [44, 32, 103, 111, 116, 32, 105, 100, 32, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__1: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__2: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__3_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__3: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__4_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 115, 117, 108, 116, 32, 39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__4: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__5_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [39, 10, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__5: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__6_value: lean_string_object<35> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32, 114, 101, 115, 112, 111, 110, 115, 101, 44, 32, 103, 111, 116, 58, 32, 39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__6: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__7_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [106, 115, 111, 110, 114, 112, 99, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__7: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__8_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [50, 46, 48, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__8: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__9_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__8_value) as *mut lean_object] };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__9: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__10_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__7_value) as *mut lean_object,core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__9_value) as *mut lean_object] };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__10: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__11_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__11: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__12_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__12: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__12_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__13_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__13: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__13_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__14_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__14: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__14_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__15_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__15: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__15_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__16_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__16: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__16_value) as *mut lean_object;
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__20: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__24: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__28_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__28: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__32_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__32: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__36_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__36: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__40_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__40: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__44_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__44: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__48_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__48: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__52_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__52: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__56_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__56: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__60_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__60: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__64_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__64: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___redArg___lam__0___closed__0_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 100, 0]};
static mut l_main___redArg___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___redArg___lam__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___lam__0___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_main___redArg___lam__0___closed__0_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___redArg___lam__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___redArg___lam__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__0_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [45, 45, 115, 101, 114, 118, 101, 114, 0]};
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__2_value: lean_array_object<1> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l_main___redArg___closed__1_value) as *mut lean_object] };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__3_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___redArg___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__4_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__3_value) as *mut lean_object] };
static mut l_main___redArg___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__5_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__4_value) as *mut lean_object] };
static mut l_main___redArg___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__6_value: lean_ctor_object<3> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*3 + 0) as u16, m_other: 3, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__5_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___redArg___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__7_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 1 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__6_value) as *mut lean_object] };
static mut l_main___redArg___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__8_value: lean_ctor_object<4> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*4 + 0) as u16, m_other: 4, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_main___redArg___closed__7_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___redArg___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__8_value) as *mut lean_object;
static mut l_main___redArg___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__10: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___redArg___closed__11_value: lean_string_object<11> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_main___redArg___closed__11: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_main___redArg___closed__12_value: lean_ctor_object<7> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*6 + 8) as u16, m_other: 6, m_tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___redArg___closed__8_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object,0 as *mut lean_object] };
static mut l_main___redArg___closed__12: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__12_value) as *mut lean_object;
static mut l_main___redArg___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__14: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0() -> *mut lean_object{
let mut v___x_1_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1_);
return v___x_2_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5(mut v_v_3_: *mut lean_object) -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0_once), _init_l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5___closed__0);
return v___x_4_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3(mut v_h_5_: *mut lean_object, mut v_n_6_: *mut lean_object) -> *mut lean_object{
let mut v_method_8_: *mut lean_object = core::ptr::null_mut(); let mut v_param_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_12_: u8 = 0; let mut v___y_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v_a_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_24_: u8 = 0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_27_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_28_: u8 = 0; let mut v_isSharedCheck_29_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_method_8_ = lean_ctor_get(v_n_6_, 0);
v_param_9_ = lean_ctor_get(v_n_6_, 1);
v_isSharedCheck_29_ = (!lean_is_exclusive(v_n_6_)) as u8;
if v_isSharedCheck_29_ == 0 {
v___x_11_ = v_n_6_;
v_isShared_12_ = v_isSharedCheck_29_;
state = 1; continue;
} else {
lean_inc(v_param_9_);
lean_inc(v_method_8_);
lean_dec(v_n_6_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_29_;
state = 1; continue;
}
}
1 => {
v___x_19_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3_spec__5(v_param_9_);
if lean_obj_tag(v___x_19_) == 0 {
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_19_, 1);
v___x_20_ = lean_box(0);
v___y_14_ = v___x_20_;
state = 2; continue;
} else {
let mut v_a_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_24_: u8 = 0; let mut v_isSharedCheck_28_: u8 = 0; 
v_a_21_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_28_ = (!lean_is_exclusive(v___x_19_)) as u8;
if v_isSharedCheck_28_ == 0 {
v___x_23_ = v___x_19_;
v_isShared_24_ = v_isSharedCheck_28_;
state = 4; continue;
} else {
lean_inc(v_a_21_);
lean_dec(v___x_19_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
state = 4; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3___boxed(mut v_h_30_: *mut lean_object, mut v_n_31_: *mut lean_object, mut v_a_32_: *mut lean_object) -> *mut lean_object{
let mut v_res_33_: *mut lean_object = core::ptr::null_mut(); 
v_res_33_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3(v_h_30_, v_n_31_);
return v_res_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__2(mut v_n_34_: *mut lean_object, mut v_a_35_: *mut lean_object) -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v_a_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v___x_37_ = l_Lean_Lsp_Ipc_stdin(v_a_35_);
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__2_spec__3(v_a_38_, v_n_34_);
return v___x_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__2___boxed(mut v_n_40_: *mut lean_object, mut v_a_41_: *mut lean_object, mut v_a_42_: *mut lean_object) -> *mut lean_object{
let mut v_res_43_: *mut lean_object = core::ptr::null_mut(); 
v_res_43_ = l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__2(v_n_40_, v_a_41_);
lean_dec_ref(v_a_41_);
return v_res_43_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17() -> *mut lean_object{
let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); 
v___x_64_ = lean_unsigned_to_nat(32700);
v___x_65_ = lean_nat_to_int(v___x_64_);
return v___x_65_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18() -> *mut lean_object{
let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_66_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__17);
v___x_67_ = lean_int_neg(v___x_66_);
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19() -> *mut lean_object{
let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); 
v___x_68_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__18);
v___x_69_ = l_Lean_JsonNumber_fromInt(v___x_68_);
return v___x_69_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__20() -> *mut lean_object{
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); 
v___x_70_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__19);
v___x_71_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21() -> *mut lean_object{
let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___x_72_ = lean_unsigned_to_nat(32600);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22() -> *mut lean_object{
let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_74_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__21);
v___x_75_ = lean_int_neg(v___x_74_);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23() -> *mut lean_object{
let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); 
v___x_76_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__22);
v___x_77_ = l_Lean_JsonNumber_fromInt(v___x_76_);
return v___x_77_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__24() -> *mut lean_object{
let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); 
v___x_78_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__23);
v___x_79_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25() -> *mut lean_object{
let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); 
v___x_80_ = lean_unsigned_to_nat(32601);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26() -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__25);
v___x_83_ = lean_int_neg(v___x_82_);
return v___x_83_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27() -> *mut lean_object{
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
v___x_84_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__26);
v___x_85_ = l_Lean_JsonNumber_fromInt(v___x_84_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__28() -> *mut lean_object{
let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); 
v___x_86_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__27);
v___x_87_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29() -> *mut lean_object{
let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
v___x_88_ = lean_unsigned_to_nat(32602);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30() -> *mut lean_object{
let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); 
v___x_90_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__29);
v___x_91_ = lean_int_neg(v___x_90_);
return v___x_91_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31() -> *mut lean_object{
let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); 
v___x_92_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__30);
v___x_93_ = l_Lean_JsonNumber_fromInt(v___x_92_);
return v___x_93_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__32() -> *mut lean_object{
let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); 
v___x_94_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__31);
v___x_95_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33() -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = lean_unsigned_to_nat(32603);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34() -> *mut lean_object{
let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
v___x_98_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__33);
v___x_99_ = lean_int_neg(v___x_98_);
return v___x_99_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35() -> *mut lean_object{
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
v___x_100_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__34);
v___x_101_ = l_Lean_JsonNumber_fromInt(v___x_100_);
return v___x_101_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__36() -> *mut lean_object{
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); 
v___x_102_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__35);
v___x_103_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37() -> *mut lean_object{
let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); 
v___x_104_ = lean_unsigned_to_nat(32002);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38() -> *mut lean_object{
let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
v___x_106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__37);
v___x_107_ = lean_int_neg(v___x_106_);
return v___x_107_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39() -> *mut lean_object{
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); 
v___x_108_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__38);
v___x_109_ = l_Lean_JsonNumber_fromInt(v___x_108_);
return v___x_109_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__40() -> *mut lean_object{
let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
v___x_110_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__39);
v___x_111_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41() -> *mut lean_object{
let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
v___x_112_ = lean_unsigned_to_nat(32001);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42() -> *mut lean_object{
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); 
v___x_114_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__41);
v___x_115_ = lean_int_neg(v___x_114_);
return v___x_115_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43() -> *mut lean_object{
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
v___x_116_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__42);
v___x_117_ = l_Lean_JsonNumber_fromInt(v___x_116_);
return v___x_117_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__44() -> *mut lean_object{
let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); 
v___x_118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__43);
v___x_119_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45() -> *mut lean_object{
let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
v___x_120_ = lean_unsigned_to_nat(32801);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46() -> *mut lean_object{
let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
v___x_122_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__45);
v___x_123_ = lean_int_neg(v___x_122_);
return v___x_123_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47() -> *mut lean_object{
let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); 
v___x_124_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__46);
v___x_125_ = l_Lean_JsonNumber_fromInt(v___x_124_);
return v___x_125_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__48() -> *mut lean_object{
let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v___x_126_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__47);
v___x_127_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49() -> *mut lean_object{
let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); 
v___x_128_ = lean_unsigned_to_nat(32800);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50() -> *mut lean_object{
let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); 
v___x_130_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__49);
v___x_131_ = lean_int_neg(v___x_130_);
return v___x_131_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51() -> *mut lean_object{
let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); 
v___x_132_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__50);
v___x_133_ = l_Lean_JsonNumber_fromInt(v___x_132_);
return v___x_133_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__52() -> *mut lean_object{
let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); 
v___x_134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__51);
v___x_135_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53() -> *mut lean_object{
let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); 
v___x_136_ = lean_unsigned_to_nat(32900);
v___x_137_ = lean_nat_to_int(v___x_136_);
return v___x_137_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54() -> *mut lean_object{
let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
v___x_138_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__53);
v___x_139_ = lean_int_neg(v___x_138_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55() -> *mut lean_object{
let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); 
v___x_140_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__54);
v___x_141_ = l_Lean_JsonNumber_fromInt(v___x_140_);
return v___x_141_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__56() -> *mut lean_object{
let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); 
v___x_142_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__55);
v___x_143_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57() -> *mut lean_object{
let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); 
v___x_144_ = lean_unsigned_to_nat(32901);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58() -> *mut lean_object{
let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); 
v___x_146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__57);
v___x_147_ = lean_int_neg(v___x_146_);
return v___x_147_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59() -> *mut lean_object{
let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); 
v___x_148_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__58);
v___x_149_ = l_Lean_JsonNumber_fromInt(v___x_148_);
return v___x_149_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__60() -> *mut lean_object{
let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); 
v___x_150_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__59);
v___x_151_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61() -> *mut lean_object{
let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
v___x_152_ = lean_unsigned_to_nat(32902);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62() -> *mut lean_object{
let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); 
v___x_154_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__61);
v___x_155_ = lean_int_neg(v___x_154_);
return v___x_155_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63() -> *mut lean_object{
let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); 
v___x_156_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__62);
v___x_157_ = l_Lean_JsonNumber_fromInt(v___x_156_);
return v___x_157_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__64() -> *mut lean_object{
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v___x_158_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___closed__63);
v___x_159_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1(mut v_expectedID_160_: *mut lean_object, mut v_a_161_: *mut lean_object) -> *mut lean_object{
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v_a_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_167_: u8 = 0; let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v_a_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_172_: u8 = 0; let mut v___y_174_: *mut lean_object = core::ptr::null_mut(); let mut v___y_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); let mut v_id_181_: *mut lean_object = core::ptr::null_mut(); let mut v_result_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_185_: u8 = 0; let mut v___x_186_: u8 = 0; let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v___y_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v_s_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v___x_196_: *mut lean_object = core::ptr::null_mut(); let mut v_n_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v_s_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v_n_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v_a_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_211_: u8 = 0; let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_222_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_223_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_224_: u8 = 0; let mut v_a_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_230_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_231_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_232_: u8 = 0; let mut v_id_233_: *mut lean_object = core::ptr::null_mut(); let mut v_code_234_: u8 = 0; let mut v_message_235_: *mut lean_object = core::ptr::null_mut(); let mut v_data_x3f_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___y_240_: *mut lean_object = core::ptr::null_mut(); let mut v___y_241_: *mut lean_object = core::ptr::null_mut(); let mut v___y_242_: *mut lean_object = core::ptr::null_mut(); let mut v___y_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v___x_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v___x_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v___x_255_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v___x_257_: *mut lean_object = core::ptr::null_mut(); let mut v___x_258_: *mut lean_object = core::ptr::null_mut(); let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v___x_260_: *mut lean_object = core::ptr::null_mut(); let mut v___x_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_267_: *mut lean_object = core::ptr::null_mut(); let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); let mut v___y_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: *mut lean_object = core::ptr::null_mut(); let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); let mut v_s_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_289_: u8 = 0; let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_292_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_293_: u8 = 0; let mut v_n_294_: *mut lean_object = core::ptr::null_mut(); let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_297_: u8 = 0; let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_300_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_301_: u8 = 0; let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_304_: u8 = 0; let mut v_a_305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_308_: u8 = 0; let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_311_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_312_: u8 = 0; let mut v_isSharedCheck_313_: u8 = 0; let mut v_a_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_317_: u8 = 0; let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_320_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_321_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_163_ = l_Lean_Lsp_Ipc_stdout(v_a_161_);
if lean_obj_tag(v___x_163_) == 0 {
let mut v_a_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_167_: u8 = 0; let mut v_isSharedCheck_313_: u8 = 0; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_313_ = (!lean_is_exclusive(v___x_163_)) as u8;
if v_isSharedCheck_313_ == 0 {
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_313_;
state = 1; continue;
} else {
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_313_;
state = 1; continue;
}
} else {
let mut v_a_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_317_: u8 = 0; let mut v_isSharedCheck_321_: u8 = 0; 
lean_dec(v_expectedID_160_);
v_a_314_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_321_ = (!lean_is_exclusive(v___x_163_)) as u8;
if v_isSharedCheck_321_ == 0 {
v___x_316_ = v___x_163_;
v_isShared_317_ = v_isSharedCheck_321_;
state = 21; continue;
} else {
lean_inc(v_a_314_);
lean_dec(v___x_163_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
state = 21; continue;
}
}
}
1 => {
v___x_168_ = l_IO_FS_Stream_readLspMessage(v_a_164_);
if lean_obj_tag(v___x_168_) == 0 {
let mut v_a_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_172_: u8 = 0; let mut v_isSharedCheck_304_: u8 = 0; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_304_ = (!lean_is_exclusive(v___x_168_)) as u8;
if v_isSharedCheck_304_ == 0 {
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_304_;
state = 2; continue;
} else {
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_304_;
state = 2; continue;
}
} else {
let mut v_a_305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_308_: u8 = 0; let mut v_isSharedCheck_312_: u8 = 0; 
lean_del_object(v___x_166_);
lean_dec(v_expectedID_160_);
v_a_305_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_312_ = (!lean_is_exclusive(v___x_168_)) as u8;
if v_isSharedCheck_312_ == 0 {
v___x_307_ = v___x_168_;
v_isShared_308_ = v_isSharedCheck_312_;
state = 19; continue;
} else {
lean_inc(v_a_305_);
lean_dec(v___x_168_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
state = 19; continue;
}
}
}
21 => {
if v_isShared_317_ == 0 {
v___x_319_ = v___x_316_;
state = 22; continue;
} else {
let mut v_reuseFailAlloc_320_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
state = 22; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1___boxed(mut v_expectedID_322_: *mut lean_object, mut v_a_323_: *mut lean_object, mut v_a_324_: *mut lean_object) -> *mut lean_object{
let mut v_res_325_: *mut lean_object = core::ptr::null_mut(); 
v_res_325_ = l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1(v_expectedID_322_, v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0_spec__1(mut v_v_326_: *mut lean_object) -> *mut lean_object{
let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); 
v___x_327_ = l_Lean_Lsp_instToJsonInitializeParams_toJson(v_v_326_);
v___x_328_ = l_Lean_Json_Structured_fromJson_x3f(v___x_327_);
return v___x_328_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0(mut v_h_329_: *mut lean_object, mut v_r_330_: *mut lean_object) -> *mut lean_object{
let mut v_id_332_: *mut lean_object = core::ptr::null_mut(); let mut v_method_333_: *mut lean_object = core::ptr::null_mut(); let mut v_param_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_337_: u8 = 0; let mut v___y_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v_a_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_349_: u8 = 0; let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_352_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_353_: u8 = 0; let mut v_isSharedCheck_354_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_id_332_ = lean_ctor_get(v_r_330_, 0);
v_method_333_ = lean_ctor_get(v_r_330_, 1);
v_param_334_ = lean_ctor_get(v_r_330_, 2);
v_isSharedCheck_354_ = (!lean_is_exclusive(v_r_330_)) as u8;
if v_isSharedCheck_354_ == 0 {
v___x_336_ = v_r_330_;
v_isShared_337_ = v_isSharedCheck_354_;
state = 1; continue;
} else {
lean_inc(v_param_334_);
lean_inc(v_method_333_);
lean_inc(v_id_332_);
lean_dec(v_r_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_354_;
state = 1; continue;
}
}
1 => {
v___x_344_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0_spec__1(v_param_334_);
if lean_obj_tag(v___x_344_) == 0 {
let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_344_, 1);
v___x_345_ = lean_box(0);
v___y_339_ = v___x_345_;
state = 2; continue;
} else {
let mut v_a_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_349_: u8 = 0; let mut v_isSharedCheck_353_: u8 = 0; 
v_a_346_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = (!lean_is_exclusive(v___x_344_)) as u8;
if v_isSharedCheck_353_ == 0 {
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_353_;
state = 4; continue;
} else {
lean_inc(v_a_346_);
lean_dec(v___x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
state = 4; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0___boxed(mut v_h_355_: *mut lean_object, mut v_r_356_: *mut lean_object, mut v_a_357_: *mut lean_object) -> *mut lean_object{
let mut v_res_358_: *mut lean_object = core::ptr::null_mut(); 
v_res_358_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0(v_h_355_, v_r_356_);
return v_res_358_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeRequest___at___00main_spec__0(mut v_r_359_: *mut lean_object, mut v_a_360_: *mut lean_object) -> *mut lean_object{
let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_a_363_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); 
v___x_362_ = l_Lean_Lsp_Ipc_stdin(v_a_360_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_362_);
v___x_364_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00main_spec__0_spec__0(v_a_363_, v_r_359_);
return v___x_364_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeRequest___at___00main_spec__0___boxed(mut v_r_365_: *mut lean_object, mut v_a_366_: *mut lean_object, mut v_a_367_: *mut lean_object) -> *mut lean_object{
let mut v_res_368_: *mut lean_object = core::ptr::null_mut(); 
v_res_368_ = l_Lean_Lsp_Ipc_writeRequest___at___00main_spec__0(v_r_365_, v_a_366_);
lean_dec_ref(v_a_366_);
return v_res_368_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___lam__0(mut v___x_373_: *mut lean_object, mut v___x_374_: *mut lean_object, mut v___x_375_: *mut lean_object, mut v___y_376_: *mut lean_object) -> *mut lean_object{
let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_384_: u8 = 0; let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_394_: u8 = 0; let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_398_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_399_: u8 = 0; let mut v_unused_400_: *mut lean_object = core::ptr::null_mut(); let mut v_a_401_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_404_: u8 = 0; let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_407_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_408_: u8 = 0; let mut v_reuseFailAlloc_409_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_410_: u8 = 0; let mut v_unused_411_: *mut lean_object = core::ptr::null_mut(); let mut v_a_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_415_: u8 = 0; let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_418_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_419_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_378_ = l_Lean_Lsp_Ipc_writeRequest___at___00main_spec__0(v___x_373_, v___y_376_);
if lean_obj_tag(v___x_378_) == 0 {
let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_378_, 1);
v___x_379_ = l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__1(v___x_374_, v___y_376_);
if lean_obj_tag(v___x_379_) == 0 {
let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_main___redArg___lam__0___closed__1;
v___x_381_ = l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__2(v___x_380_, v___y_376_);
if lean_obj_tag(v___x_381_) == 0 {
let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_384_: u8 = 0; let mut v_isSharedCheck_410_: u8 = 0; 
v_isSharedCheck_410_ = (!lean_is_exclusive(v___x_381_)) as u8;
if v_isSharedCheck_410_ == 0 {
let mut v_unused_411_: *mut lean_object = core::ptr::null_mut(); 
v_unused_411_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_411_);
v___x_383_ = v___x_381_;
v_isShared_384_ = v_isSharedCheck_410_;
state = 1; continue;
} else {
lean_dec(v___x_381_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_410_;
state = 1; continue;
}
} else {
lean_dec(v___x_375_);
return v___x_381_;
}
} else {
let mut v_a_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_415_: u8 = 0; let mut v_isSharedCheck_419_: u8 = 0; 
lean_dec(v___x_375_);
v_a_412_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_419_ = (!lean_is_exclusive(v___x_379_)) as u8;
if v_isSharedCheck_419_ == 0 {
v___x_414_ = v___x_379_;
v_isShared_415_ = v_isSharedCheck_419_;
state = 7; continue;
} else {
lean_inc(v_a_412_);
lean_dec(v___x_379_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
state = 7; continue;
}
}
} else {
lean_dec(v___x_375_);
lean_dec(v___x_374_);
return v___x_378_;
}
}
1 => {
v___x_385_ = l_Lean_JsonNumber_fromNat(v___x_375_);
if v_isShared_384_ == 0 {
lean_ctor_set_tag(v___x_383_, 1);
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_409_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_409_;
state = 2; continue;
}
}
7 => {
if v_isShared_415_ == 0 {
v___x_417_ = v___x_414_;
state = 8; continue;
} else {
let mut v_reuseFailAlloc_418_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
state = 8; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___lam__0___boxed(mut v___x_420_: *mut lean_object, mut v___x_421_: *mut lean_object, mut v___x_422_: *mut lean_object, mut v___y_423_: *mut lean_object, mut v___y_424_: *mut lean_object) -> *mut lean_object{
let mut v_res_425_: *mut lean_object = core::ptr::null_mut(); 
v_res_425_ = l_main___redArg___lam__0(v___x_420_, v___x_421_, v___x_422_, v___y_423_);
lean_dec_ref(v___y_423_);
return v_res_425_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__9() -> *mut lean_object{
let mut v___x_447_: *mut lean_object = core::ptr::null_mut(); let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); 
v___x_447_ = lean_unsigned_to_nat(0);
v___x_448_ = l_Lean_JsonNumber_fromNat(v___x_447_);
return v___x_448_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__10() -> *mut lean_object{
let mut v___x_449_: *mut lean_object = core::ptr::null_mut(); let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); 
v___x_449_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__9), core::ptr::addr_of_mut!(l_main___redArg___closed__9_once), _init_l_main___redArg___closed__9);
v___x_450_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__13() -> *mut lean_object{
let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); let mut v___x_458_: *mut lean_object = core::ptr::null_mut(); let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); 
v___x_456_ = l_main___redArg___closed__12;
v___x_457_ = l_main___redArg___closed__11;
v___x_458_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__10), core::ptr::addr_of_mut!(l_main___redArg___closed__10_once), _init_l_main___redArg___closed__10);
v___x_459_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_456_);
return v___x_459_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__14() -> *mut lean_object{
let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); let mut v___x_461_: *mut lean_object = core::ptr::null_mut(); let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); let mut v___f_463_: *mut lean_object = core::ptr::null_mut(); 
v___x_460_ = lean_unsigned_to_nat(1);
v___x_461_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__10), core::ptr::addr_of_mut!(l_main___redArg___closed__10_once), _init_l_main___redArg___closed__10);
v___x_462_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__13), core::ptr::addr_of_mut!(l_main___redArg___closed__13_once), _init_l_main___redArg___closed__13);
v___f_463_ = lean_alloc_closure(l_main___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
lean_closure_set(v___f_463_, 0, v___x_462_);
lean_closure_set(v___f_463_, 1, v___x_461_);
lean_closure_set(v___f_463_, 2, v___x_460_);
return v___f_463_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v___x_466_: *mut lean_object = core::ptr::null_mut(); let mut v___f_467_: *mut lean_object = core::ptr::null_mut(); let mut v___x_468_: *mut lean_object = core::ptr::null_mut(); 
v___x_465_ = l_main___redArg___closed__0;
v___x_466_ = l_main___redArg___closed__2;
v___f_467_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__14), core::ptr::addr_of_mut!(l_main___redArg___closed__14_once), _init_l_main___redArg___closed__14);
v___x_468_ = l_Lean_Lsp_Ipc_runWith___redArg(v___x_465_, v___x_466_, v___f_467_);
return v___x_468_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_469_: *mut lean_object) -> *mut lean_object{
let mut v_res_470_: *mut lean_object = core::ptr::null_mut(); 
v_res_470_ = l_main___redArg();
return v_res_470_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_x_471_: *mut lean_object) -> *mut lean_object{
let mut v___x_473_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_471_);
v___x_473_ = l_main___redArg();
return v___x_473_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_x_474_: *mut lean_object, mut v_a_475_: *mut lean_object) -> *mut lean_object{
let mut v_res_476_: *mut lean_object = core::ptr::null_mut(); 
v_res_476_ = _lean_main(v_x_474_);
return v_res_476_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_Lsp(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_watchdogRss(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 {
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return _lean_main(args_list);
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  let res = initialize_watchdogRss(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = 0;
      lean_dec(main_res);
    } else {
      lean_io_result_show_error(main_res);
      lean_dec(main_res);
    }
  } else {
    lean_io_result_show_error(res);
    lean_dec(res);
  }
  return ret_val;
}

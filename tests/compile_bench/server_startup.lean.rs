// Lean compiler output
// Module: server_startup
// Imports: public import Init public meta import Init public import Lean.Data.Lsp
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_int_neg(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_JsonNumber_fromInt(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_stdin(_: *mut lean_object) -> *mut lean_object;
    fn l_IO_FS_readBinFile(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_JsonNumber_fromNat(_: *mut lean_object) -> *mut lean_object;
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
    fn l_IO_FS_Stream_writeLspMessage(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Json_Structured_fromJson_x3f(_: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_shutdown(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Lean_Lsp_Ipc_runWith___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__0_value: lean_string_object<13> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 32, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__1_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [44, 32, 103, 111, 116, 32, 105, 100, 32, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__3_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__3: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__4_value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 115, 117, 108, 116, 32, 39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__4: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__5_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [39, 10, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__5: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__6_value: lean_string_object<35> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32, 114, 101, 115, 112, 111, 110, 115, 101, 44, 32, 103, 111, 116, 58, 32, 39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__6: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__7_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [106, 115, 111, 110, 114, 112, 99, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__7: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__8_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [50, 46, 48, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__8: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__9_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__8_value) as *mut lean_object] };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__9: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__10_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__7_value) as *mut lean_object,core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__9_value) as *mut lean_object] };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__10: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__10_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__11_value: lean_string_object<8> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__11: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__11_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__12_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__12: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__12_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__13_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__13: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__13_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__14_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__14: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__14_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__15_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__15: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__15_value) as *mut lean_object;
#[no_mangle] pub static l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__16_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__16: *mut lean_object = core::ptr::addr_of!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__16_value) as *mut lean_object;
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__20: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__24: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__28_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__28: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__32_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__32: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__36_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__36: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__40_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__40: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__44_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__44: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__48_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__48: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__52_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__52: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__56_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__56: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__60_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__60: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__64_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__64: *mut lean_object = core::ptr::null_mut();
static mut l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___lam__0___closed__0_value: lean_string_object<24> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 101, 114, 118, 101, 114, 95, 115, 116, 97, 114, 116, 117, 112, 46, 108, 101, 97, 110, 46, 108, 111, 103, 0]};
static mut l_main___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___lam__0___closed__0_value) as *mut lean_object;
static mut l_main___lam__0___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__0___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___lam__0___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__0___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___lam__0___closed__3_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 100, 0]};
static mut l_main___lam__0___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___lam__0___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_main___lam__0___closed__4_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_main___lam__0___closed__3_value) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___lam__0___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___lam__0___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [45, 45, 115, 101, 114, 118, 101, 114, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_closure_object<1> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_array_object<1> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17() -> *mut lean_object{
let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_21_ = lean_unsigned_to_nat(32700);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18() -> *mut lean_object{
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_23_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__17);
v___x_24_ = lean_int_neg(v___x_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19() -> *mut lean_object{
let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_25_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__18);
v___x_26_ = l_Lean_JsonNumber_fromInt(v___x_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__20() -> *mut lean_object{
let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_27_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__19);
v___x_28_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21() -> *mut lean_object{
let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); 
v___x_29_ = lean_unsigned_to_nat(32600);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22() -> *mut lean_object{
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_31_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__21);
v___x_32_ = lean_int_neg(v___x_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23() -> *mut lean_object{
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v___x_33_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__22);
v___x_34_ = l_Lean_JsonNumber_fromInt(v___x_33_);
return v___x_34_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__24() -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__23);
v___x_36_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25() -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
v___x_37_ = lean_unsigned_to_nat(32601);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26() -> *mut lean_object{
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_39_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__25);
v___x_40_ = lean_int_neg(v___x_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27() -> *mut lean_object{
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__26);
v___x_42_ = l_Lean_JsonNumber_fromInt(v___x_41_);
return v___x_42_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__28() -> *mut lean_object{
let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_43_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__27);
v___x_44_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29() -> *mut lean_object{
let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
v___x_45_ = lean_unsigned_to_nat(32602);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30() -> *mut lean_object{
let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_47_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__29);
v___x_48_ = lean_int_neg(v___x_47_);
return v___x_48_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31() -> *mut lean_object{
let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v___x_49_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__30);
v___x_50_ = l_Lean_JsonNumber_fromInt(v___x_49_);
return v___x_50_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__32() -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); 
v___x_51_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__31);
v___x_52_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33() -> *mut lean_object{
let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); 
v___x_53_ = lean_unsigned_to_nat(32603);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34() -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__33);
v___x_56_ = lean_int_neg(v___x_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35() -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__34);
v___x_58_ = l_Lean_JsonNumber_fromInt(v___x_57_);
return v___x_58_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__36() -> *mut lean_object{
let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_59_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__35);
v___x_60_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37() -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = lean_unsigned_to_nat(32002);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38() -> *mut lean_object{
let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); 
v___x_63_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__37);
v___x_64_ = lean_int_neg(v___x_63_);
return v___x_64_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39() -> *mut lean_object{
let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); 
v___x_65_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__38);
v___x_66_ = l_Lean_JsonNumber_fromInt(v___x_65_);
return v___x_66_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__40() -> *mut lean_object{
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); 
v___x_67_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__39);
v___x_68_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41() -> *mut lean_object{
let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); 
v___x_69_ = lean_unsigned_to_nat(32001);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42() -> *mut lean_object{
let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); 
v___x_71_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__41);
v___x_72_ = lean_int_neg(v___x_71_);
return v___x_72_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43() -> *mut lean_object{
let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__42);
v___x_74_ = l_Lean_JsonNumber_fromInt(v___x_73_);
return v___x_74_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__44() -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__43);
v___x_76_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45() -> *mut lean_object{
let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); 
v___x_77_ = lean_unsigned_to_nat(32801);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46() -> *mut lean_object{
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
v___x_79_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__45);
v___x_80_ = lean_int_neg(v___x_79_);
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47() -> *mut lean_object{
let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_81_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__46);
v___x_82_ = l_Lean_JsonNumber_fromInt(v___x_81_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__48() -> *mut lean_object{
let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); 
v___x_83_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__47);
v___x_84_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49() -> *mut lean_object{
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = lean_unsigned_to_nat(32800);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50() -> *mut lean_object{
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__49);
v___x_88_ = lean_int_neg(v___x_87_);
return v___x_88_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51() -> *mut lean_object{
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
v___x_89_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__50);
v___x_90_ = l_Lean_JsonNumber_fromInt(v___x_89_);
return v___x_90_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__52() -> *mut lean_object{
let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); 
v___x_91_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__51);
v___x_92_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53() -> *mut lean_object{
let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); 
v___x_93_ = lean_unsigned_to_nat(32900);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54() -> *mut lean_object{
let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); 
v___x_95_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__53);
v___x_96_ = lean_int_neg(v___x_95_);
return v___x_96_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55() -> *mut lean_object{
let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); 
v___x_97_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__54);
v___x_98_ = l_Lean_JsonNumber_fromInt(v___x_97_);
return v___x_98_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__56() -> *mut lean_object{
let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
v___x_99_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__55);
v___x_100_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57() -> *mut lean_object{
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = lean_unsigned_to_nat(32901);
v___x_102_ = lean_nat_to_int(v___x_101_);
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58() -> *mut lean_object{
let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); 
v___x_103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__57);
v___x_104_ = lean_int_neg(v___x_103_);
return v___x_104_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59() -> *mut lean_object{
let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); 
v___x_105_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__58);
v___x_106_ = l_Lean_JsonNumber_fromInt(v___x_105_);
return v___x_106_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__60() -> *mut lean_object{
let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); 
v___x_107_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__59);
v___x_108_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61() -> *mut lean_object{
let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); 
v___x_109_ = lean_unsigned_to_nat(32902);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62() -> *mut lean_object{
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v___x_111_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__61);
v___x_112_ = lean_int_neg(v___x_111_);
return v___x_112_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63() -> *mut lean_object{
let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
v___x_113_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__62);
v___x_114_ = l_Lean_JsonNumber_fromInt(v___x_113_);
return v___x_114_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__64() -> *mut lean_object{
let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); 
v___x_115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63), core::ptr::addr_of_mut!(l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63_once), _init_l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___closed__63);
v___x_116_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0(mut v_expectedID_117_: *mut lean_object, mut v_a_118_: *mut lean_object) -> *mut lean_object{
let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v_a_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_129_: u8 = 0; let mut v___y_131_: *mut lean_object = core::ptr::null_mut(); let mut v___y_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_137_: *mut lean_object = core::ptr::null_mut(); let mut v_id_138_: *mut lean_object = core::ptr::null_mut(); let mut v_result_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_142_: u8 = 0; let mut v___x_143_: u8 = 0; let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___y_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); let mut v_s_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v_n_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v_s_157_: *mut lean_object = core::ptr::null_mut(); let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v_n_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v_a_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_168_: u8 = 0; let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_179_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_180_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_181_: u8 = 0; let mut v_a_182_: *mut lean_object = core::ptr::null_mut(); let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_187_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_188_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_189_: u8 = 0; let mut v_id_190_: *mut lean_object = core::ptr::null_mut(); let mut v_code_191_: u8 = 0; let mut v_message_192_: *mut lean_object = core::ptr::null_mut(); let mut v_data_x3f_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: *mut lean_object = core::ptr::null_mut(); let mut v___x_195_: *mut lean_object = core::ptr::null_mut(); let mut v___y_197_: *mut lean_object = core::ptr::null_mut(); let mut v___y_198_: *mut lean_object = core::ptr::null_mut(); let mut v___y_199_: *mut lean_object = core::ptr::null_mut(); let mut v___y_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_216_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v___x_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_219_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: *mut lean_object = core::ptr::null_mut(); let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); let mut v___y_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); let mut v___x_233_: *mut lean_object = core::ptr::null_mut(); let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); let mut v___x_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: *mut lean_object = core::ptr::null_mut(); let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v___x_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v_s_243_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_246_: u8 = 0; let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_249_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_250_: u8 = 0; let mut v_n_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_254_: u8 = 0; let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_258_: u8 = 0; let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_261_: u8 = 0; let mut v_a_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_265_: u8 = 0; let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_268_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_269_: u8 = 0; let mut v_isSharedCheck_270_: u8 = 0; let mut v_a_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_274_: u8 = 0; let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_277_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_278_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_120_ = l_Lean_Lsp_Ipc_stdout(v_a_118_);
if lean_obj_tag(v___x_120_) == 0 {
let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v_isSharedCheck_270_: u8 = 0; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_270_ = (!lean_is_exclusive(v___x_120_)) as u8;
if v_isSharedCheck_270_ == 0 {
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_270_;
state = 1; continue;
} else {
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_270_;
state = 1; continue;
}
} else {
let mut v_a_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_274_: u8 = 0; let mut v_isSharedCheck_278_: u8 = 0; 
lean_dec(v_expectedID_117_);
v_a_271_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_278_ = (!lean_is_exclusive(v___x_120_)) as u8;
if v_isSharedCheck_278_ == 0 {
v___x_273_ = v___x_120_;
v_isShared_274_ = v_isSharedCheck_278_;
state = 21; continue;
} else {
lean_inc(v_a_271_);
lean_dec(v___x_120_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
state = 21; continue;
}
}
}
1 => {
v___x_125_ = l_IO_FS_Stream_readLspMessage(v_a_121_);
if lean_obj_tag(v___x_125_) == 0 {
let mut v_a_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_129_: u8 = 0; let mut v_isSharedCheck_261_: u8 = 0; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_261_ = (!lean_is_exclusive(v___x_125_)) as u8;
if v_isSharedCheck_261_ == 0 {
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_261_;
state = 2; continue;
} else {
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_261_;
state = 2; continue;
}
} else {
let mut v_a_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_265_: u8 = 0; let mut v_isSharedCheck_269_: u8 = 0; 
lean_del_object(v___x_123_);
lean_dec(v_expectedID_117_);
v_a_262_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_269_ = (!lean_is_exclusive(v___x_125_)) as u8;
if v_isSharedCheck_269_ == 0 {
v___x_264_ = v___x_125_;
v_isShared_265_ = v_isSharedCheck_269_;
state = 19; continue;
} else {
lean_inc(v_a_262_);
lean_dec(v___x_125_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
state = 19; continue;
}
}
}
21 => {
if v_isShared_274_ == 0 {
v___x_276_ = v___x_273_;
state = 22; continue;
} else {
let mut v_reuseFailAlloc_277_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
state = 22; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0___boxed(mut v_expectedID_279_: *mut lean_object, mut v_a_280_: *mut lean_object, mut v_a_281_: *mut lean_object) -> *mut lean_object{
let mut v_res_282_: *mut lean_object = core::ptr::null_mut(); 
v_res_282_ = l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0(v_expectedID_279_, v_a_280_);
lean_dec_ref(v_a_280_);
return v_res_282_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0() -> *mut lean_object{
let mut v___x_283_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); 
v___x_283_ = lean_box(0);
v___x_284_ = l_Lean_Json_Structured_fromJson_x3f(v___x_283_);
return v___x_284_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2(mut v_v_285_: *mut lean_object) -> *mut lean_object{
let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); 
v___x_286_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0_once), _init_l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2___closed__0);
return v___x_286_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1(mut v_h_287_: *mut lean_object, mut v_n_288_: *mut lean_object) -> *mut lean_object{
let mut v_method_290_: *mut lean_object = core::ptr::null_mut(); let mut v_param_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_294_: u8 = 0; let mut v___y_296_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v_a_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v___x_308_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_309_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_310_: u8 = 0; let mut v_isSharedCheck_311_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_method_290_ = lean_ctor_get(v_n_288_, 0);
v_param_291_ = lean_ctor_get(v_n_288_, 1);
v_isSharedCheck_311_ = (!lean_is_exclusive(v_n_288_)) as u8;
if v_isSharedCheck_311_ == 0 {
v___x_293_ = v_n_288_;
v_isShared_294_ = v_isSharedCheck_311_;
state = 1; continue;
} else {
lean_inc(v_param_291_);
lean_inc(v_method_290_);
lean_dec(v_n_288_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
state = 1; continue;
}
}
1 => {
v___x_301_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1_spec__2(v_param_291_);
if lean_obj_tag(v___x_301_) == 0 {
let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_301_, 1);
v___x_302_ = lean_box(0);
v___y_296_ = v___x_302_;
state = 2; continue;
} else {
let mut v_a_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_306_: u8 = 0; let mut v_isSharedCheck_310_: u8 = 0; 
v_a_303_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_310_ = (!lean_is_exclusive(v___x_301_)) as u8;
if v_isSharedCheck_310_ == 0 {
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_310_;
state = 4; continue;
} else {
lean_inc(v_a_303_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
state = 4; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1___boxed(mut v_h_312_: *mut lean_object, mut v_n_313_: *mut lean_object, mut v_a_314_: *mut lean_object) -> *mut lean_object{
let mut v_res_315_: *mut lean_object = core::ptr::null_mut(); 
v_res_315_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1(v_h_312_, v_n_313_);
return v_res_315_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__1(mut v_n_316_: *mut lean_object, mut v_a_317_: *mut lean_object) -> *mut lean_object{
let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v_a_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: *mut lean_object = core::ptr::null_mut(); 
v___x_319_ = l_Lean_Lsp_Ipc_stdin(v_a_317_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___x_319_);
v___x_321_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_writeNotification___at___00main_spec__1_spec__1(v_a_320_, v_n_316_);
return v___x_321_;
}
#[no_mangle] pub unsafe extern "C" fn l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__1___boxed(mut v_n_322_: *mut lean_object, mut v_a_323_: *mut lean_object, mut v_a_324_: *mut lean_object) -> *mut lean_object{
let mut v_res_325_: *mut lean_object = core::ptr::null_mut(); 
v_res_325_ = l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__1(v_n_322_, v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__0___closed__1() -> *mut lean_object{
let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); 
v___x_327_ = lean_unsigned_to_nat(0);
v___x_328_ = l_Lean_JsonNumber_fromNat(v___x_327_);
return v___x_328_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__0___closed__2() -> *mut lean_object{
let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); 
v___x_329_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__0___closed__1), core::ptr::addr_of_mut!(l_main___lam__0___closed__1_once), _init_l_main___lam__0___closed__1);
v___x_330_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v___x_335_: *mut lean_object, mut v___y_336_: *mut lean_object) -> *mut lean_object{
let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v_a_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v_a_342_: *mut lean_object = core::ptr::null_mut(); let mut v_flush_343_: *mut lean_object = core::ptr::null_mut(); let mut v_write_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v_a_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_355_: u8 = 0; let mut v___x_357_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_358_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_359_: u8 = 0; let mut v_a_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_363_: u8 = 0; let mut v___x_365_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_366_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_367_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_338_ = l_Lean_Lsp_Ipc_stdin(v___y_336_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_main___lam__0___closed__0;
v___x_341_ = l_IO_FS_readBinFile(v___x_340_);
if lean_obj_tag(v___x_341_) == 0 {
let mut v_a_342_: *mut lean_object = core::ptr::null_mut(); let mut v_flush_343_: *mut lean_object = core::ptr::null_mut(); let mut v_write_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v_flush_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc_ref(v_flush_343_);
v_write_344_ = lean_ctor_get(v_a_339_, 2);
lean_inc_ref(v_write_344_);
lean_dec(v_a_339_);
v___x_345_ = lean_apply_2(v_write_344_, v_a_342_, lean_box(0));
if lean_obj_tag(v___x_345_) == 0 {
let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_345_, 1);
v___x_346_ = lean_apply_1(v_flush_343_, lean_box(0));
if lean_obj_tag(v___x_346_) == 0 {
let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_346_, 1);
v___x_347_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__0___closed__2), core::ptr::addr_of_mut!(l_main___lam__0___closed__2_once), _init_l_main___lam__0___closed__2);
v___x_348_ = l_Lean_Lsp_Ipc_readResponseAs___at___00main_spec__0(v___x_347_, v___y_336_);
if lean_obj_tag(v___x_348_) == 0 {
let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_348_, 1);
v___x_349_ = l_main___lam__0___closed__4;
v___x_350_ = l_Lean_Lsp_Ipc_writeNotification___at___00main_spec__1(v___x_349_, v___y_336_);
if lean_obj_tag(v___x_350_) == 0 {
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_350_, 1);
v___x_351_ = l_Lean_Lsp_Ipc_shutdown(v___x_335_, v___y_336_);
return v___x_351_;
} else {
lean_dec(v___x_335_);
return v___x_350_;
}
} else {
let mut v_a_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_354_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_355_: u8 = 0; let mut v_isSharedCheck_359_: u8 = 0; 
lean_dec(v___x_335_);
v_a_352_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_359_ = (!lean_is_exclusive(v___x_348_)) as u8;
if v_isSharedCheck_359_ == 0 {
v___x_354_ = v___x_348_;
v_isShared_355_ = v_isSharedCheck_359_;
state = 1; continue;
} else {
lean_inc(v_a_352_);
lean_dec(v___x_348_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
state = 1; continue;
}
}
} else {
lean_dec(v___x_335_);
return v___x_346_;
}
} else {
lean_dec_ref(v_flush_343_);
lean_dec(v___x_335_);
return v___x_345_;
}
} else {
let mut v_a_360_: *mut lean_object = core::ptr::null_mut(); let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_363_: u8 = 0; let mut v_isSharedCheck_367_: u8 = 0; 
lean_dec(v_a_339_);
lean_dec(v___x_335_);
v_a_360_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_367_ = (!lean_is_exclusive(v___x_341_)) as u8;
if v_isSharedCheck_367_ == 0 {
v___x_362_ = v___x_341_;
v_isShared_363_ = v_isSharedCheck_367_;
state = 3; continue;
} else {
lean_inc(v_a_360_);
lean_dec(v___x_341_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_355_ == 0 {
v___x_357_ = v___x_354_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_358_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
state = 2; continue;
}
}
3 => {
if v_isShared_363_ == 0 {
v___x_365_ = v___x_362_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_366_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v___x_368_: *mut lean_object, mut v___y_369_: *mut lean_object, mut v___y_370_: *mut lean_object) -> *mut lean_object{
let mut v_res_371_: *mut lean_object = core::ptr::null_mut(); 
v_res_371_ = l_main___lam__0(v___x_368_, v___y_369_);
lean_dec_ref(v___y_369_);
return v_res_371_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___f_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); 
v___x_381_ = l_main___closed__0;
v___f_382_ = l_main___closed__2;
v___x_383_ = l_main___closed__3;
v___x_384_ = l_Lean_Lsp_Ipc_runWith___redArg(v___x_381_, v___x_383_, v___f_382_);
return v___x_384_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_385_: *mut lean_object) -> *mut lean_object{
let mut v_res_386_: *mut lean_object = core::ptr::null_mut(); 
v_res_386_ = _lean_main();
return v_res_386_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
extern "C" { fn initialize_Lean_Data_Lsp(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_server__startup(builtin: u8) -> *mut lean_object {
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
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  let res = initialize_server__startup(1 /* builtin */);
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

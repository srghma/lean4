// Lean compiler output
// Module: Std.Internal.UV.TCP
// Imports: Init.System.Promise Init.Data.SInt Std.Net
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
use crate::ffi::{
    lean_uv_tcp_accept, lean_uv_tcp_bind, lean_uv_tcp_cancel_accept, lean_uv_tcp_cancel_recv,
    lean_uv_tcp_connect, lean_uv_tcp_getpeername, lean_uv_tcp_getsockname, lean_uv_tcp_keepalive,
    lean_uv_tcp_listen, lean_uv_tcp_new, lean_uv_tcp_nodelay, lean_uv_tcp_recv, lean_uv_tcp_send,
    lean_uv_tcp_shutdown, lean_uv_tcp_try_accept, lean_uv_tcp_wait_readable,
};
pub static mut l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl()
-> *mut crate::leanh::LeanObject {
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_98_ = crate::leanh::lean_box(0);
    return v___x_98_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_new___boxed(
    mut v_a_00___x40___internal___hyg_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_101_ = lean_uv_tcp_new();
    return v_res_101_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_connect___boxed(
    mut v_socket_105_: *mut crate::leanh::LeanObject,
    mut v_addr_106_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_108_ = lean_uv_tcp_connect(v_socket_105_, v_addr_106_);
    crate::leanh::lean_dec_ref(v_addr_106_);
    crate::leanh::lean_dec(v_socket_105_);
    return v_res_108_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_send___boxed(
    mut v_socket_112_: *mut crate::leanh::LeanObject,
    mut v_data_113_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_115_ = lean_uv_tcp_send(v_socket_112_, v_data_113_);
    crate::leanh::lean_dec(v_socket_112_);
    return v_res_115_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(
    mut v_socket_119_: *mut crate::leanh::LeanObject,
    mut v_size_120_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_122_: u64 = 0;
    let mut v_res_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_122_ = crate::leanh::lean_unbox_uint64(v_size_120_);
    crate::leanh::lean_dec_ref(v_size_120_);
    v_res_123_ = lean_uv_tcp_recv(v_socket_119_, v_size_boxed_122_);
    crate::leanh::lean_dec(v_socket_119_);
    return v_res_123_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(
    mut v_socket_126_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = lean_uv_tcp_wait_readable(v_socket_126_);
    crate::leanh::lean_dec(v_socket_126_);
    return v_res_128_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(
    mut v_socket_131_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = lean_uv_tcp_cancel_recv(v_socket_131_);
    crate::leanh::lean_dec(v_socket_131_);
    return v_res_133_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_bind___boxed(
    mut v_socket_137_: *mut crate::leanh::LeanObject,
    mut v_addr_138_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_140_ = lean_uv_tcp_bind(v_socket_137_, v_addr_138_);
    crate::leanh::lean_dec_ref(v_addr_138_);
    crate::leanh::lean_dec(v_socket_137_);
    return v_res_140_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_listen___boxed(
    mut v_socket_144_: *mut crate::leanh::LeanObject,
    mut v_backlog_145_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_backlog_boxed_147_: u32 = 0;
    let mut v_res_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_147_ = crate::leanh::lean_unbox_uint32(v_backlog_145_);
    crate::leanh::lean_dec(v_backlog_145_);
    v_res_148_ = lean_uv_tcp_listen(v_socket_144_, v_backlog_boxed_147_);
    crate::leanh::lean_dec(v_socket_144_);
    return v_res_148_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_accept___boxed(
    mut v_socket_151_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_153_ = lean_uv_tcp_accept(v_socket_151_);
    crate::leanh::lean_dec(v_socket_151_);
    return v_res_153_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(
    mut v_socket_156_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = lean_uv_tcp_try_accept(v_socket_156_);
    crate::leanh::lean_dec(v_socket_156_);
    return v_res_158_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(
    mut v_socket_161_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ = lean_uv_tcp_cancel_accept(v_socket_161_);
    crate::leanh::lean_dec(v_socket_161_);
    return v_res_163_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_shutdown___boxed(
    mut v_socket_166_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = lean_uv_tcp_shutdown(v_socket_166_);
    crate::leanh::lean_dec(v_socket_166_);
    return v_res_168_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(
    mut v_socket_171_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_173_ = lean_uv_tcp_getpeername(v_socket_171_);
    crate::leanh::lean_dec(v_socket_171_);
    return v_res_173_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_getSockName___boxed(
    mut v_socket_176_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_178_ = lean_uv_tcp_getsockname(v_socket_176_);
    crate::leanh::lean_dec(v_socket_176_);
    return v_res_178_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_noDelay___boxed(
    mut v_socket_181_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_183_ = lean_uv_tcp_nodelay(v_socket_181_);
    crate::leanh::lean_dec(v_socket_181_);
    return v_res_183_;
}
pub unsafe fn l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(
    mut v_socket_188_: *mut crate::leanh::LeanObject,
    mut v_enable_189_: *mut crate::leanh::LeanObject,
    mut v_delay_190_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_192_: u8 = 0;
    let mut v_delay_boxed_193_: u32 = 0;
    let mut v_res_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_192_ = (crate::leanh::lean_unbox(v_enable_189_) as u8);
    v_delay_boxed_193_ = crate::leanh::lean_unbox_uint32(v_delay_190_);
    crate::leanh::lean_dec(v_delay_190_);
    v_res_194_ = lean_uv_tcp_keepalive(v_socket_188_, v_enable_boxed_192_, v_delay_boxed_193_);
    crate::leanh::lean_dec(v_socket_188_);
    return v_res_194_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl =
        _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_TCP(builtin);
}

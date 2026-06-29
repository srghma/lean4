// Lean compiler output
// Module: Std.Internal.UV.UDP
// Imports: Init.System.Promise Std.Net
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
use crate::lean_imports_rs::Std::Internal::UV::UDP::{
    lean_uv_udp_bind, lean_uv_udp_cancel_recv, lean_uv_udp_connect, lean_uv_udp_getpeername,
    lean_uv_udp_getsockname, lean_uv_udp_new, lean_uv_udp_recv, lean_uv_udp_send,
    lean_uv_udp_set_broadcast, lean_uv_udp_set_membership, lean_uv_udp_set_multicast_interface,
    lean_uv_udp_set_multicast_loop, lean_uv_udp_set_multicast_ttl, lean_uv_udp_set_ttl,
    lean_uv_udp_wait_readable,
};
pub static mut l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl()
-> *mut crate::leanh::LeanObject {
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_107_ = crate::leanh::lean_box(0);
    return v___x_107_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_new___boxed(
    mut v_a_00___x40___internal___hyg_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = lean_uv_udp_new();
    return v_res_110_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_bind___boxed(
    mut v_socket_114_: *mut crate::leanh::LeanObject,
    mut v_addr_115_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_117_ = lean_uv_udp_bind(v_socket_114_, v_addr_115_);
    crate::leanh::lean_dec_ref(v_addr_115_);
    crate::leanh::lean_dec(v_socket_114_);
    return v_res_117_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_connect___boxed(
    mut v_socket_121_: *mut crate::leanh::LeanObject,
    mut v_addr_122_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_124_ = lean_uv_udp_connect(v_socket_121_, v_addr_122_);
    crate::leanh::lean_dec_ref(v_addr_122_);
    crate::leanh::lean_dec(v_socket_121_);
    return v_res_124_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_send___boxed(
    mut v_socket_129_: *mut crate::leanh::LeanObject,
    mut v_data_130_: *mut crate::leanh::LeanObject,
    mut v_addr_131_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = lean_uv_udp_send(v_socket_129_, v_data_130_, v_addr_131_);
    crate::leanh::lean_dec(v_addr_131_);
    crate::leanh::lean_dec(v_socket_129_);
    return v_res_133_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_recv___boxed(
    mut v_socket_137_: *mut crate::leanh::LeanObject,
    mut v_size_138_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_140_: u64 = 0;
    let mut v_res_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_140_ = crate::leanh::lean_unbox_uint64(v_size_138_);
    crate::leanh::lean_dec_ref(v_size_138_);
    v_res_141_ = lean_uv_udp_recv(v_socket_137_, v_size_boxed_140_);
    crate::leanh::lean_dec(v_socket_137_);
    return v_res_141_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_waitReadable___boxed(
    mut v_socket_144_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = lean_uv_udp_wait_readable(v_socket_144_);
    crate::leanh::lean_dec(v_socket_144_);
    return v_res_146_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_cancelRecv___boxed(
    mut v_socket_149_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_151_ = lean_uv_udp_cancel_recv(v_socket_149_);
    crate::leanh::lean_dec(v_socket_149_);
    return v_res_151_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(
    mut v_socket_154_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = lean_uv_udp_getpeername(v_socket_154_);
    crate::leanh::lean_dec(v_socket_154_);
    return v_res_156_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_getSockName___boxed(
    mut v_socket_159_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_161_ = lean_uv_udp_getsockname(v_socket_159_);
    crate::leanh::lean_dec(v_socket_159_);
    return v_res_161_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(
    mut v_socket_165_: *mut crate::leanh::LeanObject,
    mut v_on_166_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_on_boxed_168_: u8 = 0;
    let mut v_res_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_on_boxed_168_ = (crate::leanh::lean_unbox(v_on_166_) as u8);
    v_res_169_ = lean_uv_udp_set_broadcast(v_socket_165_, v_on_boxed_168_);
    crate::leanh::lean_dec(v_socket_165_);
    return v_res_169_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(
    mut v_socket_173_: *mut crate::leanh::LeanObject,
    mut v_on_174_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_on_boxed_176_: u8 = 0;
    let mut v_res_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_on_boxed_176_ = (crate::leanh::lean_unbox(v_on_174_) as u8);
    v_res_177_ = lean_uv_udp_set_multicast_loop(v_socket_173_, v_on_boxed_176_);
    crate::leanh::lean_dec(v_socket_173_);
    return v_res_177_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(
    mut v_socket_181_: *mut crate::leanh::LeanObject,
    mut v_ttl_182_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ttl_boxed_184_: u32 = 0;
    let mut v_res_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ttl_boxed_184_ = crate::leanh::lean_unbox_uint32(v_ttl_182_);
    crate::leanh::lean_dec(v_ttl_182_);
    v_res_185_ = lean_uv_udp_set_multicast_ttl(v_socket_181_, v_ttl_boxed_184_);
    crate::leanh::lean_dec(v_socket_181_);
    return v_res_185_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setMembership___boxed(
    mut v_socket_191_: *mut crate::leanh::LeanObject,
    mut v_multicastAddr_192_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_193_: *mut crate::leanh::LeanObject,
    mut v_membership_194_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_membership_boxed_196_: u8 = 0;
    let mut v_res_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_membership_boxed_196_ = (crate::leanh::lean_unbox(v_membership_194_) as u8);
    v_res_197_ = lean_uv_udp_set_membership(
        v_socket_191_,
        v_multicastAddr_192_,
        v_interfaceAddr_193_,
        v_membership_boxed_196_,
    );
    crate::leanh::lean_dec(v_interfaceAddr_193_);
    crate::leanh::lean_dec_ref(v_multicastAddr_192_);
    crate::leanh::lean_dec(v_socket_191_);
    return v_res_197_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(
    mut v_socket_201_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_202_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = lean_uv_udp_set_multicast_interface(v_socket_201_, v_interfaceAddr_202_);
    crate::leanh::lean_dec_ref(v_interfaceAddr_202_);
    crate::leanh::lean_dec(v_socket_201_);
    return v_res_204_;
}
pub unsafe fn l_Std_Internal_UV_UDP_Socket_setTTL___boxed(
    mut v_socket_208_: *mut crate::leanh::LeanObject,
    mut v_ttl_209_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ttl_boxed_211_: u32 = 0;
    let mut v_res_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ttl_boxed_211_ = crate::leanh::lean_unbox_uint32(v_ttl_209_);
    crate::leanh::lean_dec(v_ttl_209_);
    v_res_212_ = lean_uv_udp_set_ttl(v_socket_208_, v_ttl_boxed_211_);
    crate::leanh::lean_dec(v_socket_208_);
    return v_res_212_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl =
        _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_UDP(builtin);
}

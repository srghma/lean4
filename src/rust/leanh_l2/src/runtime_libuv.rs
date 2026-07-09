use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use std::{ptr, thread};

use crate::{
    runtime_event_loop::{EventLoop, GLOBAL_EV},
    runtime_thread::{lean_finalize_thread, lean_initialize_thread},
    runtime_timer::initialize_libuv_timer,
};

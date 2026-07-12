use std::ffi::c_int;

pub unsafe fn lean_errno() -> c_int {
    #[cfg(target_os = "windows")]
    {
        *libc::_errno()
    }
    #[cfg(not(target_os = "windows"))]
    {
        *libc::__errno_location()
    }
}

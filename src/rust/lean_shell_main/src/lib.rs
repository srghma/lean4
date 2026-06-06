/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![cfg_attr(not(test), no_std)]

#[cfg(not(test))]
extern "C" {
    fn abort() -> !;
    fn lean_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int;
}

#[cfg(not(test))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    unsafe { abort() }
}

#[cfg(not(test))]
#[no_mangle]
pub extern "C" fn main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
    unsafe { lean_main(argc, argv) }
}

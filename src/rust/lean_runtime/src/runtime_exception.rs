/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

fn abort_with_message(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::abort();
}

const THROWABLE_WHAT: &[u8] = b"lean::throwable\0";
const THROWABLE_TYPE_NAME: &[u8] = b"N4lean9throwableE\0";

#[repr(C)]
pub struct SiClassTypeInfo {
    vptr: *const c_void,
    name: *const c_char,
    base: *const c_void,
}

unsafe impl Sync for SiClassTypeInfo {}

#[repr(C)]
pub struct StdString {
    data: [usize; 4],
}

unsafe impl Sync for StdString {}

#[repr(C)]
pub struct Throwable {
    vptr: *const c_void,
    msg: StdString,
}

unsafe impl Sync for Throwable {}

#[repr(C)]
pub struct ThrowableVTable {
    offset_to_top: isize,
    typeinfo: *const c_void,
    dtor1: *const c_void,
    dtor2: *const c_void,
    what: *const c_void,
}

unsafe impl Sync for ThrowableVTable {}

extern "C" {
    static _ZTVN10__cxxabiv117__class_type_infoE: [usize; 4];
    static _ZTVN10__cxxabiv120__si_class_type_infoE: [usize; 4];
    #[link_name = "_ZTISt9exception"]
    static _ZTISt9exception: [usize; 0];

    #[link_name = "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEC1Ev"]
    fn std_string_ctor(this: *mut StdString);
    #[link_name = "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEC1ERKS4_"]
    fn std_string_copy_ctor(this: *mut StdString, other: *const StdString);
    #[link_name = "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE6assignEPKc"]
    fn std_string_assign(this: *mut StdString, s: *const c_char) -> *mut StdString;
    #[link_name = "_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEED1Ev"]
    fn std_string_dtor(this: *mut StdString);
    #[link_name = "_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE5c_strEv"]
    fn std_string_c_str(this: *const StdString) -> *const c_char;
}

unsafe fn throwable_msg(this: *mut c_void) -> *mut StdString {
    core::ptr::addr_of_mut!((*(this as *mut Throwable)).msg)
}

#[export_name = "_ZTVN4lean9throwableE"]
pub static LEAN_THROWABLE_VTABLE: ThrowableVTable = ThrowableVTable {
    offset_to_top: 0,
    typeinfo: core::ptr::addr_of!(LEAN_THROWABLE_TYPEINFO) as *const c_void,
    dtor1: lean_throwable_dtor_d1 as *const c_void,
    dtor2: lean_throwable_dtor_d2 as *const c_void,
    what: lean_throwable_what as *const c_void,
};

#[no_mangle]
pub extern "C" fn throw_get_stack_size_failed() -> ! {
    abort_with_message("failed to retrieve thread stack size")
}

#[no_mangle]
pub extern "C" fn throw_stack_space_exception(component_name: *const c_char) -> ! {
    let component_name = unsafe { core::ffi::CStr::from_ptr(component_name) }.to_string_lossy();
    abort_with_message(&format!("stack space exception: {component_name}"))
}

#[no_mangle]
pub extern "C" fn throw_heartbeat_exception() -> ! {
    abort_with_message("heartbeat exception")
}

#[no_mangle]
pub extern "C" fn throw_memory_exception(component_name: *const c_char) -> ! {
    let component_name = unsafe { core::ffi::CStr::from_ptr(component_name) }.to_string_lossy();
    abort_with_message(&format!("memory exception: {component_name}"))
}

#[no_mangle]
pub extern "C" fn lean_throw_interrupted() -> ! {
    abort_with_message("interrupted")
}

#[no_mangle]
pub extern "C" fn lean_uncaught_exceptions() -> bool {
    false
}

#[export_name = "_ZN4lean9throwableC1ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEE"]
pub unsafe extern "C" fn lean_throwable_ctor_c1(this: *mut c_void, _msg: *const c_void) {
    lean_throwable_ctor_c2(this, _msg);
}

#[export_name = "_ZN4lean9throwableC2ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEE"]
pub unsafe extern "C" fn lean_throwable_ctor_c2(this: *mut c_void, msg: *const c_void) {
    let this = this as *mut Throwable;
    core::ptr::write(
        &mut (*this).vptr,
        core::ptr::addr_of!(LEAN_THROWABLE_VTABLE.dtor1) as *const c_void,
    );
    std_string_copy_ctor(throwable_msg(this as *mut c_void), msg as *const StdString);
}

#[export_name = "_ZN4lean9throwableD1Ev"]
pub unsafe extern "C" fn lean_throwable_dtor_d1(this: *mut c_void) {
    std_string_dtor(throwable_msg(this));
}

#[export_name = "_ZN4lean9throwableD2Ev"]
pub unsafe extern "C" fn lean_throwable_dtor_d2(this: *mut c_void) {
    lean_throwable_dtor_d1(this);
}

#[export_name = "_ZNK4lean9throwable4whatEv"]
pub unsafe extern "C" fn lean_throwable_what(_this: *const c_void) -> *const c_char {
    std_string_c_str(throwable_msg(_this as *mut c_void))
}

#[export_name = "_ZTIN4lean9throwableE"]
pub static LEAN_THROWABLE_TYPEINFO: SiClassTypeInfo = SiClassTypeInfo {
    vptr: unsafe { core::ptr::addr_of!(_ZTVN10__cxxabiv120__si_class_type_infoE[2]) as *const c_void },
    name: THROWABLE_TYPE_NAME.as_ptr() as *const c_char,
    base: unsafe { core::ptr::addr_of!(_ZTISt9exception) as *const c_void },
};

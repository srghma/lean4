// Lean compiler output
// Module: lazylist
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_mk_thunk(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_add___boxed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_thunk_get_own(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn l_Function_const___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_LazyList_instAppend___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_instAppend___lam__1 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_instAppend___closed__0: *mut lean_object = core::ptr::addr_of!(l_LazyList_instAppend___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_zip___redArg___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_zip___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_zip___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_LazyList_zip___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_isMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__0: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_isMonad___lam__2 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__1: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__2_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_isMonad___lam__5 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__2: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_isMonad___lam__7 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__3: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__3_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__4_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_map as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__4: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__4_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__5_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_LazyList_isMonad___closed__4_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__0_value) as *mut lean_object] };
static mut l_LazyList_isMonad___closed__5: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__5_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__6_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_pure as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__6: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__6_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__7_value: lean_ctor_object<5> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*5 + 0) as u16, m_other: 5, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_LazyList_isMonad___closed__5_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__6_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__1_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__2_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__3_value) as *mut lean_object] };
static mut l_LazyList_isMonad___closed__7: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__7_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__8_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_bind as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_isMonad___closed__8: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_isMonad___closed__9_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [core::ptr::addr_of!(l_LazyList_isMonad___closed__7_value) as *mut lean_object,core::ptr::addr_of!(l_LazyList_isMonad___closed__8_value) as *mut lean_object] };
static mut l_LazyList_isMonad___closed__9: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__9_value) as *mut lean_object;
#[no_mangle] pub static mut l_LazyList_isMonad: *mut lean_object = core::ptr::addr_of!(l_LazyList_isMonad___closed__9_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_instAlternative___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_instAlternative___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_instAlternative___closed__0: *mut lean_object = core::ptr::addr_of!(l_LazyList_instAlternative___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_LazyList_instAlternative___closed__1_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_LazyList_append as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_LazyList_instAlternative___closed__1: *mut lean_object = core::ptr::addr_of!(l_LazyList_instAlternative___closed__1_value) as *mut lean_object;
#[no_mangle] pub static mut l_LazyList_instAlternative: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_fib___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Nat_add___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_fib___closed__0: *mut lean_object = core::ptr::addr_of!(l_fib___closed__0_value) as *mut lean_object;
static mut l_fib___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_fib___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_fib: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_iota___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_iota___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_iota___closed__0: *mut lean_object = core::ptr::addr_of!(l_iota___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst___lam__0___closed__0_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l_tst___lam__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst___lam__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst___lam__0___closed__1_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 61, 32, 0]};
static mut l_tst___lam__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_tst___lam__0___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_tst___lam__1___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst___lam__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst___lam__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst___closed__0_value: lean_closure_object<3> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 245 }, m_fun: l_tst___lam__2 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_tst___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_tst___closed__1: *mut lean_object = core::ptr::addr_of!(l_tst___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_tst___closed__2_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_tst___closed__1_value) as *mut lean_object] };
static mut l_tst___closed__2: *mut lean_object = core::ptr::addr_of!(l_tst___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_tst___closed__3_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_tst___closed__2_value) as *mut lean_object] };
static mut l_tst___closed__3: *mut lean_object = core::ptr::addr_of!(l_tst___closed__3_value) as *mut lean_object;
static mut l_tst___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_tst___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_tst___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst___closed__6: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_tst: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__0___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__0___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__1_value) as *mut lean_object;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: u8 = 0;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__3_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__8_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__9_value: lean_closure_object<1> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*1) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorIdx___redArg(mut v_x_1_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_x_1_)
{
0 => {
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
return v___x_2_;
}
1 => {
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_unsigned_to_nat(1);
return v___x_3_;
}
_ => {
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = lean_unsigned_to_nat(2);
return v___x_4_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorIdx___redArg___boxed(mut v_x_5_: *mut lean_object) -> *mut lean_object{
let mut v_res_6_: *mut lean_object = core::ptr::null_mut(); 
v_res_6_ = l_LazyList_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorIdx(mut v_00_u03b1_7_: *mut lean_object, mut v_x_8_: *mut lean_object) -> *mut lean_object{
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
v___x_9_ = l_LazyList_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorIdx___boxed(mut v_00_u03b1_10_: *mut lean_object, mut v_x_11_: *mut lean_object) -> *mut lean_object{
let mut v_res_12_: *mut lean_object = core::ptr::null_mut(); 
v_res_12_ = l_LazyList_ctorIdx(v_00_u03b1_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorElim___redArg(mut v_t_13_: *mut lean_object, mut v_k_14_: *mut lean_object) -> *mut lean_object{
match lean_obj_tag(v_t_13_)
{
0 => {
return v_k_14_;
}
1 => {
let mut v_hd_15_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v_hd_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_hd_15_);
v_tl_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_tl_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_hd_15_, v_tl_16_);
return v___x_17_;
}
_ => {
let mut v_t_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
v_t_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_t_18_);
lean_dec_ref_known(v_t_13_, 1);
v___x_19_ = lean_apply_1(v_k_14_, v_t_18_);
return v___x_19_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorElim(mut v_00_u03b1_20_: *mut lean_object, mut v_motive__1_21_: *mut lean_object, mut v_ctorIdx_22_: *mut lean_object, mut v_t_23_: *mut lean_object, mut v_h_24_: *mut lean_object, mut v_k_25_: *mut lean_object) -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = l_LazyList_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_ctorElim___boxed(mut v_00_u03b1_27_: *mut lean_object, mut v_motive__1_28_: *mut lean_object, mut v_ctorIdx_29_: *mut lean_object, mut v_t_30_: *mut lean_object, mut v_h_31_: *mut lean_object, mut v_k_32_: *mut lean_object) -> *mut lean_object{
let mut v_res_33_: *mut lean_object = core::ptr::null_mut(); 
v_res_33_ = l_LazyList_ctorElim(v_00_u03b1_27_, v_motive__1_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_nil_elim___redArg(mut v_t_34_: *mut lean_object, mut v_nil_35_: *mut lean_object) -> *mut lean_object{
let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_36_ = l_LazyList_ctorElim___redArg(v_t_34_, v_nil_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_nil_elim(mut v_00_u03b1_37_: *mut lean_object, mut v_motive__1_38_: *mut lean_object, mut v_t_39_: *mut lean_object, mut v_h_40_: *mut lean_object, mut v_nil_41_: *mut lean_object) -> *mut lean_object{
let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v___x_42_ = l_LazyList_ctorElim___redArg(v_t_39_, v_nil_41_);
return v___x_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_cons_elim___redArg(mut v_t_43_: *mut lean_object, mut v_cons_44_: *mut lean_object) -> *mut lean_object{
let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v___x_45_ = l_LazyList_ctorElim___redArg(v_t_43_, v_cons_44_);
return v___x_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_cons_elim(mut v_00_u03b1_46_: *mut lean_object, mut v_motive__1_47_: *mut lean_object, mut v_t_48_: *mut lean_object, mut v_h_49_: *mut lean_object, mut v_cons_50_: *mut lean_object) -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_51_ = l_LazyList_ctorElim___redArg(v_t_48_, v_cons_50_);
return v___x_51_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_delayed_elim___redArg(mut v_t_52_: *mut lean_object, mut v_delayed_53_: *mut lean_object) -> *mut lean_object{
let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); 
v___x_54_ = l_LazyList_ctorElim___redArg(v_t_52_, v_delayed_53_);
return v___x_54_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_delayed_elim(mut v_00_u03b1_55_: *mut lean_object, mut v_motive__1_56_: *mut lean_object, mut v_t_57_: *mut lean_object, mut v_h_58_: *mut lean_object, mut v_delayed_59_: *mut lean_object) -> *mut lean_object{
let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_60_ = l_LazyList_ctorElim___redArg(v_t_57_, v_delayed_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_toLazy___redArg(mut v_x_61_: *mut lean_object) -> *mut lean_object{
let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v_head_63_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_67_: u8 = 0; let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_72_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_61_) == 0 {
let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_62_ = lean_box(0);
return v___x_62_;
} else {
let mut v_head_63_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_67_: u8 = 0; let mut v_isSharedCheck_72_: u8 = 0; 
v_head_63_ = lean_ctor_get(v_x_61_, 0);
v_tail_64_ = lean_ctor_get(v_x_61_, 1);
v_isSharedCheck_72_ = (!lean_is_exclusive(v_x_61_)) as u8;
if v_isSharedCheck_72_ == 0 {
v___x_66_ = v_x_61_;
v_isShared_67_ = v_isSharedCheck_72_;
state = 1; continue;
} else {
lean_inc(v_tail_64_);
lean_inc(v_head_63_);
lean_dec(v_x_61_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_72_;
state = 1; continue;
}
}
}
1 => {
v___x_68_ = l_List_toLazy___redArg(v_tail_64_);
if v_isShared_67_ == 0 {
lean_ctor_set(v___x_66_, 1, v___x_68_);
v___x_70_ = v___x_66_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_71_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_head_63_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toLazy(mut v_00_u03b1_73_: *mut lean_object, mut v_x_74_: *mut lean_object) -> *mut lean_object{
let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = l_List_toLazy___redArg(v_x_74_);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instInhabited(mut v_00_u03b1_76_: *mut lean_object) -> *mut lean_object{
let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); 
v___x_77_ = lean_box(0);
return v___x_77_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_pure___redArg(mut v_x_78_: *mut lean_object) -> *mut lean_object{
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
v___x_79_ = lean_box(0);
v___x_80_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_80_, 0, v_x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_pure(mut v_00_u03b1_81_: *mut lean_object, mut v_x_82_: *mut lean_object) -> *mut lean_object{
let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); 
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_84_, 0, v_x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
return v___x_84_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isEmpty___redArg(mut v_x_85_: *mut lean_object) -> u8{
let mut v___x_86_: u8 = 0; let mut v___x_87_: u8 = 0; let mut v_t_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_85_)
{
0 => {
let mut v___x_86_: u8 = 0; 
v___x_86_ = 1;
return v___x_86_;
}
1 => {
let mut v___x_87_: u8 = 0; 
lean_dec_ref_known(v_x_85_, 2);
v___x_87_ = 0;
return v___x_87_;
}
_ => {
let mut v_t_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
v_t_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref(v_t_88_);
lean_dec_ref_known(v_x_85_, 1);
v___x_89_ = lean_thunk_get_own(v_t_88_);
lean_dec_ref(v_t_88_);
v_x_85_ = v___x_89_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isEmpty___redArg___boxed(mut v_x_91_: *mut lean_object) -> *mut lean_object{
let mut v_res_92_: u8 = 0; let mut v_r_93_: *mut lean_object = core::ptr::null_mut(); 
v_res_92_ = l_LazyList_isEmpty___redArg(v_x_91_);
v_r_93_ = lean_box((v_res_92_) as usize);
return v_r_93_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isEmpty(mut v_00_u03b1_94_: *mut lean_object, mut v_x_95_: *mut lean_object) -> u8{
let mut v___x_96_: u8 = 0; 
v___x_96_ = l_LazyList_isEmpty___redArg(v_x_95_);
return v___x_96_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isEmpty___boxed(mut v_00_u03b1_97_: *mut lean_object, mut v_x_98_: *mut lean_object) -> *mut lean_object{
let mut v_res_99_: u8 = 0; let mut v_r_100_: *mut lean_object = core::ptr::null_mut(); 
v_res_99_ = l_LazyList_isEmpty(v_00_u03b1_97_, v_x_98_);
v_r_100_ = lean_box((v_res_99_) as usize);
return v_r_100_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_toList___redArg(mut v_x_101_: *mut lean_object) -> *mut lean_object{
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_103_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_107_: u8 = 0; let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_111_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_112_: u8 = 0; let mut v_t_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_101_)
{
0 => {
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_102_ = lean_box(0);
return v___x_102_;
}
1 => {
let mut v_hd_103_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_107_: u8 = 0; let mut v_isSharedCheck_112_: u8 = 0; 
v_hd_103_ = lean_ctor_get(v_x_101_, 0);
v_tl_104_ = lean_ctor_get(v_x_101_, 1);
v_isSharedCheck_112_ = (!lean_is_exclusive(v_x_101_)) as u8;
if v_isSharedCheck_112_ == 0 {
v___x_106_ = v_x_101_;
v_isShared_107_ = v_isSharedCheck_112_;
state = 1; continue;
} else {
lean_inc(v_tl_104_);
lean_inc(v_hd_103_);
lean_dec(v_x_101_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_112_;
state = 1; continue;
}
}
_ => {
let mut v_t_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
v_t_113_ = lean_ctor_get(v_x_101_, 0);
lean_inc_ref(v_t_113_);
lean_dec_ref_known(v_x_101_, 1);
v___x_114_ = lean_thunk_get_own(v_t_113_);
lean_dec_ref(v_t_113_);
v_x_101_ = v___x_114_;
state = 0; continue;
}
}
}
1 => {
v___x_108_ = l_LazyList_toList___redArg(v_tl_104_);
if v_isShared_107_ == 0 {
lean_ctor_set(v___x_106_, 1, v___x_108_);
v___x_110_ = v___x_106_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_111_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_hd_103_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_toList(mut v_00_u03b1_116_: *mut lean_object, mut v_x_117_: *mut lean_object) -> *mut lean_object{
let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); 
v___x_118_ = l_LazyList_toList___redArg(v_x_117_);
return v___x_118_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_head___redArg(mut v_inst_119_: *mut lean_object, mut v_x_120_: *mut lean_object) -> *mut lean_object{
let mut v_hd_121_: *mut lean_object = core::ptr::null_mut(); let mut v_t_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_120_)
{
0 => {
lean_inc(v_inst_119_);
return v_inst_119_;
}
1 => {
let mut v_hd_121_: *mut lean_object = core::ptr::null_mut(); 
v_hd_121_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_hd_121_);
lean_dec_ref_known(v_x_120_, 2);
return v_hd_121_;
}
_ => {
let mut v_t_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
v_t_122_ = lean_ctor_get(v_x_120_, 0);
lean_inc_ref(v_t_122_);
lean_dec_ref_known(v_x_120_, 1);
v___x_123_ = lean_thunk_get_own(v_t_122_);
lean_dec_ref(v_t_122_);
v_x_120_ = v___x_123_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_head___redArg___boxed(mut v_inst_125_: *mut lean_object, mut v_x_126_: *mut lean_object) -> *mut lean_object{
let mut v_res_127_: *mut lean_object = core::ptr::null_mut(); 
v_res_127_ = l_LazyList_head___redArg(v_inst_125_, v_x_126_);
lean_dec(v_inst_125_);
return v_res_127_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_head(mut v_00_u03b1_128_: *mut lean_object, mut v_inst_129_: *mut lean_object, mut v_x_130_: *mut lean_object) -> *mut lean_object{
let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); 
v___x_131_ = l_LazyList_head___redArg(v_inst_129_, v_x_130_);
return v___x_131_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_head___boxed(mut v_00_u03b1_132_: *mut lean_object, mut v_inst_133_: *mut lean_object, mut v_x_134_: *mut lean_object) -> *mut lean_object{
let mut v_res_135_: *mut lean_object = core::ptr::null_mut(); 
v_res_135_ = l_LazyList_head(v_00_u03b1_132_, v_inst_133_, v_x_134_);
lean_dec(v_inst_133_);
return v_res_135_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_tail___redArg(mut v_x_136_: *mut lean_object) -> *mut lean_object{
let mut v_tl_137_: *mut lean_object = core::ptr::null_mut(); let mut v_t_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_136_)
{
0 => {
return v_x_136_;
}
1 => {
let mut v_tl_137_: *mut lean_object = core::ptr::null_mut(); 
v_tl_137_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_tl_137_);
lean_dec_ref_known(v_x_136_, 2);
return v_tl_137_;
}
_ => {
let mut v_t_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
v_t_138_ = lean_ctor_get(v_x_136_, 0);
lean_inc_ref(v_t_138_);
lean_dec_ref_known(v_x_136_, 1);
v___x_139_ = lean_thunk_get_own(v_t_138_);
lean_dec_ref(v_t_138_);
v_x_136_ = v___x_139_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_tail(mut v_00_u03b1_141_: *mut lean_object, mut v_x_142_: *mut lean_object) -> *mut lean_object{
let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); 
v___x_143_ = l_LazyList_tail___redArg(v_x_142_);
return v___x_143_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_append___redArg___lam__1(mut v_t_144_: *mut lean_object, mut v_x_145_: *mut lean_object, mut v_x_146_: *mut lean_object) -> *mut lean_object{
let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
v___x_147_ = lean_thunk_get_own(v_t_144_);
v___x_148_ = l_LazyList_append___redArg(v___x_147_, v_x_145_);
return v___x_148_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_append___redArg___lam__1___boxed(mut v_t_149_: *mut lean_object, mut v_x_150_: *mut lean_object, mut v_x_151_: *mut lean_object) -> *mut lean_object{
let mut v_res_152_: *mut lean_object = core::ptr::null_mut(); 
v_res_152_ = l_LazyList_append___redArg___lam__1(v_t_149_, v_x_150_, v_x_151_);
lean_dec_ref(v_t_149_);
return v_res_152_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_append___redArg(mut v_x_153_: *mut lean_object, mut v_x_154_: *mut lean_object) -> *mut lean_object{
let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_157_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_158_: *mut lean_object = core::ptr::null_mut(); let mut v___f_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_t_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_165_: u8 = 0; let mut v___f_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_171_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_153_)
{
0 => {
let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); 
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_x_154_, v___x_155_);
return v___x_156_;
}
1 => {
let mut v_hd_157_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_158_: *mut lean_object = core::ptr::null_mut(); let mut v___f_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); 
v_hd_157_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_hd_157_);
v_tl_158_ = lean_ctor_get(v_x_153_, 1);
lean_inc(v_tl_158_);
lean_dec_ref_known(v_x_153_, 2);
v___f_159_ = lean_alloc_closure(l_LazyList_append___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_159_, 0, v_tl_158_);
lean_closure_set(v___f_159_, 1, v_x_154_);
lean_closure_set(v___f_159_, 2, v_hd_157_);
v___x_160_ = lean_mk_thunk(v___f_159_);
v___x_161_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
_ => {
let mut v_t_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_165_: u8 = 0; let mut v_isSharedCheck_171_: u8 = 0; 
v_t_162_ = lean_ctor_get(v_x_153_, 0);
v_isSharedCheck_171_ = (!lean_is_exclusive(v_x_153_)) as u8;
if v_isSharedCheck_171_ == 0 {
v___x_164_ = v_x_153_;
v_isShared_165_ = v_isSharedCheck_171_;
state = 1; continue;
} else {
lean_inc(v_t_162_);
lean_dec(v_x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_171_;
state = 1; continue;
}
}
}
}
1 => {
v___f_166_ = lean_alloc_closure(l_LazyList_append___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_166_, 0, v_t_162_);
lean_closure_set(v___f_166_, 1, v_x_154_);
v___x_167_ = lean_mk_thunk(v___f_166_);
if v_isShared_165_ == 0 {
lean_ctor_set(v___x_164_, 0, v___x_167_);
v___x_169_ = v___x_164_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_170_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_170_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_append___redArg___lam__0(mut v_tl_172_: *mut lean_object, mut v_x_173_: *mut lean_object, mut v_hd_174_: *mut lean_object, mut v_x_175_: *mut lean_object) -> *mut lean_object{
let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); 
v___x_176_ = l_LazyList_append___redArg(v_tl_172_, v_x_173_);
v___x_177_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_177_, 0, v_hd_174_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_append(mut v_00_u03b1_178_: *mut lean_object, mut v_x_179_: *mut lean_object, mut v_x_180_: *mut lean_object) -> *mut lean_object{
let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); 
v___x_181_ = l_LazyList_append___redArg(v_x_179_, v_x_180_);
return v___x_181_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instAppend___lam__0(mut v_b_182_: *mut lean_object, mut v_x_183_: *mut lean_object) -> *mut lean_object{
lean_inc(v_b_182_);
return v_b_182_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instAppend___lam__0___boxed(mut v_b_184_: *mut lean_object, mut v_x_185_: *mut lean_object) -> *mut lean_object{
let mut v_res_186_: *mut lean_object = core::ptr::null_mut(); 
v_res_186_ = l_LazyList_instAppend___lam__0(v_b_184_, v_x_185_);
lean_dec(v_b_184_);
return v_res_186_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instAppend___lam__1(mut v_a_187_: *mut lean_object, mut v_b_188_: *mut lean_object) -> *mut lean_object{
let mut v___f_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); 
v___f_189_ = lean_alloc_closure(l_LazyList_instAppend___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_189_, 0, v_b_188_);
v___x_190_ = l_LazyList_append___redArg(v_a_187_, v___f_189_);
return v___x_190_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instAppend(mut v_00_u03b1_192_: *mut lean_object) -> *mut lean_object{
let mut v___f_193_: *mut lean_object = core::ptr::null_mut(); 
v___f_193_ = l_LazyList_instAppend___closed__0;
return v___f_193_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_interleave___redArg___lam__1(mut v_t_194_: *mut lean_object, mut v_x_195_: *mut lean_object, mut v_x_196_: *mut lean_object) -> *mut lean_object{
let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); 
v___x_197_ = lean_thunk_get_own(v_t_194_);
v___x_198_ = l_LazyList_interleave___redArg(v___x_197_, v_x_195_);
return v___x_198_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_interleave___redArg___lam__1___boxed(mut v_t_199_: *mut lean_object, mut v_x_200_: *mut lean_object, mut v_x_201_: *mut lean_object) -> *mut lean_object{
let mut v_res_202_: *mut lean_object = core::ptr::null_mut(); 
v_res_202_ = l_LazyList_interleave___redArg___lam__1(v_t_199_, v_x_200_, v_x_201_);
lean_dec_ref(v_t_199_);
return v_res_202_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_interleave___redArg(mut v_x_203_: *mut lean_object, mut v_x_204_: *mut lean_object) -> *mut lean_object{
let mut v_hd_205_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_206_: *mut lean_object = core::ptr::null_mut(); let mut v___f_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v_t_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_213_: u8 = 0; let mut v___f_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: *mut lean_object = core::ptr::null_mut(); let mut v___x_217_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_218_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_219_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_203_)
{
0 => {
return v_x_204_;
}
1 => {
let mut v_hd_205_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_206_: *mut lean_object = core::ptr::null_mut(); let mut v___f_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); 
v_hd_205_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_hd_205_);
v_tl_206_ = lean_ctor_get(v_x_203_, 1);
lean_inc(v_tl_206_);
lean_dec_ref_known(v_x_203_, 2);
v___f_207_ = lean_alloc_closure(l_LazyList_interleave___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_207_, 0, v_x_204_);
lean_closure_set(v___f_207_, 1, v_tl_206_);
lean_closure_set(v___f_207_, 2, v_hd_205_);
v___x_208_ = lean_mk_thunk(v___f_207_);
v___x_209_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
_ => {
let mut v_t_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_213_: u8 = 0; let mut v_isSharedCheck_219_: u8 = 0; 
v_t_210_ = lean_ctor_get(v_x_203_, 0);
v_isSharedCheck_219_ = (!lean_is_exclusive(v_x_203_)) as u8;
if v_isSharedCheck_219_ == 0 {
v___x_212_ = v_x_203_;
v_isShared_213_ = v_isSharedCheck_219_;
state = 1; continue;
} else {
lean_inc(v_t_210_);
lean_dec(v_x_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_219_;
state = 1; continue;
}
}
}
}
1 => {
v___f_214_ = lean_alloc_closure(l_LazyList_interleave___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_214_, 0, v_t_210_);
lean_closure_set(v___f_214_, 1, v_x_204_);
v___x_215_ = lean_mk_thunk(v___f_214_);
if v_isShared_213_ == 0 {
lean_ctor_set(v___x_212_, 0, v___x_215_);
v___x_217_ = v___x_212_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_218_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_218_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_interleave___redArg___lam__0(mut v_x_220_: *mut lean_object, mut v_tl_221_: *mut lean_object, mut v_hd_222_: *mut lean_object, mut v_x_223_: *mut lean_object) -> *mut lean_object{
let mut v___x_224_: *mut lean_object = core::ptr::null_mut(); let mut v___x_225_: *mut lean_object = core::ptr::null_mut(); 
v___x_224_ = l_LazyList_interleave___redArg(v_x_220_, v_tl_221_);
v___x_225_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_225_, 0, v_hd_222_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_interleave(mut v_00_u03b1_226_: *mut lean_object, mut v_x_227_: *mut lean_object, mut v_x_228_: *mut lean_object) -> *mut lean_object{
let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); 
v___x_229_ = l_LazyList_interleave___redArg(v_x_227_, v_x_228_);
return v___x_229_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map___redArg___lam__0(mut v_f_230_: *mut lean_object, mut v_hd_231_: *mut lean_object, mut v_tl_232_: *mut lean_object, mut v_x_233_: *mut lean_object) -> *mut lean_object{
let mut v___x_234_: *mut lean_object = core::ptr::null_mut(); let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_f_230_);
v___x_234_ = lean_apply_1(v_f_230_, v_hd_231_);
v___x_235_ = l_LazyList_map___redArg(v_f_230_, v_tl_232_);
v___x_236_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
return v___x_236_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map___redArg___lam__1___boxed(mut v_t_237_: *mut lean_object, mut v_f_238_: *mut lean_object, mut v_x_239_: *mut lean_object) -> *mut lean_object{
let mut v_res_240_: *mut lean_object = core::ptr::null_mut(); 
v_res_240_ = l_LazyList_map___redArg___lam__1(v_t_237_, v_f_238_, v_x_239_);
lean_dec_ref(v_t_237_);
return v_res_240_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map___redArg(mut v_f_241_: *mut lean_object, mut v_x_242_: *mut lean_object) -> *mut lean_object{
let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_244_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_245_: *mut lean_object = core::ptr::null_mut(); let mut v___f_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); let mut v_t_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v___f_253_: *mut lean_object = core::ptr::null_mut(); let mut v___x_254_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_258_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_242_)
{
0 => {
let mut v___x_243_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_f_241_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
1 => {
let mut v_hd_244_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_245_: *mut lean_object = core::ptr::null_mut(); let mut v___f_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: *mut lean_object = core::ptr::null_mut(); 
v_hd_244_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_hd_244_);
v_tl_245_ = lean_ctor_get(v_x_242_, 1);
lean_inc(v_tl_245_);
lean_dec_ref_known(v_x_242_, 2);
v___f_246_ = lean_alloc_closure(l_LazyList_map___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_246_, 0, v_f_241_);
lean_closure_set(v___f_246_, 1, v_hd_244_);
lean_closure_set(v___f_246_, 2, v_tl_245_);
v___x_247_ = lean_mk_thunk(v___f_246_);
v___x_248_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
_ => {
let mut v_t_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_252_: u8 = 0; let mut v_isSharedCheck_258_: u8 = 0; 
v_t_249_ = lean_ctor_get(v_x_242_, 0);
v_isSharedCheck_258_ = (!lean_is_exclusive(v_x_242_)) as u8;
if v_isSharedCheck_258_ == 0 {
v___x_251_ = v_x_242_;
v_isShared_252_ = v_isSharedCheck_258_;
state = 1; continue;
} else {
lean_inc(v_t_249_);
lean_dec(v_x_242_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
state = 1; continue;
}
}
}
}
1 => {
v___f_253_ = lean_alloc_closure(l_LazyList_map___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_253_, 0, v_t_249_);
lean_closure_set(v___f_253_, 1, v_f_241_);
v___x_254_ = lean_mk_thunk(v___f_253_);
if v_isShared_252_ == 0 {
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_256_ = v___x_251_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_257_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_257_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map___redArg___lam__1(mut v_t_259_: *mut lean_object, mut v_f_260_: *mut lean_object, mut v_x_261_: *mut lean_object) -> *mut lean_object{
let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); 
v___x_262_ = lean_thunk_get_own(v_t_259_);
v___x_263_ = l_LazyList_map___redArg(v_f_260_, v___x_262_);
return v___x_263_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map(mut v_00_u03b1_264_: *mut lean_object, mut v_00_u03b2_265_: *mut lean_object, mut v_f_266_: *mut lean_object, mut v_x_267_: *mut lean_object) -> *mut lean_object{
let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); 
v___x_268_ = l_LazyList_map___redArg(v_f_266_, v_x_267_);
return v___x_268_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg___lam__0(mut v_f_269_: *mut lean_object, mut v_hd_270_: *mut lean_object, mut v_hd_271_: *mut lean_object, mut v_tl_272_: *mut lean_object, mut v_tl_273_: *mut lean_object, mut v_x_274_: *mut lean_object) -> *mut lean_object{
let mut v___x_275_: *mut lean_object = core::ptr::null_mut(); let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_f_269_);
v___x_275_ = lean_apply_2(v_f_269_, v_hd_270_, v_hd_271_);
v___x_276_ = l_LazyList_map_u2082___redArg(v_f_269_, v_tl_272_, v_tl_273_);
v___x_277_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg___lam__1___boxed(mut v_t_278_: *mut lean_object, mut v_f_279_: *mut lean_object, mut v_x_280_: *mut lean_object, mut v_x_281_: *mut lean_object) -> *mut lean_object{
let mut v_res_282_: *mut lean_object = core::ptr::null_mut(); 
v_res_282_ = l_LazyList_map_u2082___redArg___lam__1(v_t_278_, v_f_279_, v_x_280_, v_x_281_);
lean_dec_ref(v_t_278_);
return v_res_282_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg___lam__2(mut v_t_283_: *mut lean_object, mut v_f_284_: *mut lean_object, mut v_bs_285_: *mut lean_object, mut v_x_286_: *mut lean_object) -> *mut lean_object{
let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); 
v___x_287_ = lean_thunk_get_own(v_t_283_);
v___x_288_ = l_LazyList_map_u2082___redArg(v_f_284_, v___x_287_, v_bs_285_);
return v___x_288_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg___lam__2___boxed(mut v_t_289_: *mut lean_object, mut v_f_290_: *mut lean_object, mut v_bs_291_: *mut lean_object, mut v_x_292_: *mut lean_object) -> *mut lean_object{
let mut v_res_293_: *mut lean_object = core::ptr::null_mut(); 
v_res_293_ = l_LazyList_map_u2082___redArg___lam__2(v_t_289_, v_f_290_, v_bs_291_, v_x_292_);
lean_dec_ref(v_t_289_);
return v_res_293_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg(mut v_f_294_: *mut lean_object, mut v_x_295_: *mut lean_object, mut v_x_296_: *mut lean_object) -> *mut lean_object{
let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_299_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_300_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_301_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_302_: *mut lean_object = core::ptr::null_mut(); let mut v___f_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); let mut v_t_306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_308_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_309_: u8 = 0; let mut v___f_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_314_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_315_: u8 = 0; let mut v_t_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_319_: u8 = 0; let mut v_bs_321_: *mut lean_object = core::ptr::null_mut(); let mut v___f_322_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_328_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_295_)
{
0 => {
let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_296_);
lean_dec(v_f_294_);
v___x_297_ = lean_box(0);
return v___x_297_;
}
1 => {
match lean_obj_tag(v_x_296_)
{
0 => {
let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v_x_295_, 2);
lean_dec(v_f_294_);
v___x_298_ = lean_box(0);
return v___x_298_;
}
1 => {
let mut v_hd_299_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_300_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_301_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_302_: *mut lean_object = core::ptr::null_mut(); let mut v___f_303_: *mut lean_object = core::ptr::null_mut(); let mut v___x_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); 
v_hd_299_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_hd_299_);
v_tl_300_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_tl_300_);
lean_dec_ref_known(v_x_295_, 2);
v_hd_301_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_hd_301_);
v_tl_302_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_tl_302_);
lean_dec_ref_known(v_x_296_, 2);
v___f_303_ = lean_alloc_closure(l_LazyList_map_u2082___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
lean_closure_set(v___f_303_, 0, v_f_294_);
lean_closure_set(v___f_303_, 1, v_hd_299_);
lean_closure_set(v___f_303_, 2, v_hd_301_);
lean_closure_set(v___f_303_, 3, v_tl_300_);
lean_closure_set(v___f_303_, 4, v_tl_302_);
v___x_304_ = lean_mk_thunk(v___f_303_);
v___x_305_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
_ => {
let mut v_t_306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_308_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_309_: u8 = 0; let mut v_isSharedCheck_315_: u8 = 0; 
v_t_306_ = lean_ctor_get(v_x_296_, 0);
v_isSharedCheck_315_ = (!lean_is_exclusive(v_x_296_)) as u8;
if v_isSharedCheck_315_ == 0 {
v___x_308_ = v_x_296_;
v_isShared_309_ = v_isSharedCheck_315_;
state = 1; continue;
} else {
lean_inc(v_t_306_);
lean_dec(v_x_296_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_315_;
state = 1; continue;
}
}
}
}
_ => {
let mut v_t_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_319_: u8 = 0; let mut v_isSharedCheck_328_: u8 = 0; 
v_t_316_ = lean_ctor_get(v_x_295_, 0);
v_isSharedCheck_328_ = (!lean_is_exclusive(v_x_295_)) as u8;
if v_isSharedCheck_328_ == 0 {
v___x_318_ = v_x_295_;
v_isShared_319_ = v_isSharedCheck_328_;
state = 3; continue;
} else {
lean_inc(v_t_316_);
lean_dec(v_x_295_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
state = 3; continue;
}
}
}
}
1 => {
v___f_310_ = lean_alloc_closure(l_LazyList_map_u2082___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_310_, 0, v_t_306_);
lean_closure_set(v___f_310_, 1, v_f_294_);
lean_closure_set(v___f_310_, 2, v_x_295_);
v___x_311_ = lean_mk_thunk(v___f_310_);
if v_isShared_309_ == 0 {
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_314_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_314_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
state = 2; continue;
}
}
3 => {
match lean_obj_tag(v_x_296_)
{
0 => {
let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); 
lean_del_object(v___x_318_);
lean_dec_ref(v_t_316_);
lean_dec(v_f_294_);
v___x_327_ = lean_box(0);
return v___x_327_;
}
2 => {
v_bs_321_ = v_x_296_;
state = 4; continue;
}
_ => {
v_bs_321_ = v_x_296_;
state = 4; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082___redArg___lam__1(mut v_t_329_: *mut lean_object, mut v_f_330_: *mut lean_object, mut v_x_331_: *mut lean_object, mut v_x_332_: *mut lean_object) -> *mut lean_object{
let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); 
v___x_333_ = lean_thunk_get_own(v_t_329_);
v___x_334_ = l_LazyList_map_u2082___redArg(v_f_330_, v_x_331_, v___x_333_);
return v___x_334_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_map_u2082(mut v_00_u03b1_335_: *mut lean_object, mut v_00_u03b2_336_: *mut lean_object, mut v_00_u03b4_337_: *mut lean_object, mut v_f_338_: *mut lean_object, mut v_x_339_: *mut lean_object, mut v_x_340_: *mut lean_object) -> *mut lean_object{
let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); 
v___x_341_ = l_LazyList_map_u2082___redArg(v_f_338_, v_x_339_, v_x_340_);
return v___x_341_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_zip___redArg___lam__0(mut v_fst_342_: *mut lean_object, mut v_snd_343_: *mut lean_object) -> *mut lean_object{
let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
v___x_344_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_344_, 0, v_fst_342_);
lean_ctor_set(v___x_344_, 1, v_snd_343_);
return v___x_344_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_zip___redArg(mut v_a_346_: *mut lean_object, mut v_a_347_: *mut lean_object) -> *mut lean_object{
let mut v___f_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); 
v___f_348_ = l_LazyList_zip___redArg___closed__0;
v___x_349_ = l_LazyList_map_u2082___redArg(v___f_348_, v_a_346_, v_a_347_);
return v___x_349_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_zip(mut v_00_u03b1_350_: *mut lean_object, mut v_00_u03b2_351_: *mut lean_object, mut v_a_352_: *mut lean_object, mut v_a_353_: *mut lean_object) -> *mut lean_object{
let mut v___f_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_355_: *mut lean_object = core::ptr::null_mut(); 
v___f_354_ = l_LazyList_zip___redArg___closed__0;
v___x_355_ = l_LazyList_map_u2082___redArg(v___f_354_, v_a_352_, v_a_353_);
return v___x_355_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join___redArg___lam__1(mut v_hd_356_: *mut lean_object, mut v___f_357_: *mut lean_object, mut v_x_358_: *mut lean_object) -> *mut lean_object{
let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); 
v___x_359_ = l_LazyList_append___redArg(v_hd_356_, v___f_357_);
return v___x_359_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join___redArg___lam__2(mut v_t_360_: *mut lean_object, mut v_x_361_: *mut lean_object) -> *mut lean_object{
let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_363_: *mut lean_object = core::ptr::null_mut(); 
v___x_362_ = lean_thunk_get_own(v_t_360_);
v___x_363_ = l_LazyList_join___redArg(v___x_362_);
return v___x_363_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join___redArg___lam__2___boxed(mut v_t_364_: *mut lean_object, mut v_x_365_: *mut lean_object) -> *mut lean_object{
let mut v_res_366_: *mut lean_object = core::ptr::null_mut(); 
v_res_366_ = l_LazyList_join___redArg___lam__2(v_t_364_, v_x_365_);
lean_dec_ref(v_t_364_);
return v_res_366_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join___redArg(mut v_x_367_: *mut lean_object) -> *mut lean_object{
let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_369_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_370_: *mut lean_object = core::ptr::null_mut(); let mut v___f_371_: *mut lean_object = core::ptr::null_mut(); let mut v___f_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v_t_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_378_: u8 = 0; let mut v___f_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_383_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_384_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_367_)
{
0 => {
let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); 
v___x_368_ = lean_box(0);
return v___x_368_;
}
1 => {
let mut v_hd_369_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_370_: *mut lean_object = core::ptr::null_mut(); let mut v___f_371_: *mut lean_object = core::ptr::null_mut(); let mut v___f_372_: *mut lean_object = core::ptr::null_mut(); let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); 
v_hd_369_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_hd_369_);
v_tl_370_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_tl_370_);
lean_dec_ref_known(v_x_367_, 2);
v___f_371_ = lean_alloc_closure(l_LazyList_join___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_371_, 0, v_tl_370_);
v___f_372_ = lean_alloc_closure(l_LazyList_join___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_372_, 0, v_hd_369_);
lean_closure_set(v___f_372_, 1, v___f_371_);
v___x_373_ = lean_mk_thunk(v___f_372_);
v___x_374_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
_ => {
let mut v_t_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_378_: u8 = 0; let mut v_isSharedCheck_384_: u8 = 0; 
v_t_375_ = lean_ctor_get(v_x_367_, 0);
v_isSharedCheck_384_ = (!lean_is_exclusive(v_x_367_)) as u8;
if v_isSharedCheck_384_ == 0 {
v___x_377_ = v_x_367_;
v_isShared_378_ = v_isSharedCheck_384_;
state = 1; continue;
} else {
lean_inc(v_t_375_);
lean_dec(v_x_367_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_384_;
state = 1; continue;
}
}
}
}
1 => {
v___f_379_ = lean_alloc_closure(l_LazyList_join___redArg___lam__2___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_379_, 0, v_t_375_);
v___x_380_ = lean_mk_thunk(v___f_379_);
if v_isShared_378_ == 0 {
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_383_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_383_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join___redArg___lam__0(mut v_tl_385_: *mut lean_object, mut v_x_386_: *mut lean_object) -> *mut lean_object{
let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); 
v___x_387_ = l_LazyList_join___redArg(v_tl_385_);
return v___x_387_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_join(mut v_00_u03b1_388_: *mut lean_object, mut v_x_389_: *mut lean_object) -> *mut lean_object{
let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); 
v___x_390_ = l_LazyList_join___redArg(v_x_389_);
return v___x_390_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_bind___redArg(mut v_x_391_: *mut lean_object, mut v_f_392_: *mut lean_object) -> *mut lean_object{
let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
v___x_393_ = l_LazyList_map___redArg(v_f_392_, v_x_391_);
v___x_394_ = l_LazyList_join___redArg(v___x_393_);
return v___x_394_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_bind(mut v_00_u03b1_395_: *mut lean_object, mut v_00_u03b2_396_: *mut lean_object, mut v_x_397_: *mut lean_object, mut v_f_398_: *mut lean_object) -> *mut lean_object{
let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v___x_400_: *mut lean_object = core::ptr::null_mut(); 
v___x_399_ = l_LazyList_map___redArg(v_f_398_, v_x_397_);
v___x_400_ = l_LazyList_join___redArg(v___x_399_);
return v___x_400_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__0(mut v_00_u03b1_401_: *mut lean_object, mut v_00_u03b2_402_: *mut lean_object, mut v___y_403_: *mut lean_object, mut v___y_404_: *mut lean_object) -> *mut lean_object{
let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); 
v___x_405_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___x_405_, 0, lean_box(0));
lean_closure_set(v___x_405_, 1, lean_box(0));
lean_closure_set(v___x_405_, 2, v___y_403_);
v___x_406_ = l_LazyList_map___redArg(v___x_405_, v___y_404_);
return v___x_406_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__1(mut v_x_407_: *mut lean_object, mut v_y_408_: *mut lean_object) -> *mut lean_object{
let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); 
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_x_407_, v___x_409_);
v___x_411_ = l_LazyList_map___redArg(v_y_408_, v___x_410_);
return v___x_411_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__2(mut v_00_u03b1_412_: *mut lean_object, mut v_00_u03b2_413_: *mut lean_object, mut v_f_414_: *mut lean_object, mut v_x_415_: *mut lean_object) -> *mut lean_object{
let mut v___f_416_: *mut lean_object = core::ptr::null_mut(); let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); let mut v___x_418_: *mut lean_object = core::ptr::null_mut(); 
v___f_416_ = lean_alloc_closure(l_LazyList_isMonad___lam__1 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_416_, 0, v_x_415_);
v___x_417_ = l_LazyList_map___redArg(v___f_416_, v_f_414_);
v___x_418_ = l_LazyList_join___redArg(v___x_417_);
return v___x_418_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__3(mut v_a_419_: *mut lean_object, mut v_x_420_: *mut lean_object) -> *mut lean_object{
let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: *mut lean_object = core::ptr::null_mut(); 
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_422_, 0, v_a_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
return v___x_422_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__3___boxed(mut v_a_423_: *mut lean_object, mut v_x_424_: *mut lean_object) -> *mut lean_object{
let mut v_res_425_: *mut lean_object = core::ptr::null_mut(); 
v_res_425_ = l_LazyList_isMonad___lam__3(v_a_423_, v_x_424_);
lean_dec(v_x_424_);
return v_res_425_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__4(mut v_y_426_: *mut lean_object, mut v_a_427_: *mut lean_object) -> *mut lean_object{
let mut v___f_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: *mut lean_object = core::ptr::null_mut(); let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); let mut v___x_432_: *mut lean_object = core::ptr::null_mut(); 
v___f_428_ = lean_alloc_closure(l_LazyList_isMonad___lam__3___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_428_, 0, v_a_427_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_y_426_, v___x_429_);
v___x_431_ = l_LazyList_map___redArg(v___f_428_, v___x_430_);
v___x_432_ = l_LazyList_join___redArg(v___x_431_);
return v___x_432_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__5(mut v_00_u03b1_433_: *mut lean_object, mut v_00_u03b2_434_: *mut lean_object, mut v_x_435_: *mut lean_object, mut v_y_436_: *mut lean_object) -> *mut lean_object{
let mut v___f_437_: *mut lean_object = core::ptr::null_mut(); let mut v___x_438_: *mut lean_object = core::ptr::null_mut(); let mut v___x_439_: *mut lean_object = core::ptr::null_mut(); 
v___f_437_ = lean_alloc_closure(l_LazyList_isMonad___lam__4 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_437_, 0, v_y_436_);
v___x_438_ = l_LazyList_map___redArg(v___f_437_, v_x_435_);
v___x_439_ = l_LazyList_join___redArg(v___x_438_);
return v___x_439_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__6(mut v_y_440_: *mut lean_object, mut v_x_441_: *mut lean_object) -> *mut lean_object{
let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: *mut lean_object = core::ptr::null_mut(); 
v___x_442_ = lean_box(0);
v___x_443_ = lean_apply_1(v_y_440_, v___x_442_);
return v___x_443_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__6___boxed(mut v_y_444_: *mut lean_object, mut v_x_445_: *mut lean_object) -> *mut lean_object{
let mut v_res_446_: *mut lean_object = core::ptr::null_mut(); 
v_res_446_ = l_LazyList_isMonad___lam__6(v_y_444_, v_x_445_);
lean_dec(v_x_445_);
return v_res_446_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_isMonad___lam__7(mut v_00_u03b1_447_: *mut lean_object, mut v_00_u03b2_448_: *mut lean_object, mut v_x_449_: *mut lean_object, mut v_y_450_: *mut lean_object) -> *mut lean_object{
let mut v___f_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); 
v___f_451_ = lean_alloc_closure(l_LazyList_isMonad___lam__6___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_451_, 0, v_y_450_);
v___x_452_ = l_LazyList_map___redArg(v___f_451_, v_x_449_);
v___x_453_ = l_LazyList_join___redArg(v___x_452_);
return v___x_453_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_instAlternative___lam__0(mut v_00_u03b1_474_: *mut lean_object) -> *mut lean_object{
let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); 
v___x_475_ = lean_box(0);
return v___x_475_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_LazyList_instAlternative() -> *mut lean_object{
let mut v___x_478_: *mut lean_object = core::ptr::null_mut(); let mut v_toApplicative_479_: *mut lean_object = core::ptr::null_mut(); let mut v___f_480_: *mut lean_object = core::ptr::null_mut(); let mut v___x_481_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); 
v___x_478_ = l_LazyList_isMonad;
v_toApplicative_479_ = lean_ctor_get(v___x_478_, 0);
v___f_480_ = l_LazyList_instAlternative___closed__0;
v___x_481_ = l_LazyList_instAlternative___closed__1;
lean_inc_ref(v_toApplicative_479_);
v___x_482_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_482_, 0, v_toApplicative_479_);
lean_ctor_set(v___x_482_, 1, v___f_480_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
return v___x_482_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_approx___redArg(mut v_x_483_: *mut lean_object, mut v_x_484_: *mut lean_object) -> *mut lean_object{
let mut v_zero_485_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_486_: u8 = 0; let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v_one_488_: *mut lean_object = core::ptr::null_mut(); let mut v_n_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v_hd_491_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_495_: u8 = 0; let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_499_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_500_: u8 = 0; let mut v_t_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_485_ = lean_unsigned_to_nat(0);
v_isZero_486_ = lean_nat_dec_eq(v_x_483_, v_zero_485_);
if v_isZero_486_ == 1 {
let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_x_484_);
lean_dec(v_x_483_);
v___x_487_ = lean_box(0);
return v___x_487_;
} else {
let mut v_one_488_: *mut lean_object = core::ptr::null_mut(); let mut v_n_489_: *mut lean_object = core::ptr::null_mut(); 
v_one_488_ = lean_unsigned_to_nat(1);
v_n_489_ = lean_nat_sub(v_x_483_, v_one_488_);
lean_dec(v_x_483_);
match lean_obj_tag(v_x_484_)
{
0 => {
let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_n_489_);
v___x_490_ = lean_box(0);
return v___x_490_;
}
1 => {
let mut v_hd_491_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_495_: u8 = 0; let mut v_isSharedCheck_500_: u8 = 0; 
v_hd_491_ = lean_ctor_get(v_x_484_, 0);
v_tl_492_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_500_ = (!lean_is_exclusive(v_x_484_)) as u8;
if v_isSharedCheck_500_ == 0 {
v___x_494_ = v_x_484_;
v_isShared_495_ = v_isSharedCheck_500_;
state = 1; continue;
} else {
lean_inc(v_tl_492_);
lean_inc(v_hd_491_);
lean_dec(v_x_484_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
state = 1; continue;
}
}
_ => {
let mut v_t_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); 
v_t_501_ = lean_ctor_get(v_x_484_, 0);
lean_inc_ref(v_t_501_);
lean_dec_ref_known(v_x_484_, 1);
v___x_502_ = lean_nat_add(v_n_489_, v_one_488_);
lean_dec(v_n_489_);
v___x_503_ = lean_thunk_get_own(v_t_501_);
lean_dec_ref(v_t_501_);
v_x_483_ = v___x_502_;
v_x_484_ = v___x_503_;
state = 0; continue;
}
}
}
}
1 => {
v___x_496_ = l_LazyList_approx___redArg(v_n_489_, v_tl_492_);
if v_isShared_495_ == 0 {
lean_ctor_set(v___x_494_, 1, v___x_496_);
v___x_498_ = v___x_494_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_499_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_hd_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_approx(mut v_00_u03b1_505_: *mut lean_object, mut v_x_506_: *mut lean_object, mut v_x_507_: *mut lean_object) -> *mut lean_object{
let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); 
v___x_508_ = l_LazyList_approx___redArg(v_x_506_, v_x_507_);
return v___x_508_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate___redArg(mut v_f_509_: *mut lean_object, mut v_x_510_: *mut lean_object) -> *mut lean_object{
let mut v___f_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_x_510_);
v___f_511_ = lean_alloc_closure(l_LazyList_iterate___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_511_, 0, v_f_509_);
lean_closure_set(v___f_511_, 1, v_x_510_);
v___x_512_ = lean_mk_thunk(v___f_511_);
v___x_513_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_514_, 0, v_x_510_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate___redArg___lam__0(mut v_f_515_: *mut lean_object, mut v_x_516_: *mut lean_object, mut v_x_517_: *mut lean_object) -> *mut lean_object{
let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v___x_519_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_f_515_);
v___x_518_ = lean_apply_1(v_f_515_, v_x_516_);
v___x_519_ = l_LazyList_iterate___redArg(v_f_515_, v___x_518_);
return v___x_519_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate(mut v_00_u03b1_520_: *mut lean_object, mut v_f_521_: *mut lean_object, mut v_x_522_: *mut lean_object) -> *mut lean_object{
let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); 
v___x_523_ = l_LazyList_iterate___redArg(v_f_521_, v_x_522_);
return v___x_523_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate_u2082___redArg(mut v_f_524_: *mut lean_object, mut v_x_525_: *mut lean_object, mut v_x_526_: *mut lean_object) -> *mut lean_object{
let mut v___f_527_: *mut lean_object = core::ptr::null_mut(); let mut v___x_528_: *mut lean_object = core::ptr::null_mut(); let mut v___x_529_: *mut lean_object = core::ptr::null_mut(); let mut v___x_530_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_x_525_);
v___f_527_ = lean_alloc_closure(l_LazyList_iterate_u2082___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_527_, 0, v_f_524_);
lean_closure_set(v___f_527_, 1, v_x_525_);
lean_closure_set(v___f_527_, 2, v_x_526_);
v___x_528_ = lean_mk_thunk(v___f_527_);
v___x_529_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_529_, 0, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_530_, 0, v_x_525_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate_u2082___redArg___lam__0(mut v_f_531_: *mut lean_object, mut v_x_532_: *mut lean_object, mut v_x_533_: *mut lean_object, mut v_x_534_: *mut lean_object) -> *mut lean_object{
let mut v___x_535_: *mut lean_object = core::ptr::null_mut(); let mut v___x_536_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_f_531_);
lean_inc(v_x_533_);
v___x_535_ = lean_apply_2(v_f_531_, v_x_532_, v_x_533_);
v___x_536_ = l_LazyList_iterate_u2082___redArg(v_f_531_, v_x_533_, v___x_535_);
return v___x_536_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_iterate_u2082(mut v_00_u03b1_537_: *mut lean_object, mut v_f_538_: *mut lean_object, mut v_x_539_: *mut lean_object, mut v_x_540_: *mut lean_object) -> *mut lean_object{
let mut v___x_541_: *mut lean_object = core::ptr::null_mut(); 
v___x_541_ = l_LazyList_iterate_u2082___redArg(v_f_538_, v_x_539_, v_x_540_);
return v___x_541_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter___redArg___lam__1(mut v_p_542_: *mut lean_object, mut v_tl_543_: *mut lean_object, mut v_hd_544_: *mut lean_object, mut v_x_545_: *mut lean_object) -> *mut lean_object{
let mut v___x_546_: *mut lean_object = core::ptr::null_mut(); let mut v___x_547_: *mut lean_object = core::ptr::null_mut(); 
v___x_546_ = l_LazyList_filter___redArg(v_p_542_, v_tl_543_);
v___x_547_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_547_, 0, v_hd_544_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter___redArg___lam__2(mut v_t_548_: *mut lean_object, mut v_p_549_: *mut lean_object, mut v_x_550_: *mut lean_object) -> *mut lean_object{
let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); 
v___x_551_ = lean_thunk_get_own(v_t_548_);
v___x_552_ = l_LazyList_filter___redArg(v_p_549_, v___x_551_);
return v___x_552_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter___redArg___lam__2___boxed(mut v_t_553_: *mut lean_object, mut v_p_554_: *mut lean_object, mut v_x_555_: *mut lean_object) -> *mut lean_object{
let mut v_res_556_: *mut lean_object = core::ptr::null_mut(); 
v_res_556_ = l_LazyList_filter___redArg___lam__2(v_t_553_, v_p_554_, v_x_555_);
lean_dec_ref(v_t_553_);
return v_res_556_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter___redArg(mut v_p_557_: *mut lean_object, mut v_x_558_: *mut lean_object) -> *mut lean_object{
let mut v_hd_559_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); let mut v___x_562_: u8 = 0; let mut v___f_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___f_566_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); let mut v_t_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_572_: u8 = 0; let mut v___f_573_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v___x_576_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_577_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_578_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
match lean_obj_tag(v_x_558_)
{
0 => {
lean_dec_ref(v_p_557_);
return v_x_558_;
}
1 => {
let mut v_hd_559_: *mut lean_object = core::ptr::null_mut(); let mut v_tl_560_: *mut lean_object = core::ptr::null_mut(); let mut v___x_561_: *mut lean_object = core::ptr::null_mut(); let mut v___x_562_: u8 = 0; 
v_hd_559_ = lean_ctor_get(v_x_558_, 0);
lean_inc_n(v_hd_559_, 2);
v_tl_560_ = lean_ctor_get(v_x_558_, 1);
lean_inc(v_tl_560_);
lean_dec_ref_known(v_x_558_, 2);
lean_inc_ref(v_p_557_);
v___x_561_ = lean_apply_1(v_p_557_, v_hd_559_);
v___x_562_ = (lean_unbox(v___x_561_) as u8);
if v___x_562_ == 0 {
let mut v___f_563_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_hd_559_);
v___f_563_ = lean_alloc_closure(l_LazyList_filter___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_563_, 0, v_p_557_);
lean_closure_set(v___f_563_, 1, v_tl_560_);
v___x_564_ = lean_mk_thunk(v___f_563_);
v___x_565_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
} else {
let mut v___f_566_: *mut lean_object = core::ptr::null_mut(); let mut v___x_567_: *mut lean_object = core::ptr::null_mut(); let mut v___x_568_: *mut lean_object = core::ptr::null_mut(); 
v___f_566_ = lean_alloc_closure(l_LazyList_filter___redArg___lam__1 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_566_, 0, v_p_557_);
lean_closure_set(v___f_566_, 1, v_tl_560_);
lean_closure_set(v___f_566_, 2, v_hd_559_);
v___x_567_ = lean_mk_thunk(v___f_566_);
v___x_568_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
_ => {
let mut v_t_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_572_: u8 = 0; let mut v_isSharedCheck_578_: u8 = 0; 
v_t_569_ = lean_ctor_get(v_x_558_, 0);
v_isSharedCheck_578_ = (!lean_is_exclusive(v_x_558_)) as u8;
if v_isSharedCheck_578_ == 0 {
v___x_571_ = v_x_558_;
v_isShared_572_ = v_isSharedCheck_578_;
state = 1; continue;
} else {
lean_inc(v_t_569_);
lean_dec(v_x_558_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
state = 1; continue;
}
}
}
}
1 => {
v___f_573_ = lean_alloc_closure(l_LazyList_filter___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_573_, 0, v_t_569_);
lean_closure_set(v___f_573_, 1, v_p_557_);
v___x_574_ = lean_mk_thunk(v___f_573_);
if v_isShared_572_ == 0 {
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_577_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_577_ = lean_alloc_ctor(2, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter___redArg___lam__0(mut v_p_579_: *mut lean_object, mut v_tl_580_: *mut lean_object, mut v_x_581_: *mut lean_object) -> *mut lean_object{
let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); 
v___x_582_ = l_LazyList_filter___redArg(v_p_579_, v_tl_580_);
return v___x_582_;
}
#[no_mangle] pub unsafe extern "C" fn l_LazyList_filter(mut v_00_u03b1_583_: *mut lean_object, mut v_p_584_: *mut lean_object, mut v_x_585_: *mut lean_object) -> *mut lean_object{
let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); 
v___x_586_ = l_LazyList_filter___redArg(v_p_584_, v_x_585_);
return v___x_586_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_fib___closed__1() -> *mut lean_object{
let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); let mut v___x_589_: *mut lean_object = core::ptr::null_mut(); let mut v___f_590_: *mut lean_object = core::ptr::null_mut(); let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); 
v___x_588_ = lean_unsigned_to_nat(1);
v___x_589_ = lean_unsigned_to_nat(0);
v___f_590_ = l_fib___closed__0;
v___x_591_ = l_LazyList_iterate_u2082___redArg(v___f_590_, v___x_589_, v___x_588_);
return v___x_591_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_fib() -> *mut lean_object{
let mut v___x_592_: *mut lean_object = core::ptr::null_mut(); 
v___x_592_ = lean_obj_once(core::ptr::addr_of_mut!(l_fib___closed__1), core::ptr::addr_of_mut!(l_fib___closed__1_once), _init_l_fib___closed__1);
return v___x_592_;
}
#[no_mangle] pub unsafe extern "C" fn l_iota___lam__0(mut v_n_593_: *mut lean_object) -> *mut lean_object{
let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v___x_595_: *mut lean_object = core::ptr::null_mut(); 
v___x_594_ = lean_unsigned_to_nat(1);
v___x_595_ = lean_nat_add(v_n_593_, v___x_594_);
return v___x_595_;
}
#[no_mangle] pub unsafe extern "C" fn l_iota___lam__0___boxed(mut v_n_596_: *mut lean_object) -> *mut lean_object{
let mut v_res_597_: *mut lean_object = core::ptr::null_mut(); 
v_res_597_ = l_iota___lam__0(v_n_596_);
lean_dec(v_n_596_);
return v_res_597_;
}
#[no_mangle] pub unsafe extern "C" fn l_iota(mut v_i_599_: *mut lean_object) -> *mut lean_object{
let mut v___f_600_: *mut lean_object = core::ptr::null_mut(); let mut v___x_601_: *mut lean_object = core::ptr::null_mut(); 
v___f_600_ = l_iota___closed__0;
v___x_601_ = l_LazyList_iterate___redArg(v___f_600_, v_i_599_);
return v___x_601_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst___lam__0(mut v_x_604_: *mut lean_object, mut v_y_605_: *mut lean_object, mut v___x_606_: *mut lean_object, mut v_____r_607_: *mut lean_object) -> *mut lean_object{
let mut v___x_608_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v___x_612_: *mut lean_object = core::ptr::null_mut(); let mut v___x_613_: *mut lean_object = core::ptr::null_mut(); let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); let mut v___x_615_: *mut lean_object = core::ptr::null_mut(); let mut v___x_616_: *mut lean_object = core::ptr::null_mut(); let mut v___x_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_618_: *mut lean_object = core::ptr::null_mut(); 
v___x_608_ = l_Nat_reprFast(v_x_604_);
v___x_609_ = l_tst___lam__0___closed__0;
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
v___x_611_ = l_Nat_reprFast(v_y_605_);
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
lean_dec_ref(v___x_611_);
v___x_613_ = l_tst___lam__0___closed__1;
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
v___x_615_ = l_Nat_reprFast(v___x_606_);
v___x_616_ = lean_string_append(v___x_614_, v___x_615_);
lean_dec_ref(v___x_615_);
v___x_617_ = lean_box(0);
v___x_618_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst___lam__1(mut v_x_622_: *mut lean_object, mut v_y_623_: *mut lean_object) -> *mut lean_object{
let mut v___x_624_: *mut lean_object = core::ptr::null_mut(); let mut v___x_625_: *mut lean_object = core::ptr::null_mut(); let mut v___f_626_: *mut lean_object = core::ptr::null_mut(); let mut v___y_628_: *mut lean_object = core::ptr::null_mut(); let mut v___x_629_: *mut lean_object = core::ptr::null_mut(); let mut v___x_630_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: u8 = 0; let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_624_ = lean_unsigned_to_nat(5);
v___x_625_ = lean_nat_add(v_x_622_, v_y_623_);
lean_inc(v___x_625_);
v___f_626_ = lean_alloc_closure(l_tst___lam__0 as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___f_626_, 0, v_x_622_);
lean_closure_set(v___f_626_, 1, v_y_623_);
lean_closure_set(v___f_626_, 2, v___x_625_);
v___x_631_ = lean_nat_dec_lt(v___x_624_, v___x_625_);
lean_dec(v___x_625_);
if v___x_631_ == 0 {
let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); 
v___x_632_ = lean_box(0);
v___y_628_ = v___x_632_;
state = 1; continue;
} else {
let mut v___x_633_: *mut lean_object = core::ptr::null_mut(); 
v___x_633_ = l_tst___lam__1___closed__0;
v___y_628_ = v___x_633_;
state = 1; continue;
}
}
1 => {
lean_inc(v___y_628_);
v___x_629_ = l_LazyList_map___redArg(v___f_626_, v___y_628_);
v___x_630_ = l_LazyList_join___redArg(v___x_629_);
return v___x_630_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst___lam__2(mut v___x_634_: *mut lean_object, mut v___x_635_: *mut lean_object, mut v___x_636_: *mut lean_object, mut v_x_637_: *mut lean_object) -> *mut lean_object{
let mut v___f_638_: *mut lean_object = core::ptr::null_mut(); let mut v___x_639_: *mut lean_object = core::ptr::null_mut(); let mut v___x_640_: *mut lean_object = core::ptr::null_mut(); let mut v___x_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v___x_644_: *mut lean_object = core::ptr::null_mut(); let mut v___x_645_: *mut lean_object = core::ptr::null_mut(); 
v___f_638_ = lean_alloc_closure(l_tst___lam__1 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_638_, 0, v_x_637_);
v___x_639_ = lean_unsigned_to_nat(4);
v___x_640_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_634_);
v___x_641_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_641_, 0, v___x_635_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_642_, 0, v___x_636_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_List_toLazy___redArg(v___x_642_);
v___x_644_ = l_LazyList_map___redArg(v___f_638_, v___x_643_);
v___x_645_ = l_LazyList_join___redArg(v___x_644_);
return v___x_645_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst___closed__4() -> *mut lean_object{
let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); 
v___x_659_ = l_tst___closed__3;
v___x_660_ = l_List_toLazy___redArg(v___x_659_);
return v___x_660_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst___closed__5() -> *mut lean_object{
let mut v___x_661_: *mut lean_object = core::ptr::null_mut(); let mut v___f_662_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: *mut lean_object = core::ptr::null_mut(); 
v___x_661_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst___closed__4), core::ptr::addr_of_mut!(l_tst___closed__4_once), _init_l_tst___closed__4);
v___f_662_ = l_tst___closed__0;
v___x_663_ = l_LazyList_map___redArg(v___f_662_, v___x_661_);
return v___x_663_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst___closed__6() -> *mut lean_object{
let mut v___x_664_: *mut lean_object = core::ptr::null_mut(); let mut v___x_665_: *mut lean_object = core::ptr::null_mut(); 
v___x_664_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst___closed__5), core::ptr::addr_of_mut!(l_tst___closed__5_once), _init_l_tst___closed__5);
v___x_665_ = l_LazyList_join___redArg(v___x_664_);
return v___x_665_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst() -> *mut lean_object{
let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); 
v___x_666_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst___closed__6), core::ptr::addr_of_mut!(l_tst___closed__6_once), _init_l_tst___closed__6);
return v___x_666_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_x_667_: *mut lean_object) -> *mut lean_object{
let mut v___x_668_: *mut lean_object = core::ptr::null_mut(); let mut v___x_669_: *mut lean_object = core::ptr::null_mut(); 
v___x_668_ = lean_unsigned_to_nat(100);
v___x_669_ = lean_nat_add(v_x_667_, v___x_668_);
return v___x_669_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v_x_670_: *mut lean_object) -> *mut lean_object{
let mut v_res_671_: *mut lean_object = core::ptr::null_mut(); 
v_res_671_ = l_main___lam__0(v_x_670_);
lean_dec(v_x_670_);
return v_res_671_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1(mut v_x_672_: *mut lean_object) -> *mut lean_object{
let mut v___x_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_674_: *mut lean_object = core::ptr::null_mut(); 
v___x_673_ = lean_unsigned_to_nat(10);
v___x_674_ = lean_nat_add(v_x_672_, v___x_673_);
return v___x_674_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__1___boxed(mut v_x_675_: *mut lean_object) -> *mut lean_object{
let mut v_res_676_: *mut lean_object = core::ptr::null_mut(); 
v_res_676_ = l_main___lam__1(v_x_675_);
lean_dec(v_x_675_);
return v_res_676_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__2(mut v___x_677_: *mut lean_object, mut v_x_678_: *mut lean_object) -> u8{
let mut v___x_679_: *mut lean_object = core::ptr::null_mut(); let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); let mut v___x_681_: u8 = 0; 
v___x_679_ = lean_unsigned_to_nat(2);
v___x_680_ = lean_nat_mod(v_x_678_, v___x_679_);
v___x_681_ = lean_nat_dec_eq(v___x_680_, v___x_677_);
lean_dec(v___x_680_);
return v___x_681_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__2___boxed(mut v___x_682_: *mut lean_object, mut v_x_683_: *mut lean_object) -> *mut lean_object{
let mut v_res_684_: u8 = 0; let mut v_r_685_: *mut lean_object = core::ptr::null_mut(); 
v_res_684_ = l_main___lam__2(v___x_682_, v_x_683_);
lean_dec(v_x_683_);
lean_dec(v___x_682_);
v_r_685_ = lean_box((v_res_684_) as usize);
return v_r_685_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_686_: *mut lean_object) -> *mut lean_object{
let mut v___x_688_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); 
v___x_688_ = lean_get_stdout();
v_putStr_689_ = lean_ctor_get(v___x_688_, 4);
lean_inc_ref(v_putStr_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_apply_2(v_putStr_689_, v_s_686_, lean_box(0));
return v___x_690_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_691_: *mut lean_object, mut v_a_692_: *mut lean_object) -> *mut lean_object{
let mut v_res_693_: *mut lean_object = core::ptr::null_mut(); 
v_res_693_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_691_);
return v_res_693_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_694_: *mut lean_object) -> *mut lean_object{
let mut v___x_696_: u32 = 0; let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_698_: *mut lean_object = core::ptr::null_mut(); 
v___x_696_ = 10;
v___x_697_ = lean_string_push(v_s_694_, v___x_696_);
v___x_698_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_697_);
return v___x_698_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_699_: *mut lean_object, mut v_a_700_: *mut lean_object) -> *mut lean_object{
let mut v_res_701_: *mut lean_object = core::ptr::null_mut(); 
v_res_701_ = l_IO_println___at___00main_spec__1(v_s_699_);
return v_res_701_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4(mut v_x_703_: *mut lean_object, mut v_x_704_: *mut lean_object) -> *mut lean_object{
let mut v_head_705_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_706_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); let mut v___x_708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_704_) == 0 {
return v_x_703_;
} else {
let mut v_head_705_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_706_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); let mut v___x_708_: *mut lean_object = core::ptr::null_mut(); let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); 
v_head_705_ = lean_ctor_get(v_x_704_, 0);
lean_inc(v_head_705_);
v_tail_706_ = lean_ctor_get(v_x_704_, 1);
lean_inc(v_tail_706_);
lean_dec_ref_known(v_x_704_, 2);
v___x_707_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4___closed__0;
v___x_708_ = lean_string_append(v_x_703_, v___x_707_);
v___x_709_ = l_Nat_reprFast(v_head_705_);
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
lean_dec_ref(v___x_709_);
v_x_703_ = v___x_710_;
v_x_704_ = v_tail_706_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__2_spec__3(mut v_x_715_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_715_) == 0 {
let mut v___x_716_: *mut lean_object = core::ptr::null_mut(); 
v___x_716_ = l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__0;
return v___x_716_;
} else {
let mut v_tail_717_: *mut lean_object = core::ptr::null_mut(); 
v_tail_717_ = lean_ctor_get(v_x_715_, 1);
if lean_obj_tag(v_tail_717_) == 0 {
let mut v_head_718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); let mut v___x_720_: *mut lean_object = core::ptr::null_mut(); let mut v___x_721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_722_: *mut lean_object = core::ptr::null_mut(); let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); 
v_head_718_ = lean_ctor_get(v_x_715_, 0);
lean_inc(v_head_718_);
lean_dec_ref_known(v_x_715_, 2);
v___x_719_ = l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__1;
v___x_720_ = l_Nat_reprFast(v_head_718_);
v___x_721_ = lean_string_append(v___x_719_, v___x_720_);
lean_dec_ref(v___x_720_);
v___x_722_ = l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__2;
v___x_723_ = lean_string_append(v___x_721_, v___x_722_);
return v___x_723_;
} else {
let mut v_head_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: *mut lean_object = core::ptr::null_mut(); let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: *mut lean_object = core::ptr::null_mut(); let mut v___x_728_: *mut lean_object = core::ptr::null_mut(); let mut v___x_729_: u32 = 0; let mut v___x_730_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_717_);
v_head_724_ = lean_ctor_get(v_x_715_, 0);
lean_inc(v_head_724_);
lean_dec_ref_known(v_x_715_, 2);
v___x_725_ = l_List_toString___at___00IO_println___at___00main_spec__2_spec__3___closed__1;
v___x_726_ = l_Nat_reprFast(v_head_724_);
v___x_727_ = lean_string_append(v___x_725_, v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__2_spec__3_spec__4(v___x_727_, v_tail_717_);
v___x_729_ = 93;
v___x_730_ = lean_string_push(v___x_728_, v___x_729_);
return v___x_730_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2(mut v_s_731_: *mut lean_object) -> *mut lean_object{
let mut v___x_733_: *mut lean_object = core::ptr::null_mut(); let mut v___x_734_: u32 = 0; let mut v___x_735_: *mut lean_object = core::ptr::null_mut(); let mut v___x_736_: *mut lean_object = core::ptr::null_mut(); 
v___x_733_ = l_List_toString___at___00IO_println___at___00main_spec__2_spec__3(v_s_731_);
v___x_734_ = 10;
v___x_735_ = lean_string_push(v___x_733_, v___x_734_);
v___x_736_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_735_);
return v___x_736_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2___boxed(mut v_s_737_: *mut lean_object, mut v_a_738_: *mut lean_object) -> *mut lean_object{
let mut v_res_739_: *mut lean_object = core::ptr::null_mut(); 
v_res_739_ = l_IO_println___at___00main_spec__2(v_s_737_);
return v_res_739_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_742_: u8) -> *mut lean_object{
let mut v___y_745_: *mut lean_object = core::ptr::null_mut(); let mut v___x_746_: u32 = 0; let mut v___x_747_: *mut lean_object = core::ptr::null_mut(); let mut v___x_748_: *mut lean_object = core::ptr::null_mut(); let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); let mut v___x_750_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_742_ == 0 {
let mut v___x_749_: *mut lean_object = core::ptr::null_mut(); 
v___x_749_ = l_IO_println___at___00main_spec__0___closed__0;
v___y_745_ = v___x_749_;
state = 1; continue;
} else {
let mut v___x_750_: *mut lean_object = core::ptr::null_mut(); 
v___x_750_ = l_IO_println___at___00main_spec__0___closed__1;
v___y_745_ = v___x_750_;
state = 1; continue;
}
}
1 => {
v___x_746_ = 10;
lean_inc_ref(v___y_745_);
v___x_747_ = lean_string_push(v___y_745_, v___x_746_);
v___x_748_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_747_);
return v___x_748_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_751_: *mut lean_object, mut v_a_752_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_753_: u8 = 0; let mut v_res_754_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_753_ = (lean_unbox(v_s_751_) as u8);
v_res_754_ = l_IO_println___at___00main_spec__0(v_s_boxed_753_);
return v_res_754_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> u8{
let mut v___x_755_: *mut lean_object = core::ptr::null_mut(); let mut v___x_756_: u8 = 0; 
v___x_755_ = l_tst;
v___x_756_ = l_LazyList_isEmpty___redArg(v___x_755_);
return v___x_756_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_758_: *mut lean_object = core::ptr::null_mut(); let mut v___x_759_: *mut lean_object = core::ptr::null_mut(); let mut v___x_760_: *mut lean_object = core::ptr::null_mut(); 
v___x_758_ = l_tst;
v___x_759_ = l_main___closed__1;
v___x_760_ = l_LazyList_head___redArg(v___x_759_, v___x_758_);
return v___x_760_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_762_: *mut lean_object = core::ptr::null_mut(); let mut v___x_763_: *mut lean_object = core::ptr::null_mut(); 
v___x_762_ = lean_unsigned_to_nat(0);
v___x_763_ = l_iota(v___x_762_);
return v___x_763_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_764_: *mut lean_object = core::ptr::null_mut(); let mut v___f_765_: *mut lean_object = core::ptr::null_mut(); let mut v___x_766_: *mut lean_object = core::ptr::null_mut(); 
v___x_764_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___f_765_ = l_main___closed__3;
v___x_766_ = l_LazyList_map___redArg(v___f_765_, v___x_764_);
return v___x_766_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_767_: *mut lean_object = core::ptr::null_mut(); let mut v___x_768_: *mut lean_object = core::ptr::null_mut(); let mut v___x_769_: *mut lean_object = core::ptr::null_mut(); 
v___x_767_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_768_ = l_fib;
v___x_769_ = l_LazyList_interleave___redArg(v___x_768_, v___x_767_);
return v___x_769_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_770_: *mut lean_object = core::ptr::null_mut(); let mut v_n_771_: *mut lean_object = core::ptr::null_mut(); let mut v___x_772_: *mut lean_object = core::ptr::null_mut(); 
v___x_770_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_n_771_ = lean_unsigned_to_nat(40);
v___x_772_ = l_LazyList_approx___redArg(v_n_771_, v___x_770_);
return v___x_772_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_776_: *mut lean_object = core::ptr::null_mut(); let mut v___f_777_: *mut lean_object = core::ptr::null_mut(); let mut v___x_778_: *mut lean_object = core::ptr::null_mut(); 
v___x_776_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___f_777_ = l_main___closed__8;
v___x_778_ = l_LazyList_map___redArg(v___f_777_, v___x_776_);
return v___x_778_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> *mut lean_object{
let mut v___x_779_: *mut lean_object = core::ptr::null_mut(); let mut v___f_780_: *mut lean_object = core::ptr::null_mut(); let mut v___x_781_: *mut lean_object = core::ptr::null_mut(); 
v___x_779_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___f_780_ = l_main___closed__9;
v___x_781_ = l_LazyList_filter___redArg(v___f_780_, v___x_779_);
return v___x_781_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> *mut lean_object{
let mut v___x_782_: *mut lean_object = core::ptr::null_mut(); let mut v_n_783_: *mut lean_object = core::ptr::null_mut(); let mut v___x_784_: *mut lean_object = core::ptr::null_mut(); 
v___x_782_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v_n_783_ = lean_unsigned_to_nat(40);
v___x_784_ = l_LazyList_approx___redArg(v_n_783_, v___x_782_);
return v___x_784_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_786_: u8 = 0; let mut v___x_787_: *mut lean_object = core::ptr::null_mut(); 
v___x_786_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_787_ = l_IO_println___at___00main_spec__0(v___x_786_);
if lean_obj_tag(v___x_787_) == 0 {
let mut v___x_788_: *mut lean_object = core::ptr::null_mut(); let mut v___x_789_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_787_, 1);
v___x_788_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_789_ = l_IO_println___at___00main_spec__1(v___x_788_);
if lean_obj_tag(v___x_789_) == 0 {
let mut v___x_790_: *mut lean_object = core::ptr::null_mut(); let mut v___x_791_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_789_, 1);
v___x_790_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_791_ = l_IO_println___at___00main_spec__2(v___x_790_);
if lean_obj_tag(v___x_791_) == 0 {
let mut v___x_792_: *mut lean_object = core::ptr::null_mut(); let mut v___x_793_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_791_, 1);
v___x_792_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_793_ = l_IO_println___at___00main_spec__2(v___x_792_);
return v___x_793_;
} else {
return v___x_791_;
}
} else {
return v___x_789_;
}
} else {
return v___x_787_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_794_: *mut lean_object) -> *mut lean_object{
let mut v_res_795_: *mut lean_object = core::ptr::null_mut(); 
v_res_795_ = _lean_main();
return v_res_795_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_lazylist(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_LazyList_instAlternative = _init_l_LazyList_instAlternative();
lean_mark_persistent(l_LazyList_instAlternative);
l_fib = _init_l_fib();
lean_mark_persistent(l_fib);
l_tst = _init_l_tst();
lean_mark_persistent(l_tst);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_lazylist(1 /* builtin */);
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

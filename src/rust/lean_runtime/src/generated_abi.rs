#![allow(non_camel_case_types)]

#[repr(C)]
pub struct lean_object {
    pub m_rc: i32,
    pub m_cs_sz: u16,
    pub m_other: u8,
    pub m_tag: u8,
}

#[repr(C)]
pub struct lean_once_cell {
    pub state: i32,
    pub lock: i32,
}

macro_rules! lean_apply_fns {
    ($($name:ident ($($arg:ident),*));* $(;)?) => {
        extern "C" {
            $(
                pub fn $name(obj: *mut lean_object, $($arg: *mut lean_object),*) -> *mut lean_object;
            )*
        }
    };
}

lean_apply_fns! {
    lean_apply_1(a1);
    lean_apply_2(a1, a2);
    lean_apply_3(a1, a2, a3);
    lean_apply_4(a1, a2, a3, a4);
    lean_apply_5(a1, a2, a3, a4, a5);
    lean_apply_6(a1, a2, a3, a4, a5, a6);
    lean_apply_7(a1, a2, a3, a4, a5, a6, a7);
    lean_apply_8(a1, a2, a3, a4, a5, a6, a7, a8);
    lean_apply_9(a1, a2, a3, a4, a5, a6, a7, a8, a9);
    lean_apply_10(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
    lean_apply_11(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
    lean_apply_12(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
    lean_apply_13(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
    lean_apply_14(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
    lean_apply_15(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
    lean_apply_16(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
}

macro_rules! lean_ctor_accessors {
    ($($set:ident, $get:ident => $t:ty);* $(;)?) => {
        extern "C" {
            $(
                pub fn $set(obj: *mut lean_object, offset: core::ffi::c_uint, value: $t);
                pub fn $get(obj: *mut lean_object, offset: core::ffi::c_uint) -> $t;
            )*
        }
    };
}

lean_ctor_accessors! {
    lean_ctor_set_usize,   lean_ctor_get_usize   => usize;
    lean_ctor_set_float,   lean_ctor_get_float   => f64;
    lean_ctor_set_float32, lean_ctor_get_float32 => f32;
    lean_ctor_set_uint8,   lean_ctor_get_uint8   => u8;
    lean_ctor_set_uint16,  lean_ctor_get_uint16  => u16;
    lean_ctor_set_uint32,  lean_ctor_get_uint32  => u32;
    lean_ctor_set_uint64,  lean_ctor_get_uint64  => u64;
}

macro_rules! lean_boxing {
    ($($unbox:ident, $box_fn:ident => $t:ty);* $(;)?) => {
        extern "C" {
            $(
                pub fn $unbox(o: *mut lean_object) -> $t;
                pub fn $box_fn(v: $t) -> *mut lean_object;
            )*
        }
    };
}

lean_boxing! {
    lean_unbox_uint32,  lean_box_uint32  => u32;
    lean_unbox_uint64,  lean_box_uint64  => u64;
    lean_unbox_usize,   lean_box_usize   => usize;
    lean_unbox_float,   lean_box_float   => f64;
    lean_unbox_float32, lean_box_float32 => f32;
}

macro_rules! lean_once_fns {
    ($($name:ident => $t:ty);* $(;)?) => {
        extern "C" {
            $(
                pub fn $name(
                    v: *mut $t,
                    t: *mut lean_once_cell,
                    f: unsafe extern "C" fn() -> $t,
                ) -> $t;
            )*
        }
    };
}

lean_once_fns! {
    lean_float_once   => f64;
    lean_float32_once => f32;
    lean_uint8_once   => u8;
    lean_uint16_once  => u16;
    lean_uint32_once  => u32;
    lean_uint64_once  => u64;
    lean_usize_once   => usize;
    lean_obj_once     => *mut lean_object;
}

// NON-REPETITIVE C BINDINGS

extern "C" {
    pub fn lean_box(n: usize) -> *mut lean_object;
    pub fn lean_unbox(o: *mut lean_object) -> usize;
    pub fn lean_dec(o: *mut lean_object);
    pub fn lean_inc(o: *mut lean_object);
    pub fn lean_alloc_ctor(
        tag: core::ffi::c_uint,
        num_objs: core::ffi::c_uint,
        scalar_size: core::ffi::c_uint,
    ) -> *mut lean_object;
    pub fn lean_ctor_set(obj: *mut lean_object, index: core::ffi::c_uint, value: *mut lean_object);
    pub fn lean_ctor_get(obj: *mut lean_object, index: core::ffi::c_uint) -> *mut lean_object;
    pub fn lean_ctor_release(obj: *mut lean_object, index: core::ffi::c_uint);
    pub fn lean_ctor_set_tag(obj: *mut lean_object, tag: core::ffi::c_uint);
    pub fn lean_is_exclusive(o: *mut lean_object) -> bool;
    pub fn lean_is_scalar(obj: *const lean_object) -> u8;
    pub fn lean_alloc_closure(
        fun_ptr: *mut core::ffi::c_void,
        arity: core::ffi::c_uint,
        num_fixed: core::ffi::c_uint,
    ) -> *mut lean_object;
    pub fn lean_closure_set(
        obj: *mut lean_object,
        index: core::ffi::c_uint,
        value: *mut lean_object,
    );
    pub fn lean_apply_m(
        obj: *mut lean_object,
        nargs: usize,
        args: *mut *mut lean_object,
    ) -> *mut lean_object;

    pub fn lean_mk_string_unchecked(
        s: *const core::ffi::c_char,
        sz: usize,
        len: usize,
    ) -> *mut lean_object;
    pub fn lean_mk_string(s: *const core::ffi::c_char) -> *mut lean_object;
    pub fn lean_unsigned_to_nat(v: core::ffi::c_uint) -> *mut lean_object;
    pub fn lean_cstr_to_nat(s: *const core::ffi::c_char) -> *mut lean_object;

    pub fn lean_mark_persistent(o: *mut lean_object);
    pub fn lean_io_result_mk_ok(o: *mut lean_object) -> *mut lean_object;
    pub fn lean_obj_tag(o: *mut lean_object) -> core::ffi::c_uint;
    pub fn lean_del_object(o: *mut lean_object);
    pub fn lean_dec_ref(o: *mut lean_object);
    pub fn lean_dec_ref_known(o: *mut lean_object, n: usize);

    pub fn lean_setup_args(
        argc: core::ffi::c_int,
        argv: *mut *mut core::ffi::c_char,
    ) -> *mut *mut core::ffi::c_char;
    pub fn lean_initialize();
    pub fn lean_initialize_runtime_module();
    pub fn lean_init_task_manager();
    pub fn lean_finalize_task_manager();
    pub fn lean_run_main(
        f: unsafe extern "C" fn(core::ffi::c_int, *mut *mut core::ffi::c_char) -> *mut lean_object,
        argc: core::ffi::c_int,
        argv: *mut *mut core::ffi::c_char,
    ) -> *mut lean_object;

    pub fn lean_io_mark_end_initialization();
    pub fn lean_io_result_is_error(res: *mut lean_object) -> bool;
    pub fn lean_io_result_is_ok(res: *mut lean_object) -> bool;
    pub fn lean_io_result_get_value(res: *mut lean_object) -> *mut lean_object;
    pub fn lean_io_result_get_error(res: *mut lean_object) -> *mut lean_object;
    pub fn lean_io_result_show_error(res: *mut lean_object);

    pub fn lean_inc_ref(o: *mut lean_object);
    pub fn lean_inc_ref_n(o: *mut lean_object, n: usize);
    pub fn lean_inc_n(o: *mut lean_object, n: usize);
}

// GENERIC TYPES AND TRAITS

#[repr(C)]
pub struct lean_ctor_object<const N: usize> {
    pub m_header: lean_object,
    pub m_objs: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_closure_object<const N: usize> {
    pub m_header: lean_object,
    pub m_fun: *const core::ffi::c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    pub m_objs: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_array_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_sarray_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: [u8; N],
}

#[repr(C)]
pub struct lean_string_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_length: usize,
    pub m_data: [u8; N],
}

macro_rules! impl_sync_for_lean_objs {
    // Notice the $(,)? here which correctly allows a trailing comma
    ($($name:ident),* $(,)?) => {
        $(
            unsafe impl<const N: usize> Sync for $name<N> {}
        )*
    };
}

impl_sync_for_lean_objs! {
    lean_ctor_object,
    lean_closure_object,
    lean_array_object,
    lean_sarray_object,
    lean_string_object,
}

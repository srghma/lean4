use core::ffi::c_void;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_closure::lean_alloc_closure, lean_alloc_ctor::lean_alloc_ctor,
        lean_box::lean_box, lean_closure_set::lean_closure_set, lean_ctor_set::lean_ctor_set,
        lean_dec::lean_dec, lean_dec_ref::lean_dec_ref, lean_inc_n::lean_inc_n,
        lean_unbox_usize::lean_unbox_usize,
    },
};

use crate::r#priv::{
    lean_io_prim_handle_flush::lean_io_prim_handle_flush,
    lean_io_prim_handle_get_line::lean_io_prim_handle_get_line,
    lean_io_prim_handle_is_tty::lean_io_prim_handle_is_tty,
    lean_io_prim_handle_put_str::lean_io_prim_handle_put_str,
    lean_io_prim_handle_read::lean_io_prim_handle_read,
    lean_io_prim_handle_write::lean_io_prim_handle_write,
};

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LeanStreamTag {
    Stream = 0,
}

const STREAM_NUM_FIELDS: u32 = 6;
const STREAM_SCALAR_SIZE: u32 = 0;

const STREAM_FLUSH_IDX: u32 = 0;
const STREAM_READ_IDX: u32 = 1;
const STREAM_WRITE_IDX: u32 = 2;
const STREAM_GET_LINE_IDX: u32 = 3;
const STREAM_PUT_STR_IDX: u32 = 4;
const STREAM_IS_TTY_IDX: u32 = 5;

unsafe fn lean_io_fs_handle_flush_boxed(
    h: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let result = lean_io_prim_handle_flush(h);
    lean_dec(h);
    result
}

unsafe fn lean_io_fs_handle_read_boxed(
    h: *mut LeanObject,
    bytes: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let nbytes = lean_unbox_usize(bytes);
    lean_dec(bytes);
    let result = lean_io_prim_handle_read(h, nbytes);
    lean_dec(h);
    result
}

unsafe fn lean_io_fs_handle_write_boxed(
    h: *mut LeanObject,
    buffer: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let result = lean_io_prim_handle_write(h, buffer);
    lean_dec_ref(buffer);
    lean_dec(h);
    result
}

unsafe fn lean_io_fs_handle_get_line_boxed(
    h: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let result = lean_io_prim_handle_get_line(h);
    lean_dec(h);
    result
}

unsafe fn lean_io_fs_handle_put_str_boxed(
    h: *mut LeanObject,
    s: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let result = lean_io_prim_handle_put_str(h, s);
    lean_dec_ref(s);
    lean_dec(h);
    result
}

unsafe fn lean_io_fs_handle_is_tty_boxed(
    h: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    let result = lean_io_prim_handle_is_tty(h);
    lean_dec(h);
    lean_box(result as usize)
}

pub unsafe fn lean_stream_of_handle(h: *mut LeanObject) -> *mut LeanObject {
    // Mirrors `IO.FS.Stream.ofHandle` from `src/Init/System/IO.lean`.
    // The generated Lean code only closes over the runtime handle primitives,
    // so this native version imports those FFI entry points directly.
    lean_inc_n(h, 5);

    let flush = lean_alloc_closure(lean_io_fs_handle_flush_boxed as *mut c_void, 2, 1);
    lean_closure_set(flush, 0, h);

    let read = lean_alloc_closure(lean_io_fs_handle_read_boxed as *mut c_void, 3, 1);
    lean_closure_set(read, 0, h);

    let write = lean_alloc_closure(lean_io_fs_handle_write_boxed as *mut c_void, 3, 1);
    lean_closure_set(write, 0, h);

    let get_line = lean_alloc_closure(lean_io_fs_handle_get_line_boxed as *mut c_void, 2, 1);
    lean_closure_set(get_line, 0, h);

    let put_str = lean_alloc_closure(lean_io_fs_handle_put_str_boxed as *mut c_void, 3, 1);
    lean_closure_set(put_str, 0, h);

    let is_tty = lean_alloc_closure(lean_io_fs_handle_is_tty_boxed as *mut c_void, 2, 1);
    lean_closure_set(is_tty, 0, h);

    let stream = lean_alloc_ctor(
        LeanStreamTag::Stream as u32,
        STREAM_NUM_FIELDS,
        STREAM_SCALAR_SIZE,
    );
    lean_ctor_set(stream, STREAM_FLUSH_IDX, flush);
    lean_ctor_set(stream, STREAM_READ_IDX, read);
    lean_ctor_set(stream, STREAM_WRITE_IDX, write);
    lean_ctor_set(stream, STREAM_GET_LINE_IDX, get_line);
    lean_ctor_set(stream, STREAM_PUT_STR_IDX, put_str);
    lean_ctor_set(stream, STREAM_IS_TTY_IDX, is_tty);
    stream
}

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint32::lean_ctor_set_uint32,
    },
};

const IO_ERROR_ONE_OBJ_FIELDS: u32 = 1;
const IO_ERROR_TWO_OBJ_FIELDS: u32 = 2;
const IO_ERROR_SCALAR_SIZE: u32 = core::mem::size_of::<u32>() as u32;
const IO_ERROR_FILE_IDX: u32 = 0;
const IO_ERROR_DETAILS_IDX: u32 = 1;
const IO_ERROR_U32_OFFSET_ONE_OBJ: u32 = core::mem::size_of::<*mut LeanObject>() as u32;
const IO_ERROR_U32_OFFSET_TWO_OBJS: u32 = (core::mem::size_of::<*mut LeanObject>() * 2) as u32;

#[inline]
pub(crate) unsafe fn mk_io_error_one_obj(
    tag: u8,
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    let obj = lean_alloc_ctor(tag as u32, IO_ERROR_ONE_OBJ_FIELDS, IO_ERROR_SCALAR_SIZE);
    lean_ctor_set(obj, 0, details);
    lean_ctor_set_uint32(obj, IO_ERROR_U32_OFFSET_ONE_OBJ, os_code);
    obj
}

#[inline]
pub(crate) unsafe fn mk_io_error_two_objs(
    tag: u8,
    field0: *mut LeanObject,
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    let obj = lean_alloc_ctor(tag as u32, IO_ERROR_TWO_OBJ_FIELDS, IO_ERROR_SCALAR_SIZE);
    lean_ctor_set(obj, IO_ERROR_FILE_IDX, field0);
    lean_ctor_set(obj, IO_ERROR_DETAILS_IDX, details);
    lean_ctor_set_uint32(obj, IO_ERROR_U32_OFFSET_TWO_OBJS, os_code);
    obj
}

use leanh_l1::datatypes::LeanObject;

use crate::r#priv::lean_runtime_get_external_data::lean_runtime_get_external_data;

pub unsafe fn lean_io_prim_handle_is_tty(h: *const LeanObject) -> bool {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    libc::isatty(libc::fileno(fp)) != 0
}

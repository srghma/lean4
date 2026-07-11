// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
// #[inline]
// pub unsafe fn lean_mpz_clear(obj: *mut LeanObject) {
//     unsafe {
//         let mpz = &mut (*(obj as *mut LeanMpzObject)).m_value[0];
//         if !mpz.mp_d.is_null() {
//             libc::free(mpz.mp_d.cast());
//             mpz.mp_alloc = 0;
//             mpz.mp_size = 0;
//             mpz.mp_d = ptr::null_mut();
//         }
//     }
// }

use crate::{
    datatypes::LeanObject,
    r#priv::{lean_is_ctor::lean_is_ctor, lean_to_ctor::lean_to_ctor},
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 28 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_num_objs(obj: *const LeanObject) -> usize {
    unsafe {
        debug_assert!(lean_is_ctor(obj));
        (*lean_to_ctor(obj)).m_header.other as usize
    }
}

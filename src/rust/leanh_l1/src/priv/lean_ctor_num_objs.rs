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
    common1::lean_ptr_tag,
    datatypes::{LEAN_MAX_CTOR_TAG, LeanObject},
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 28 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_num_objs(obj: *mut LeanObject) -> usize {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (*obj).other as usize
    }
}

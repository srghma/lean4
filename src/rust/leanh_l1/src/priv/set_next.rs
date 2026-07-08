// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.

use crate::datatypes::LeanObject;

#[inline(always)]
pub unsafe fn set_next(o: *mut LeanObject, next: *mut LeanObject) {
    #[cfg(target_pointer_width = "64")]
    {
        use std::ptr;

        let mut hi: u16 = 0;
        ptr::copy_nonoverlapping((o as *const u8).add(6), &mut hi as *mut u16 as *mut u8, 2);
        let header: usize = ((hi as usize) << 48) | (next as usize);
        ptr::copy_nonoverlapping(&header as *const usize as *const u8, o as *mut u8, 8);
    }
    #[cfg(target_pointer_width = "32")]
    {
        *(o as *mut *mut LeanObject) = next;
    }
}

use crate::datatypes::LeanObject;

// appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/not_in_emit_rust.rs:19-29
#[inline(always)]
pub unsafe fn get_next(o: *mut LeanObject) -> *mut LeanObject {
    #[cfg(target_pointer_width = "64")]
    {
        use std::ptr;

        let mut header: usize = 0;
        ptr::copy_nonoverlapping(o as *const u8, &mut header as *mut usize as *mut u8, 8);
        header &= !(0xffff_usize << 48);
        header as *mut LeanObject
    }
    #[cfg(target_pointer_width = "32")]
    {
        *(o as *mut *mut LeanObject)
    }
}

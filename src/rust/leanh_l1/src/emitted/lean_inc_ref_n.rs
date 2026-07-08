use std::sync::atomic::{AtomicI32, Ordering};

use crate::{
    datatypes::LeanObject,
    r#priv::quar::{LEAN_UAF_POISON_RC, UAF_DETECT, quar_report_uaf},
};

#[inline]
pub unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    if UAF_DETECT && (*obj).rc == LEAN_UAF_POISON_RC {
        quar_report_uaf(obj, "inc");
    }
    if (*obj).rc > 0 {
        (*obj).rc += n as i32;
    } else if (*obj).rc != 0 {
        let rc = (&raw mut (*obj).rc).cast::<AtomicI32>();
        (*rc).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

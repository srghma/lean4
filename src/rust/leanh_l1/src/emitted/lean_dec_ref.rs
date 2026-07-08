use crate::{
    datatypes::LeanObject,
    lean_dec_ref_cold::lean_dec_ref_cold,
    r#priv::quar::{LEAN_UAF_POISON_RC, UAF_DETECT, quar_report_uaf},
};

#[inline]
pub unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    if UAF_DETECT && (*obj).rc == LEAN_UAF_POISON_RC {
        quar_report_uaf(obj, "dec");
    }
    if (*obj).rc > 1 {
        (*obj).rc -= 1;
    } else if (*obj).rc != 0 {
        lean_dec_ref_cold(obj);
    }
}

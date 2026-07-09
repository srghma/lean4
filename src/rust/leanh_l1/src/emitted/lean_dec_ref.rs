use crate::{
    datatypes::LeanObject,
    r#priv::lean_dec_ref_cold::lean_dec_ref_cold,
    r#priv::quar::{LEAN_UAF_POISON_RC, UAF_DETECT, quar_report_uaf},
};

#[inline]
pub unsafe fn lean_dec_ref(obj: *const LeanObject) {
    if UAF_DETECT && (*obj).rc == LEAN_UAF_POISON_RC {
        quar_report_uaf(obj as *mut LeanObject, "dec");
    }
    if (*obj).rc > 1 {
        (*(obj as *mut LeanObject)).rc -= 1;
    } else if (*obj).rc != 0 {
        lean_dec_ref_cold(obj as *mut LeanObject);
    }
}

use leanh_l1::datatypes::{LeanObject, LeanObjectTag};

// Set the header for a single-thread (rc = 1) task object.
#[inline(always)]
pub unsafe fn set_task_header_st(o: *mut LeanObject) {
    (*o).rc = 1;
    (*o).set_tag(LeanObjectTag::Task);
    (*o).other = 0;
    (*o).cs_size = 0;
}

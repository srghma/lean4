use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::lean_object_tag::lean_object_tag,
};

#[inline]
pub unsafe fn lean_is_task(obj: *const LeanObject) -> bool {
    matches!(lean_object_tag(obj), LeanObjectTag::Task)
}

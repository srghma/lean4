use leanh_l1::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_small_object_size(o: *const LeanObject) -> usize {
    // #[cfg(lean_small_allocator)]
    // {
    //     lean_small_mem_size(o) as usize
    // }

    // #[cfg(all(not(lean_small_allocator), lean_has_mimalloc))]
    // {
    (*o).cs_size as usize
    // }

    // #[cfg(all(not(lean_small_allocator), not(lean_has_mimalloc)))]
    // {
    //     *((o as *const usize).sub(1))
    // }
}

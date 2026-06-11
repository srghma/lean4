/*
 * module_shims.cpp
 *
 * Expose lean_compacted_region_save / lean_compacted_region_read to Rust via
 * C linkage by forwarding to the implementations in module.cpp.
 *
 * Place in: src/library/module_shims.cpp
 * Add to library CMakeLists target alongside module.cpp.
 * Remove lean_compacted_region_save / lean_compacted_region_read bodies from
 * module.cpp (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/module.h"
#include "runtime/compact.h"
#include "runtime/object.h"

/* Forward declarations of the implementations in module.cpp (renamed). */
extern "C" lean_object * lean_compacted_region_save_impl(
    lean_object * ofname, lean_object * module_name, lean_object * odata,
    lean_object * odep_regions, lean_object * oprev,
    uint8_t allow_closures, lean_object * w);

extern "C" lean_object * lean_compacted_region_read_impl(
    lean_object * ofname, lean_object * odep_regions, lean_object * w);

extern "C" {

lean_object * lean_cxx_compacted_region_save(
    lean_object * ofname, lean_object * module_name, lean_object * odata,
    lean_object * odep_regions, lean_object * oprev,
    uint8_t allow_closures, lean_object * w) {
    return lean_compacted_region_save_impl(ofname, module_name, odata,
                                           odep_regions, oprev, allow_closures, w);
}

lean_object * lean_cxx_compacted_region_read(
    lean_object * ofname, lean_object * odep_regions, lean_object * w) {
    return lean_compacted_region_read_impl(ofname, odep_regions, w);
}

} // extern "C"

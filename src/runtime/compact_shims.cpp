/*
 * compact_shims.cpp
 *
 * Thin C wrappers exposing object_compactor and compacted_region to Rust.
 * Place in src/runtime/ and add to RUNTIME_OBJS in CMakeLists.txt.
 * compact.cpp stays as-is; only the three extern "C" LEAN_EXPORT functions
 * at its bottom are now provided by runtime_compact.rs — remove them from
 * compact.cpp (or guard with #ifndef LEAN_RUST_COMPACT).
 */
#include <cstdlib>
#include <cstring>
#include <lean/lean.h>
#include "runtime/compact.h"

using namespace lean;

extern "C" {

/* ---- object_compactor ---- */

void * lean_compact_compactor_new(void * base_addr, uint8_t allow_closures) {
    return new object_compactor(base_addr, {}, allow_closures != 0);
}

void lean_compact_compactor_free(void * c) {
    delete static_cast<object_compactor *>(c);
}

void lean_compact_compactor_insert(void * c, lean_object * o) {
    (*static_cast<object_compactor *>(c))(o);
}

size_t lean_compact_compactor_size(void const * c) {
    return static_cast<object_compactor const *>(c)->size();
}

void const * lean_compact_compactor_data(void const * c) {
    return static_cast<object_compactor const *>(c)->data();
}

void const * lean_compact_compactor_base_addr(void const * c) {
    return static_cast<object_compactor const *>(c)->base_addr();
}

/* ---- compacted_region ---- */

void * lean_compact_region_new(size_t sz, void * data, void * base_addr, uint8_t is_mmap) {
    // Takes ownership of `data`; free_data lambda calls free()
    auto free_fn = [data]() { free(data); };
    return new compacted_region(sz, data, base_addr, is_mmap != 0, free_fn);
}

void lean_compact_region_free(void * r) {
    delete static_cast<compacted_region *>(r);
}

lean_object * lean_compact_region_read(void * r) {
    return static_cast<compacted_region *>(r)->read();
}

uint8_t lean_compact_region_is_mmap(void const * r) {
    return static_cast<compacted_region const *>(r)->is_memory_mapped() ? 1 : 0;
}

size_t lean_compact_region_size(void const * r) {
    return static_cast<compacted_region const *>(r)->size();
}

/* ---- helpers ---- */

size_t lean_compact_get_loaded_libs_count() {
    return get_loaded_libs().size();
}

void * lean_compact_malloc(size_t sz) { return malloc(sz); }
void   lean_compact_free(void * p)    { free(p); }
void   lean_compact_memcpy(void * dst, void const * src, size_t n) { memcpy(dst, src, n); }

} // extern "C"

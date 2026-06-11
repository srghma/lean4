/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Thin C++ shims called from runtime_alloc.rs.
Add to src/runtime/CMakeLists.txt RUNTIME_OBJS.
*/

#include <lean/lean.h>
#include "runtime/thread.h"   // register_thread_finalizer

extern "C" {

// ---------------------------------------------------------------------------
// System allocator wrappers
// The Rust alloc module calls these instead of lean.h inlines to avoid
// dependency on the C preprocessor / inline expansion at the Rust boundary.
// ---------------------------------------------------------------------------

void * lean_sys_alloc(size_t sz) {
#if defined(LEAN_MIMALLOC)
    return mi_malloc(sz);
#else
    return malloc(sz);
#endif
}

void lean_sys_free_sized(void * ptr, size_t sz) {
#if defined(LEAN_MIMALLOC)
    mi_free_size(ptr, sz);
#else
    (void)sz;
    free(ptr);
#endif
}

// ---------------------------------------------------------------------------
// register_thread_finalizer bridge
// The Rust small allocator needs to register finalize_heap as a thread
// finalizer.  The C++ function lives in the lean namespace so it has a
// mangled name; expose it as a plain C symbol for Rust.
// ---------------------------------------------------------------------------
void lean_register_thread_finalizer_c(void (*fn)(void *), void * data) {
    lean::register_thread_finalizer(fn, data);
}

} // extern "C"

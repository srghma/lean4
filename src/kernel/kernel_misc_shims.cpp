/*
C++ shims for kernel_local_ctx.rs, kernel_declaration.rs, kernel_environment.rs
*/
#include "kernel/local_ctx.h"
#include "kernel/declaration.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "runtime/interrupt.h"
#include <lean/lean.h>

using namespace lean;

extern "C" {

// ---------------------------------------------------------------------------
// local_ctx — init/finalize bodies live in local_ctx.cpp
// ---------------------------------------------------------------------------

void lean_cxx_initialize_local_ctx();
void lean_cxx_finalize_local_ctx();

// ---------------------------------------------------------------------------
// declaration — init/finalize bodies live in declaration.cpp
// ---------------------------------------------------------------------------

void lean_cxx_initialize_declaration();
void lean_cxx_finalize_declaration();

// ---------------------------------------------------------------------------
// environment — init/finalize are no-ops (environment.cpp bodies are empty)
// lean_cxx_add_decl / lean_cxx_add_decl_without_checking live in environment.cpp
// ---------------------------------------------------------------------------

void lean_cxx_initialize_environment() {
    /* empty — environment.cpp initialize_environment() is a no-op */
}

void lean_cxx_finalize_environment() {
    /* empty — environment.cpp finalize_environment() is a no-op */
}

} // extern "C"

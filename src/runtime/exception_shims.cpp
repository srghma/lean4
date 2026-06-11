/*
 * exception_shims.cpp
 *
 * Thin C wrappers so Rust can throw typed C++ exceptions without embedding
 * any C++ in the Rust crate.  Each function is [[noreturn]] because the
 * corresponding `throw` never returns.
 *
 * Place in: src/runtime/exception_shims.cpp
 * Add to RUNTIME_OBJS in src/runtime/CMakeLists.txt.
 * Remove the bodies of throw_get_stack_size_failed / throw_stack_space_exception /
 * throw_heartbeat_exception / throw_memory_exception / lean_throw_interrupted /
 * lean_uncaught_exceptions from src/runtime/exception.cpp (or delete that file).
 */
#include "runtime/exception.h"
#include "runtime/sstream.h"
#include <lean/version.h>
#include <exception>

extern "C" {

[[noreturn]] void lean_cxx_throw_get_stack_size_failed() {
    throw lean::exception("failed to retrieve thread stack size");
}

[[noreturn]] void lean_cxx_throw_stack_space_exception(char const * component_name) {
    throw lean::stack_space_exception(component_name);
}

[[noreturn]] void lean_cxx_throw_heartbeat_exception() {
    throw lean::heartbeat_exception();
}

[[noreturn]] void lean_cxx_throw_memory_exception(char const * component_name) {
    throw lean::memory_exception(component_name);
}

[[noreturn]] void lean_cxx_throw_interrupted() {
    throw lean::interrupted();
}

int lean_cxx_uncaught_exceptions() {
    return std::uncaught_exceptions() > 0 ? 1 : 0;
}

} // extern "C"

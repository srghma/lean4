/*
 * time_task_shims.cpp
 *
 * C shims exposing library/time_task C++ functionality to Rust.
 *
 * Place in: src/library/time_task_shims.cpp
 * Add to the library CMakeLists target alongside time_task.cpp.
 * Remove lean_display_cumulative_profiling_times / lean_profileit bodies
 * from time_task.cpp (or keep them — the Rust port delegates back here).
 */
#include "library/time_task.h"
#include "kernel/trace.h"
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include <iostream>
#include <string>

extern "C" {

bool lean_cxx_has_no_block_profiling_task() {
    return lean::has_no_block_profiling_task();
}

void lean_cxx_report_profiling_time(char const * category, double seconds) {
    lean::report_profiling_time(std::string(category),
        lean::second_duration(seconds));
}

void lean_cxx_exclude_profiling_time(double seconds) {
    lean::exclude_profiling_time_from_current_task(lean::second_duration(seconds));
}

void lean_cxx_display_cumulative_profiling_times() {
    lean::display_cumulative_profiling_times(std::cerr);
}

lean_object * lean_cxx_profileit(lean_object * category, lean_object * opts,
                                  lean_object * fn, lean_object * decl) {
    lean::time_task t(lean::string_to_std(category),
                      TO_REF(lean::options, opts),
                      lean::name(decl));
    return lean::apply_1(fn, lean::box(0));
}

} // extern "C"

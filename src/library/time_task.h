/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <chrono>
#include <functional>
#include <iomanip>
#include <iostream>
#include <string>
#include "library/profiling.h"

namespace lean {
struct display_profiling_time {
    second_duration m_time;
};

inline std::ostream & operator<<(std::ostream & out, display_profiling_time const & time) {
    out << std::setprecision(3);
    if (time.m_time < second_duration(1)) {
        out << std::chrono::duration<double, std::milli>(time.m_time).count() << "ms";
    } else {
        out << time.m_time.count() << "s";
    }
    return out;
}

/** \brief Low tech timer. */
class timeit {
    second_duration m_threshold;
    std::chrono::steady_clock::time_point m_start;
    std::ostream & m_out;
    std::string    m_msg;
public:
    timeit(std::ostream & out, char const * msg, second_duration threshold):
        m_threshold(threshold), m_out(out), m_msg(msg) {
        m_start = std::chrono::steady_clock::now();
    }
    timeit(std::ostream & out, char const * msg, double threshold):
        timeit(out, msg, second_duration(threshold)) {}
    timeit(std::ostream & out, char const * msg) : timeit(out, msg, second_duration(0)) {}
    ~timeit() {
        auto end = std::chrono::steady_clock::now();
        auto diff = second_duration(end - m_start);
        if (diff >= m_threshold) {
            m_out << m_msg << " " << display_profiling_time{diff} << "\n";
        }
    }
};

/** \brief Low tech timer. */
class xtimeit {
    second_duration m_threshold;
    second_duration m_excluded {0};
    std::chrono::steady_clock::time_point m_start;
    std::function<void(second_duration)> m_fn; // NOLINT
public:
    xtimeit(second_duration threshold, std::function<void(second_duration)> const & fn): // NOLINT
        m_threshold(threshold), m_fn(fn) {
        m_start = std::chrono::steady_clock::now();
    }
    xtimeit(std::function<void(second_duration)> const & fn) : xtimeit(second_duration(0), fn) {} // NOLINT
    xtimeit(xtimeit const &) = delete;
    xtimeit& operator=(xtimeit const &) = delete;
    xtimeit(xtimeit && other) noexcept
      : m_threshold(std::move(other.m_threshold)),
        m_excluded(std::move(other.m_excluded)),
        m_start(std::move(other.m_start)),
        m_fn(std::move(other.m_fn)) { // TODO: use `std::exchange(_, nullptr)` in C++14
        other.m_fn = nullptr;
    }
    xtimeit& operator=(xtimeit && other) noexcept {
        m_threshold = std::move(other.m_threshold);
        m_excluded  = std::move(other.m_excluded);
        m_start     = std::move(other.m_start);
        m_fn        = std::move(other.m_fn); // TODO: use `std::exchange(_, nullptr)` in C++14
        other.m_fn = nullptr;
        return *this;
    }
    ~xtimeit() {
        if (!m_fn) return;
        auto diff = get_elapsed();
        if (diff >= m_threshold) {
            m_fn(diff);
        }
    }

    second_duration get_elapsed_inclusive() const {
        auto end = std::chrono::steady_clock::now();
        return second_duration(end - m_start);
    }

    second_duration get_elapsed() const {
        return get_elapsed_inclusive() - m_excluded;
    }

    void exclude_duration(second_duration d) {
        m_excluded += d;
    }
};

LEAN_EXPORT bool has_no_block_profiling_task();
LEAN_EXPORT void report_profiling_time(std::string const & category, second_duration time);
LEAN_EXPORT void display_cumulative_profiling_times(std::ostream & out);
LEAN_EXPORT void exclude_profiling_time_from_current_task(second_duration time);

/** Measure time of some task and report it for the final cumulative profile. */
class LEAN_EXPORT time_task {
    std::string     m_category;
    optional<xtimeit> m_timeit;
    time_task *     m_parent_task;
public:
    time_task(std::string const & category, options const & opts, name decl = name());
    ~time_task();
    void exclude_duration(second_duration duration) { m_timeit->exclude_duration(duration); }
    std::string const & category() const { return m_category; }
};

void initialize_time_task();
void finalize_time_task();
}

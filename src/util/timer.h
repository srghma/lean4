/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "runtime/thread.h"
#include "runtime/optional.h"
#include <functional>

namespace lean {

#if defined(LEAN_MULTI_THREAD)
constexpr chrono::steady_clock::duration accuracy = chrono::milliseconds(10);

class single_timer {
public:
    using callback = std::function<void()>;

private:
    mutex m_mutex;
    condition_variable m_timer_changed;
    bool m_shutting_down;

    optional<chrono::steady_clock::time_point> m_time;
    callback m_cb;

    lthread m_thread;

    void worker() {
        unique_lock<mutex> lock(m_mutex);
        while (!m_shutting_down) {
            auto now = chrono::steady_clock::now();
            if (m_time && *m_time <= now + accuracy) {
                m_time = optional<chrono::steady_clock::time_point>();
                if (auto cb = std::move(m_cb)) {
                    lock.unlock();
                    cb();
                    lock.lock();
                }
            } else if (m_time) {
                m_timer_changed.wait_for(lock, *m_time - now);
            } else {
                m_timer_changed.wait(lock);
            }
        }
    }

public:
    single_timer() :
        m_shutting_down(false),
        m_thread(std::bind(&single_timer::worker, this)) {}
    ~single_timer() {
        {
            unique_lock<mutex> lock(m_mutex);
            m_shutting_down = true;
            m_timer_changed.notify_one();
        }
        m_thread.join();
    }

    void set(chrono::steady_clock::time_point const & time, callback const & cb, bool overwrite = true) {
        unique_lock<mutex> lock(m_mutex);
        if (overwrite || !m_time) {
            m_time = optional<chrono::steady_clock::time_point>(time);
            m_cb = cb;
            m_timer_changed.notify_one();
        }
    }
    void reset() {
        unique_lock<mutex> lock(m_mutex);
        m_time = optional<chrono::steady_clock::time_point>();
        m_cb = nullptr;
        m_timer_changed.notify_one();
    }
};
#else
class single_timer {};
#endif

}

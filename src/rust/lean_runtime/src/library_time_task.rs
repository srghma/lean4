use crate::*;

/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust port of src/library/time_task.cpp.

Exports:
  lean_display_cumulative_profiling_times() -> lean_object*  (BaseIO Unit)
  lean_profileit(category, opts, fn, decl) -> lean_object*
  lean_runtime_time_task_begin(category_cstr, opts, name) -> u8  (1 if enabled)
  lean_runtime_time_task_end(enabled: u8)
  _ZN4lean20initialize_time_taskEv  (no-op, state lives in Rust statics)
  _ZN4lean18finalize_time_taskEv    (clears cumulative times map)
*/

pub(crate) mod library_time_task_impl {
    use super::*;
    use std::collections::BTreeMap;
    use std::ffi::CStr;
    use std::io::Write;
    use std::sync::Mutex;
    use std::time::{Duration, Instant};

    struct TimeTaskEntry {
        category: String,
        name_str: Option<String>,
        start: Instant,
        threshold: Duration,
        excluded: Duration,
    }

    thread_local! {
        static TASK_STACK: std::cell::RefCell<Vec<TimeTaskEntry>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }

    static CUM_TIMES: Mutex<BTreeMap<String, Duration>> = Mutex::new(BTreeMap::new());

    // Format profiling duration matching C++ setprecision(3) style.
    fn format_profiling_time(d: Duration) -> String {
        let secs = d.as_secs_f64();
        if secs < 1.0 {
            let ms = secs * 1000.0;
            if ms < 10.0 {
                format!("{:.2}ms", ms)
            } else if ms < 100.0 {
                format!("{:.1}ms", ms)
            } else {
                format!("{:.0}ms", ms)
            }
        } else if secs < 10.0 {
            format!("{:.2}s", secs)
        } else if secs < 100.0 {
            format!("{:.1}s", secs)
        } else {
            format!("{:.0}s", secs)
        }
    }

    // Build a dot-separated display string from a Lean Name (anonymous → None).
    // Name tag 1 = str component (field 1 = lean string), tag 2 = num component (field 1 = lean nat).
    unsafe fn lean_name_to_display_string(n: *mut LeanObject) -> Option<String> {
        if lean_is_scalar(n) {
            return None;
        }
        let mut parts: Vec<String> = Vec::new();
        let mut cur = n;
        while !lean_is_scalar(cur) {
            let tag = lean_ptr_tag(cur);
            parts.push(if tag == 1 {
                let str_obj = lean_ctor_get(cur, 1);
                CStr::from_ptr(lean_string_cstr(str_obj))
                    .to_string_lossy()
                    .into_owned()
            } else {
                let nat = lean_ctor_get(cur, 1);
                if lean_is_scalar(nat) {
                    lean_unbox(nat).to_string()
                } else {
                    "?".to_string()
                }
            });
            cur = lean_ctor_get(cur, 0);
        }
        parts.reverse();
        Some(parts.join("."))
    }

    fn begin_impl(category: String, name_str: Option<String>, threshold: Duration) {
        TASK_STACK.with(|stack| {
            stack.borrow_mut().push(TimeTaskEntry {
                category,
                name_str,
                start: Instant::now(),
                threshold,
                excluded: Duration::ZERO,
            });
        });
    }

    fn end_impl() {
        TASK_STACK.with(|stack| {
            let mut s = stack.borrow_mut();
            if let Some(entry) = s.pop() {
                let elapsed_inclusive = entry.start.elapsed();
                let elapsed = elapsed_inclusive.saturating_sub(entry.excluded);
                if elapsed >= entry.threshold {
                    let name_part = match &entry.name_str {
                        Some(n) => format!(" of {}", n),
                        None => String::new(),
                    };
                    let msg = format!(
                        "{}{} took {}\n",
                        entry.category,
                        name_part,
                        format_profiling_time(elapsed)
                    );
                    let _ = std::io::stderr().write_all(msg.as_bytes());
                }
                if let Ok(mut cum) = CUM_TIMES.lock() {
                    *cum.entry(entry.category).or_insert(Duration::ZERO) += elapsed;
                }
                // Exclude this task's inclusive time from the parent task.
                if let Some(parent) = s.last_mut() {
                    parent.excluded += elapsed_inclusive;
                }
            }
        });
    }

    /// C-callable API for runtime/interpreter callers.
    /// opts and name are borrowed (b_obj_arg). Returns 1 if profiling enabled.
    #[inline]
    pub(crate) unsafe fn lean_runtime_time_task_begin(
        category_cstr: *const core::ffi::c_char,
        opts: *mut LeanObject,
        name: *mut LeanObject,
    ) -> u8 {
        let lean_opts = LeanOptions { obj: opts };
        let enabled = get_profiler(&lean_opts);
        if enabled {
            let threshold = Duration::from_secs_f64(get_profiling_threshold(&lean_opts));
            let category = CStr::from_ptr(category_cstr).to_string_lossy().into_owned();
            let name_str = lean_name_to_display_string(name);
            begin_impl(category, name_str, threshold);
        }
        enabled as u8
    }

    #[inline]
    pub(crate) unsafe fn lean_runtime_time_task_end(enabled: u8) {
        if enabled != 0 {
            end_impl();
        }
    }

    /// displayCumulativeProfilingTimes : BaseIO Unit
    #[inline]
    pub(crate) unsafe fn lean_display_cumulative_profiling_times() -> *mut LeanObject {
        if let Ok(cum) = CUM_TIMES.lock() {
            if !cum.is_empty() {
                let mut s = String::from("cumulative profiling times:\n");
                for (k, v) in cum.iter() {
                    s.push_str(&format!("\t{} {}\n", k, format_profiling_time(*v)));
                }
                let _ = std::io::stderr().write_all(s.as_bytes());
            }
        }
        lean_box(0)
    }

    /// profileit {α} (category : @& String) (opts : @& Options) (fn : Unit → α) (decl : Name) : α
    /// category and opts are b_obj_arg (borrowed); func and decl are obj_arg (owned).
    #[inline]
    pub(crate) unsafe fn lean_profileit(
        category: *mut LeanObject,
        opts: *mut LeanObject,
        func: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        let lean_opts = LeanOptions { obj: opts };
        let enabled = get_profiler(&lean_opts);
        if enabled {
            let threshold = Duration::from_secs_f64(get_profiling_threshold(&lean_opts));
            let category_str = CStr::from_ptr(lean_string_cstr(category))
                .to_string_lossy()
                .into_owned();
            let name_str = lean_name_to_display_string(decl);
            lean_dec(decl);
            begin_impl(category_str, name_str, threshold);
            let result = lean_apply_1(func, lean_box(0));
            end_impl();
            result
        } else {
            lean_dec(decl);
            lean_apply_1(func, lean_box(0))
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean20initialize_time_taskEv")]
    pub extern "C" fn initialize_time_task() {}

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean18finalize_time_taskEv")]
    pub extern "C" fn finalize_time_task() {
        if let Ok(mut cum) = CUM_TIMES.lock() {
            cum.clear();
        }
    }
}

// Port of src/library/time_task.cpp to Rust.
//
// The C++ `time_task` RAII class relies on C++ destructors and captures
// lambdas — we forward the exported `extern "C"` functions to thin C++ shims
// (time_task_shims.cpp) for the parts that need C++ class semantics.
// The pure-data functions (cumulative time map, display) are ported directly.

mod runtime_time_task_impl {
    use super::*;
    use core::ffi::{c_char, c_void};
    use std::collections::BTreeMap;
    use std::io::Write;
    use std::sync::Mutex;

    // ── Global cumulative-times map ──────────────────────────────────────────

    static G_CUM_TIMES: Mutex<Option<BTreeMap<String, f64>>> = Mutex::new(None);

    pub fn ensure_init() {
        let mut g = G_CUM_TIMES.lock().unwrap();
        if g.is_none() {
            *g = Some(BTreeMap::new());
        }
    }

    /// Called from `lean_initialize_time_task` (below).
    pub fn initialize() {
        ensure_init();
    }

    /// Called from `lean_finalize_time_task` (below).
    pub fn finalize() {
        let mut g = G_CUM_TIMES.lock().unwrap();
        *g = None;
    }

    pub fn report_time(category: &str, seconds: f64) {
        let mut g = G_CUM_TIMES.lock().unwrap();
        if let Some(ref mut map) = *g {
            *map.entry(category.to_string()).or_insert(0.0) += seconds;
        }
    }

    pub fn display_cumulative(out: &mut dyn Write) {
        let g = G_CUM_TIMES.lock().unwrap();
        if let Some(ref map) = *g {
            if map.is_empty() {
                return;
            }
            let mut s = String::from("cumulative profiling times:\n");
            for (k, v) in map.iter() {
                s.push_str(&format!("\t{} {:.6}s\n", k, v));
            }
            let _ = out.write_all(s.as_bytes());
        }
    }

    // ── C++ shims for time_task RAII ─────────────────────────────────────────

    extern "C" {
        /// Creates a `time_task` on the C++ heap and returns an opaque pointer.
        /// Signature: (category: *const c_char, opts: *mut LeanObject, decl: *mut LeanObject) -> *mut c_void
        fn lean_cxx_time_task_create(
            category: *const c_char,
            opts: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut c_void;

        /// Destroys a `time_task` (runs the destructor, reports time).
        fn lean_cxx_time_task_destroy(task: *mut c_void);

        /// `report_profiling_time` C++ implementation.
        fn lean_cxx_report_profiling_time(category: *const c_char, seconds: f64);

        /// `exclude_profiling_time_from_current_task` C++ implementation.
        fn lean_cxx_exclude_profiling_time(seconds: f64);

        /// `has_no_block_profiling_task` C++ implementation.
        fn lean_cxx_has_no_block_profiling_task() -> bool;

        /// `display_cumulative_profiling_times` to stderr C++ implementation.
        fn lean_cxx_display_cumulative_profiling_times();

        /// `lean_profileit` full C++ implementation (category, opts, fn, decl).
        fn lean_cxx_profileit(
            category: *mut LeanObject,
            opts: *mut LeanObject,
            func: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    // ── Exported functions ───────────────────────────────────────────────────

    #[no_mangle]
    pub extern "C" fn lean_has_no_block_profiling_task() -> bool {
        unsafe { lean_cxx_has_no_block_profiling_task() }
    }

    #[no_mangle]
    pub extern "C" fn lean_report_profiling_time(category: *const c_char, seconds: f64) {
        unsafe { lean_cxx_report_profiling_time(category, seconds) }
    }

    #[no_mangle]
    pub extern "C" fn lean_exclude_profiling_time_from_current_task(seconds: f64) {
        unsafe { lean_cxx_exclude_profiling_time(seconds) }
    }

    #[no_mangle]
    pub extern "C" fn lean_display_cumulative_profiling_times() {
        unsafe { lean_cxx_display_cumulative_profiling_times() }
    }

    /// `displayCumulativeProfilingTimes : BaseIO Unit`
    #[no_mangle]
    pub unsafe extern "C" fn lean_display_cumulative_profiling_times_io() -> *mut LeanObject {
        lean_cxx_display_cumulative_profiling_times();
        lean_box(0)
    }

    /// `profileit {α} (category opts fn decl) : α`
    #[no_mangle]
    pub unsafe extern "C" fn lean_profileit(
        category: *mut LeanObject,
        opts: *mut LeanObject,
        func: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_profileit(category, opts, func, decl)
    }

    #[export_name = "_ZN4lean20initialize_time_taskEv"]
    pub extern "C" fn initialize_time_task() {
        initialize();
    }

    #[export_name = "_ZN4lean18finalize_time_taskEv"]
    pub extern "C" fn finalize_time_task() {
        finalize();
    }
}

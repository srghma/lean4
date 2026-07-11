use std::sync::OnceLock;

/// Returns the number of threads to be used by the Lean runtime.
/// Memoized: The environment variable and CPU count are only checked once.
pub fn lean_get_lean_num_threads() -> usize {
    // OnceLock ensures thread-safe, one-time initialization
    static NUM_THREADS: OnceLock<usize> = OnceLock::new();

    *NUM_THREADS.get_or_init(|| {
        std::env::var("LEAN_NUM_THREADS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok()) // Parse env var to usize
            .unwrap_or_else(|| {
                // Fallback: Get hardware concurrency (returns NonZeroUsize)
                std::thread::available_parallelism()
                    .map(|count| count.get())
                    .unwrap_or(1) // Final fallback if hardware check fails
            })
    })
}

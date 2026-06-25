# runtime_exception.rs audit

Original C++:
- `origin-master-src/runtime/exception.cpp`
- `origin-master-src/runtime/exception.h`

Rust:
- `src/rust/lean_runtime/src/runtime_exception.rs`

## 2026-06-25 status

- `src/runtime/exception.cpp` is removed from the build and deleted.
- The exported no-return resource hooks are now in Rust:
  - `throw_get_stack_size_failed`
  - `throw_stack_space_exception`
  - `throw_heartbeat_exception`
  - `throw_memory_exception`
  - `lean_throw_interrupted`
  - `lean_uncaught_exceptions`
- These hooks preserve the C++ `what()` message text where practical and abort instead of throwing C++ exceptions. Kernel-facing resource checks already use Rust `Result<KernelError>` paths.
- The C ABI exports are gated with `cfg_attr(feature = "export-runtime-ffi", no_mangle)` so the embedded `lean_runtime` copy inside `lean_shell` does not export duplicate symbols.
- `src/runtime/exception.h` remains temporarily for C++ facade headers. Header collapse is deferred to the generated `lean.h` milestone.

## Focused tests

Passed after deleting `exception.cpp`:

```bash
CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test -j$(nproc) \
  ARGS='-R "kernel_maxheartbeats|kernelInterrupt|inductive1|inductive_mutual|nested_inductive|quotInd" --timeout 240 --output-on-failure'
```

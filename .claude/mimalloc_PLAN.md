› we, we made mimalloc a defualt, but rust has own allocator, what would take to remove use rust allocator instead mimalloc too


• To make Lean use mimalloc instead of Rust’s default allocator, you need to do two separate things:

  1. Install mimalloc as the global allocator.
  2. Remove the raw allocator calls that bypass Rust’s allocator.

  Right now, you have not done step 1, so Rust still uses the default global allocator.

  What it would take:

  - Add back:

    #[global_allocator]
    static GLOBAL_ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;
    in src/rust/lean_runtime/src/lib.rs, behind #[cfg(feature = "std")] or equivalent.
    in src/rust/lean_runtime/src/lib.rs, behind #[cfg(feature = "std")] or equivalent.

  - Keep the mimalloc crate dependency enabled in Cargo.toml.
  - Make sure Rust allocation sites use Rust allocation APIs:
      - std::alloc::{alloc, dealloc}
      - Box, Vec, String
      - not libc::malloc, libc::free, free_sized

  - Audit all places that manually allocate/free memory:
      - runtime_object_rc.rs
      - runtime_alloc.rs if any old paths remain
      - runtime_object_task.rs
      - runtime_object_nat_int.rs
      - any libc::malloc/free in the runtime

  Why this matters:

  - #[global_allocator] only affects Rust allocations.
  - Any explicit libc::malloc/free still bypasses mimalloc.
  - If you want mimalloc to be the real allocator for Lean runtime objects, you need the code to allocate through Rust’s allocator layer, not libc.

  Important compatibility point:

  - If some objects are created in Rust and freed in C/C++, or vice versa, both sides must agree on the allocator.
  - In your current direction, the clean model is:
      - Rust owns allocation
      - C/C++ only consumes the ABI
      - deallocation of Rust-owned objects goes through Rust paths

  So the practical plan is:

  1. re-enable #[global_allocator] with mimalloc
  2. remove all libc::malloc/free paths from Rust runtime objects
  3. keep only Rust allocator calls for Rust-owned memory
  4. leave FFI objects alone only if they are still allocated/freed by foreign code

  If you want, I can do the next pass and list every remaining libc::malloc/free site in src/rust/lean_runtime/src that still needs conversion.

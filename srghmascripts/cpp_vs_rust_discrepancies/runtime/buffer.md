# `runtime/buffer` (`runtime/buffer.h`)

## Location of corresponding Rust implementation
No corresponding custom buffer implementation exists in the Rust port. 

## Discrepancies and issues
The C++ `lean::buffer<T, INITIAL_SIZE>` was an optimization to allocate elements on the stack when the size of the array is known to be small, to avoid heap allocation overheads.
In the Rust codebase, standard arrays or `std::vec::Vec<T>` are typically used instead. If stack allocation optimizations are strictly required in the future, standard Rust crates like `smallvec` or `tinyvec` can be dropped in. Currently, Rust relies on its own memory allocator (and sometimes custom array types managed by the Lean garbage collector) which are performant enough.

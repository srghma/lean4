# Dynamic plugins are not part of the Rust/Cargo backend; verify the module still emits an rlib.
lean --rust=SnakeLinter.rs -Dcompiler.postponeCompile=false SnakeLinter.lean
leanc ${LEANC_OPTS-} -O3 -DNDEBUG -c -o SnakeLinter.rlib SnakeLinter.rs

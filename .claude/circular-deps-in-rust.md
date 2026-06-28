```sh
✘  ~/projects/lean4/src/rust  ⇅ rust-rewrite ±✚  cargo machete
Analyzing dependencies of crates in this directory...
cargo-machete found the following unused dependencies in this directory:
lean_runtime -- ./lean_runtime/Cargo.toml:
       libloading

If you believe cargo-machete has detected an unused dependency incorrectly,
you can add the dependency to the list of dependencies to ignore in the
`[package.metadata.cargo-machete]` section of the appropriate Cargo.toml.
For example:

[package.metadata.cargo-machete]
ignored = ["prost"]

You can also try running it with the `--with-metadata` flag for better accuracy,
though this may modify your Cargo.lock files.

Done!
```

cargo install cargo-modules
cargo modules generate graph | dot -Tpng > graph.png

cargo-ferris-wheel

cargo install cargo-cycles && cargo cycles

cargo install cargo-coupling

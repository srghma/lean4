/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

fn main() {
    println!("cargo:rustc-check-cfg=cfg(lean_lazy_rc)");
    if std::env::var("LEAN_RUST_LAZY_RC").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_lazy_rc");
    }
}

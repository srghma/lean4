/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

fn main() {
    for key in [
        "LEAN_RUST_GITHASH",
        "LEAN_RUST_BUILD_TYPE",
        "LEAN_RUST_HAS_LLVM",
        "LEAN_RUST_HAS_ADDRESS_SANITIZER",
        "LEAN_RUST_HAS_MIMALLOC",
        "LEAN_RUST_SMALL_ALLOCATOR",
        "LEAN_RUST_MULTI_THREAD",
        "LEAN_RUST_DEBUG",
        "LEAN_RUST_LEANC_EXTRA_CC_FLAGS",
        "LEAN_RUST_LEANC_INTERNAL_FLAGS",
        "LEAN_RUST_LEANC_STATIC_LINKER_FLAGS",
        "LEAN_RUST_LEANC_SHARED_LINKER_FLAGS",
        "LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS",
        "LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS",
        "LEAN_RUST_LEANRT_INITIAL_EXEC_ARCHIVE",
        "LEAN_RUST_IS_STAGE0",
    ] {
        println!("cargo:rerun-if-env-changed={key}");
        println!(
            "cargo:rustc-env={key}={}",
            std::env::var(key).unwrap_or_default()
        );
    }
    if let Ok(archive) = std::env::var("LEAN_RUST_LEANRT_INITIAL_EXEC_ARCHIVE") {
        if !archive.is_empty() {
            println!("cargo:rustc-link-arg={archive}");
        }
    }
    println!("cargo:rustc-check-cfg=cfg(lean_small_allocator)");
    if std::env::var("LEAN_RUST_SMALL_ALLOCATOR").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_small_allocator");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_has_mimalloc)");
    if std::env::var("LEAN_RUST_HAS_MIMALLOC").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_has_mimalloc");
    }
    println!("cargo:rerun-if-env-changed=LEAN_RUST_USE_GMP");
    println!("cargo:rustc-check-cfg=cfg(lean_use_gmp)");
    if std::env::var("LEAN_RUST_USE_GMP").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_use_gmp");
    }
}

/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

fn main() {
    println!("cargo:rerun-if-changed=../../CMakeLists.txt");
    for key in [
        // "LEAN_RUST_GITHASH",
        // "LEAN_RUST_BUILD_TYPE",
        "LEAN_RUST_MANUAL_ROOT",
        // "LEAN_RUST_HAS_LLVM",
        // "LEAN_RUST_HAS_ADDRESS_SANITIZER",
        "LEAN_RUST_MULTI_THREAD",
        // "LEAN_RUST_DEBUG",
        // "LEAN_RUST_LEANC_EXTRA_CC_FLAGS",
        // "LEAN_RUST_LEANC_INTERNAL_FLAGS",
        // "LEAN_RUST_LEANC_STATIC_LINKER_FLAGS",
        // "LEAN_RUST_LEANC_SHARED_LINKER_FLAGS",
        // "LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS",
        // "LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE",
        // "LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS",
        // "LEAN_RUST_IS_STAGE0",
    ] {
        println!("cargo:rerun-if-env-changed={key}");
        println!(
            "cargo:rustc-env={key}={}",
            std::env::var(key).unwrap_or_default()
        );
    }
    println!("cargo:rustc-check-cfg=cfg(lean_multi_thread)");
    if true {
        // std::env::var("LEAN_RUST_MULTI_THREAD").as_deref() == Ok("1") {
        // by default ON
        println!("cargo:rustc-cfg=lean_multi_thread");
    }

    println!("cargo:rustc-check-cfg=cfg(lean_has_address_sanitizer)");
    if true {
        // std::env::var("LEAN_RUST_HAS_ADDRESS_SANITIZER").as_deref() == Ok("1") {
        // by default OFF
        println!("cargo:rustc-cfg=lean_has_address_sanitizer");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_has_llvm)");
    if true {
        // std::env::var("LEAN_RUST_HAS_LLVM").as_deref() == Ok("1") {
        // by default OFF
        println!("cargo:rustc-cfg=lean_has_llvm");
    }
}

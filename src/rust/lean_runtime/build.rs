/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

fn main() {
    println!("cargo:rerun-if-changed=../../CMakeLists.txt");
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
        "LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE",
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
    println!("cargo:rerun-if-env-changed=LEAN_RUST_VERSION_STRING");
    if let Ok(version_string) = std::env::var("LEAN_RUST_VERSION_STRING") {
        println!("cargo:rustc-env=LEAN_RUST_VERSION_STRING={version_string}");
    } else {
        let version_string = derive_version_string_from_cmake();
        println!("cargo:rustc-env=LEAN_RUST_VERSION_STRING={version_string}");
    }
    if let Ok(archive) = std::env::var("LEAN_RUST_LEANRT_INITIAL_EXEC_ARCHIVE") {
        if !archive.is_empty() {
            println!("cargo:rustc-link-arg={archive}");
        }
    }
    let version_string = std::env::var("LEAN_RUST_VERSION_STRING")
        .unwrap_or_else(|_| derive_version_string_from_cmake());
    let out_dir = std::env::var("OUT_DIR").expect("OUT_DIR must be set by cargo");
    let version_rs = std::path::Path::new(&out_dir).join("lean_version.rs");
    std::fs::write(
        &version_rs,
        format!(
            "pub(crate) const LEAN_VERSION_STRING: &str = {:?};\npub(crate) const LEAN_VERSION_STRING_CSTR: &[u8] = b\"{}\\0\";\n",
            version_string,
            version_string
        ),
    )
    .unwrap_or_else(|_| panic!("unable to write {}", version_rs.display()));
    println!("cargo:rustc-check-cfg=cfg(lean_small_allocator)");
    if std::env::var("LEAN_RUST_SMALL_ALLOCATOR").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_small_allocator");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_multi_thread)");
    if std::env::var("LEAN_RUST_MULTI_THREAD").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_multi_thread");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_has_mimalloc)");
    if std::env::var("LEAN_RUST_HAS_MIMALLOC").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_has_mimalloc");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_has_address_sanitizer)");
    if std::env::var("LEAN_RUST_HAS_ADDRESS_SANITIZER").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_has_address_sanitizer");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_has_llvm)");
    if std::env::var("LEAN_RUST_HAS_LLVM").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_has_llvm");
    }
    println!("cargo:rustc-check-cfg=cfg(lean_lazy_rc)");
    if std::env::var("LEAN_RUST_LAZY_RC").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_lazy_rc");
    }
    println!("cargo:rerun-if-env-changed=LEAN_RUST_USE_GMP");
    println!("cargo:rustc-check-cfg=cfg(lean_use_gmp)");
    if std::env::var("LEAN_RUST_USE_GMP").as_deref() == Ok("1") {
        println!("cargo:rustc-cfg=lean_use_gmp");
    }
}

fn derive_version_string_from_cmake() -> String {
    let manifest_dir =
        std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR must be set by cargo");
    let cmake_path = std::path::Path::new(&manifest_dir).join("../../CMakeLists.txt");
    let cmake = std::fs::read_to_string(&cmake_path)
        .unwrap_or_else(|_| panic!("unable to read {} for Lean version", cmake_path.display()));

    let major = parse_cmake_integer(&cmake, "LEAN_VERSION_MAJOR");
    let minor = parse_cmake_integer(&cmake, "LEAN_VERSION_MINOR");
    let patch = parse_cmake_integer(&cmake, "LEAN_VERSION_PATCH");
    let is_release = parse_cmake_integer(&cmake, "LEAN_VERSION_IS_RELEASE");
    let special_desc = parse_cmake_string(&cmake, "LEAN_SPECIAL_VERSION_DESC");

    let mut version = format!("{major}.{minor}.{patch}");
    if !special_desc.is_empty() {
        version.push('-');
        version.push_str(&special_desc);
    } else if is_release == 0 {
        version.push_str("-pre");
    }
    version
}

fn parse_cmake_integer(text: &str, name: &str) -> u32 {
    let prefix = format!("set({name} ");
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with(&prefix))
        .unwrap_or_else(|| panic!("missing {name} in CMakeLists.txt"));
    let value = line
        .trim_start()
        .strip_prefix(&prefix)
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_else(|| panic!("unable to parse {name}"));
    value
        .parse()
        .unwrap_or_else(|_| panic!("unable to parse integer {name}"))
}

fn parse_cmake_string(text: &str, name: &str) -> String {
    let prefix = format!("set({name} \"");
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with(&prefix))
        .unwrap_or_else(|| panic!("missing {name} in CMakeLists.txt"));
    let rest = line
        .trim_start()
        .strip_prefix(&prefix)
        .unwrap_or_else(|| panic!("unable to parse {name}"));
    let value = rest
        .split_once('"')
        .unwrap_or_else(|| panic!("unable to parse {name}"))
        .0;
    value.to_owned()
}

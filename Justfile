set shell := ["bash", "-euo", "pipefail", "-c"]

nproc := `nproc`
test_log_dir := "/tmp"

# Rebuild stage0 with the current sources.
update-stage0:
    make -C build/release/stage0 lean -j{{ nproc }}

# Rebuild stage1 with the current sources.
update-stage1:
    cmake -S . -B build/release
    make -C build/release/stage1 lean -j{{ nproc }}

# Rebuild stage2 with the current sources.
update-stage2:
    make -C build/release/stage2 lean -j{{ nproc }}

regenerate-gen:
    bun srghmascripts/regenerate_gen.ts
    bun srghmascripts/split_gen_lean_ffi.ts
    bun srghmascripts/audit_gen_lean_split_cycles.ts

regenerate-gen-rs-do name="" depends_on="":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "src/rust"

    if [ -z "{{ name }}" ]; then
        echo "Error: 'name' is required." >&2
        exit 1
    fi

    extra_args=()
    if [ -n "{{ depends_on }}" ]; then
        extra_args=(--depends-on="{{ depends_on }}")
    fi

    bun ../../srghmascripts/regenerate_module_tree.ts "{{ name }}" "${extra_args[@]}"
    rustfmt --edition 2024 "{{ name }}/src/gen.rs"

# Shorthand dependency recipes
regenerate-gen-rs--gen_init:
    just regenerate-gen-rs-do "gen_init"

regenerate-gen-rs--gen_std:
    just regenerate-gen-rs-do "gen_std" "gen_init::r#gen::Init"

regenerate-gen-rs--gen_lean:
    just regenerate-gen-rs "gen_lean" "gen_init::r#gen::Init,gen_std::r#gen::Std"

regenerate-gen-rs--lake:
    just regenerate-gen-rs "lake" "gen_init::r#gen::Init,gen_std::r#gen::Std,gen_lean::r#gen::Lean"

regenerate-gen-rs--lean_checker:
    just regenerate-gen-rs "lean_checker" "gen_init::r#gen::Init,gen_std::r#gen::Std,gen_lean::r#gen::Lean,lake::r#gen::Lake"

regenerate-gen-rs:
    just regenerate-gen-rs--gen_init
    just regenerate-gen-rs--gen_std
    just regenerate-gen-rs--gen_lean
    just regenerate-gen-rs--lake
    just regenerate-gen-rs--lean_checker

rustfmt-all:
    #!/usr/bin/env bash
    set -euo pipefail
    cd src/rust
    rustfmt --edition 2024 **/*.rs

cargo-do crate="" build_or_check="build" normal_or_for_ai_or_short_errors="normal":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "src/rust"
    crate_args=()
    if [ -n "{{ crate }}" ]; then
        crate_args=(-p "{{ crate }}")
    fi
    case "{{ normal_or_for_ai_or_short_errors }}" in
        normal)
            CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo {{ build_or_check }} "${crate_args[@]}"
            ;;
        short_errors)
            CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo {{ build_or_check }} "${crate_args[@]}" --message-format=short 2>&1 | grep 'error\[' | sed -E 's/^[^:]+:[0-9]+:[0-9]+: //' | sort -u
            ;;
        for_ai)
            CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo {{ build_or_check }} "${crate_args[@]}" --message-format=json | python3 ../../srghmascripts/collect-cargo-build-json-errors-and-warnings-for-ai.py 2>&1 | copyq add -
            ;;
        *)
            echo "unknown mode: {{ normal_or_for_ai_or_short_errors }}" >&2
            exit 2
            ;;
    esac

cargo-do-all build_or_check="build" normal_or_for_ai_or_short_errors="normal":
    #!/usr/bin/env bash
    set -euo pipefail
    just cargo-do leanh {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_init_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_init {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_std_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_std {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_base_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_meta_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_meta_tactic_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_meta_grind_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_compiler_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean_elab_tactic_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do gen_lean {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do runtime {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do lake_ffi {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do lake {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do lean_checker {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do lean_ir {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do lean_shell {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}
    just cargo-do leanc {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }}

# Type-check only the generated Rust tree, without compiling lean_runtime/src/lib.rs.
# The default checks a small generated file first; use check-gen-roots/check-gen-full for heavier checks.
# check-gen:
#     bun srghmascripts/check_gen.ts --files=Init/Prelude.rs
# Type-check selected generated roots. Example: just check-gen-roots LeanChecker
# check-gen-roots roots:
#     bun srghmascripts/check_gen.ts --roots={{ roots }}
#
# # Type-check the whole generated tree. This is memory-heavy.
# check-gen-full:
#     bun srghmascripts/check_gen.ts --full

# Run all tests, tee full output to a log file, and print only failures to stdout.
test-all:
    name=all
    log="{{ test_log_dir }}/lean4-test-output-${name}-$(date +%Y%m%d-%H%M%S).log"
    /usr/bin/time -p bash -lc 'set -o pipefail; CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test -j"$(nproc)" ARGS='\''-E bench/mvcgen/sym --timeout 240 --output-on-failure'\''' 2>&1 | tee "$log" | grep -A5 -B20 -Ei 'fail(ed|ure)?|failure' || true
    s=${PIPESTATUS[0]}
    echo "log: $log"
    exit $s

# Run only elab tests, tee full output to a log file, and print only failures to stdout.
test-elab:
    name=elab
    log="{{ test_log_dir }}/lean4-test-output-${name}-$(date +%Y%m%d-%H%M%S).log"
    /usr/bin/time -p bash -lc 'set -o pipefail; CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test -j"$(nproc)" ARGS='\''-E bench/mvcgen/sym --timeout 240 --output-on-failure -R "elab"'\''' 2>&1 | tee "$log" | grep -A5 -B20 -Ei 'fail(ed|ure)?|failure' || true
    s=${PIPESTATUS[0]}
    echo "log: $log"
    exit $s

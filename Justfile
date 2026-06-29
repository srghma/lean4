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

regenerate-gen-rs--gen_init:
    #!/usr/bin/env bash
    set -euo pipefail
    cd src/rust
    bun ../../srghmascripts/regenerate_module_tree.ts gen_init
    rustfmt --edition 2024 gen_init/src/gen.rs

regenerate-gen-rs--gen_std:
    #!/usr/bin/env bash
    set -euo pipefail
    cd src/rust
    bun ../../srghmascripts/regenerate_module_tree.ts gen_std --depends-on=gen_init
    rustfmt --edition 2024 gen_std/src/gen.rs

regenerate-gen-rs--gen_lean:
    #!/usr/bin/env bash
    set -euo pipefail
    cd src/rust
    bun ../../srghmascripts/regenerate_module_tree.ts gen_lean --depends-on="gen_init,gen_std"
    rustfmt --edition 2024 gen_lean/src/gen.rs

regenerate-gen-rs--lake:
    #!/usr/bin/env bash
    set -euo pipefail
    cd src/rust
    bun ../../srghmascripts/regenerate_module_tree.ts lake --depends-on="gen_init,gen_std,gen_lean"
    rustfmt --edition 2024 lake/src/gen.rs

regenerate-gen-rs:
    #!/usr/bin/env bash
    set -euo pipefail
    just regenerate-gen-rs--gen_init
    just regenerate-gen-rs--gen_std
    just regenerate-gen-rs--gen_lean
    just regenerate-gen-rs--lake

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
            CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo {{ build_or_check }} "${crate_args[@]}" --message-format=json | python3 collect-cargo-build-json-errors-and-warnings-for-ai.py | copyq add -
            ;;
        *)
            echo "unknown mode: {{ normal_or_for_ai_or_short_errors }}" >&2
            exit 2
            ;;
    esac

cargo-do-all build_or_check="build" normal_or_for_ai_or_short_errors="normal":
    #!/usr/bin/env bash
    set -euo pipefail
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} leanh
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} gen_init
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} gen_std
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} gen_lean
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} runtime
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} lake
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} lean_checker
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} lean_ir
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} lean_shell
    just cargo-do {{ build_or_check }} {{ normal_or_for_ai_or_short_errors }} leanc

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

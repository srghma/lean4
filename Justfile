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

# Regenerate src/rust/lean_runtime/src/gen from the current stage1 compiler.
regenerate-gen:
    bun srghmascripts/regenerate_gen.ts

# Regenerate src/rust/lean_runtime/src/gen.rs from the files under src/rust/lean_runtime/src/gen.
regenerate-gen-tree:
    bun srghmascripts/regenerate_module_tree.ts gen

# Regenerate src/rust/lean_runtime/src/lean_imports_rs.rs from the files under src/rust/lean_runtime/src/lean_imports_rs.
regenerate-lean-imports-rs-tree:
    # e.g. bun srghmascripts/regenerate_module_tree.ts lean_imports_rs --roots="Init,Lean" will generete 2 trees
    bun srghmascripts/regenerate_module_tree.ts lean_imports_rs

cargo-build:
    #!/usr/bin/env bash
    set -euo pipefail
    cd /home/srghma/projects/lean4/src/rust/lean_runtime
    CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo build

# Build and print only unique error signatures
cargo-build-errors-short:
    #!/usr/bin/env bash
    set -euo pipefail
    cd /home/srghma/projects/lean4/src/rust/lean_runtime
    CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo build --message-format=short 2>&1 | grep 'error\[' | sed -E 's/^[^:]+:[0-9]+:[0-9]+: //' | sort -u

cargo-build-ai:
    #!/usr/bin/env bash
    set -euo pipefail
    cd /home/srghma/projects/lean4/src/rust/lean_runtime
    CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo build --message-format=json | python3 -c '
    import sys, json
    from collections import defaultdict

    messages = defaultdict(list)

    for line in sys.stdin:
        try:
            data = json.loads(line)
            if data.get("reason") == "compiler-message":
                msg = data.get("message", {})
                level = msg.get("level")
                if level in ("error", "warning"):
                    code = msg.get("code", {}).get("code", "UNKNOWN") if msg.get("code") else "UNKNOWN"
                    rendered = msg.get("rendered", "")
                    messages[(level, code)].append(rendered)
        except Exception:
            pass

    # Sorting keys puts "error" before "warning" alphabetically
    for (level, code), items in sorted(messages.items()):
        label = f"{level.capitalize()} Code: {code}"
        print(f"\n=================== {label} (Showing {min(len(items), 5)} of {len(items)}) ===================")
        for item in items[:5]:
            print(item)
    ' | copyq add -

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

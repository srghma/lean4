---
name: project-lean-stdlib-build
description: "lean_stdlib cargo build: OOM fix (split into 5 rlib chunks), duplicate symbol fix (exclude entry-point .rs files)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 7058f11e-2861-41a3-a776-2687c29621e6
---

## lean_stdlib cargo build: split into 5 rlib chunks

**Fact:** 2269 Lean stdlib modules in one rustc invocation at opt-level=3 OOMs on a 15 GB system (~12.5 GB peak). The fix in `setup.sh` splits into ~500-module rlib chunks (lean_stdlib_0 through lean_stdlib_4) plus a root staticlib that depends on all chunks.

**Why:** rustc analysis + codegen for 2269 modules requires ~12.5 GB. Lean/* modules (202 MB) peak at ~12 GB per 500-module chunk; Init/* modules (21 MB) peak at ~2 GB. Building chunks sequentially keeps peak memory at one chunk at a time.

**How to apply:** The workspace is at `build/release/stage2/lean_stdlib/` with subdirs `lean_stdlib_0` through `lean_stdlib_4`. Build order: each chunk rlib sequentially, then the root staticlib.

## Entry-point files must be excluded from lean_stdlib

**Fact:** `Leanc.rs`, `LeanChecker.rs`, `LeanIR.rs` define `_lean_main` and `l_main___*` symbols. Including two or more of them in the same compilation unit causes `E0428` duplicate symbol errors. setup.sh detects them via `grep '^#[no_mangle] pub unsafe extern "C" fn _lean_main'` and skips their `include!` lines.

**Why:** Multiple Lean source files define `main` → all get `l_main___closed__*` symbols → same name → link-time collision.

**How to apply:** Any time entry-point .lean files are compiled together with library modules, ensure only ONE entry-point (or none) is included per compilation unit.

## Array indexing: bash (0-indexed) vs zsh (1-indexed)

**Fact:** When the Bash tool executes commands, it uses zsh (the user's shell). Zsh arrays are 1-indexed: `ALL_RS_FILES[1]` = first element, `ALL_RS_FILES[0]` = empty. Bash arrays are 0-indexed. The setup.sh uses `#!/usr/bin/env bash` so it runs correctly in bash. But ad-hoc scripts run directly via the Bash tool run in zsh → off-by-one errors.

**Why:** Chunk boundary was miscalculated when running fix scripts directly; caused Ring/Int.rs and VCGen/Entails.rs to appear in two chunks simultaneously → duplicate symbols in liblean_stdlib.a.

**How to apply:** When running multi-step bash scripts involving arrays directly via the Bash tool, wrap them in `bash << 'HEREDOC' ... HEREDOC` to force bash semantics. Never use `while IFS= read -r f; do arr+=("$f")` with arithmetic indexing directly in the Bash tool — use `bash << '...'` or rely on setup.sh.

## GOAL.md status (2026-06-08)

Both GOAL.md tests now pass:
1. `cd ./src/rust/lean_runtime/ && cargo test -p lean_runtime && cargo test -p lean_shell && cargo build -p lean_runtime && cargo build -p lean_shell` ✓
2. `CTEST_PARALLEL_LEVEL=$(nproc) ... make -C build/release ... test ARGS='-E bench/mvcgen/sym -R "elab/1921|elab/4306"'` ✓

lean_stdlib.a (423 MB): built successfully with 0 duplicate symbols (2266 modules, excluding 3 entry-point files).

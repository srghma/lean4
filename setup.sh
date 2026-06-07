#!/usr/bin/env bash
# Setup script for lean4 rust-rewrite3 (NixOS).
# Works on a completely clean project.
#
# Architecture:
#   stage0 — original C++ lean (from stage0/), built by cmake.
#             Uses EmitC backend: lean files → C files.
#   stage1 — C++ runtime (same as stage0) + EmitRust backend compiled in.
#             cmake builds the C++ runtime (kernel/util/shell/runtime/library) and
#             the Rust lean_runtime (src/rust/lean_runtime) into libleanshell.a.
#             Then stdlib.make (bash/make) drives stage0's lean binary to compile
#             the lean stdlib → C files → shared libs, and links the lean binary.
#             When stage1's lean binary runs on user code, it uses EmitRust → .rs files.
#   stage2 — Rust runtime + EmitRust.
#             stage1's lean binary compiles all lean stdlib .lean → .rs files.
#             A generated Rust crate (lean_stdlib) includes all .rs files via mod/include!.
#             cargo builds lean_stdlib + lean_runtime → pure-Rust lean binary.

set -euo pipefail

for cmd in cmake cargo rustc make; do
  if ! command -v "$cmd" &> /dev/null; then
    echo "ERROR: '$cmd' is not installed or not in PATH. Are you inside the Nix shell?" >&2
    exit 1
  fi
done

PROJECT="$(cd "$(dirname "$0")" && pwd)"
BUILD="$PROJECT/build/release"
NPROC=$(nproc)

# Default value for the test flag
RUN_TESTS=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --run-tests)
      RUN_TESTS=true
      shift
      ;;
    *)
      echo "Unknown option: $1" >&2
      echo "Usage: $0 [--run-tests]" >&2
      exit 1
      ;;
  esac
done

# ── 1. Clean ─────────────────────────────────────────────────────────────────
echo "=== Cleaning build ==="
rm -rdf "$PROJECT/build"

git clean -xn \
  -e ".direnv/" \
  -e ".envrc" \
  -e ".gemini/"

# ── 2. Check / update stage0 against upstream/master ─────────────────────────
echo "=== Checking stage0 against origin/master ==="
cd "$PROJECT"
if ! git remote get-url origin &>/dev/null; then
  echo "ERROR: remote 'origin' not found; skipping stage0 check."
  echo "  Add it: git remote add origin https://github.com/leanprover/lean4.git"
  exit 1
else
  STAGE0_DIFF="$(git diff origin/master -- stage0/ 2>&1)"
  if [ -n "$STAGE0_DIFF" ]; then
    echo "  stage0/ differs from origin/master — updating..."
    git checkout origin/master -- stage0/
    echo "  stage0/ updated."
  else
    echo "  stage0/ matches origin/master. OK."
  fi
fi

# ── 3. Build stage0 via cmake ─────────────────────────────────────────────────
# cmake is used ONLY for stage0.  It downloads cadical/leantar, compiles the
# original C++ lean, and produces stage0/bin/lean (EmitC backend).
echo "=== Configuring cmake ==="
cmake -S "$PROJECT" -B "$BUILD" -DCMAKE_BUILD_TYPE=Release

echo "=== Building stage0 (cmake) ==="
# The ExternalProject build for stage0 uses BUILD_ALWAYS=ON, so cmake always
# re-runs the build. With USE_LAKE=OFF and C_ONLY=1 the leanmake invocation
# should only compile pre-existing .c files in stage0/stdlib/ to .o files and
# must not regenerate them. If stage0/ files are nonetheless dirtied (observed
# on some NixOS setups — root cause not yet determined), restore them.
make -C "$BUILD" -j"$NPROC" stage0

# Check if stage0/ has dirty files or untracked changes
if ! git -C "$PROJECT" diff --quiet -- stage0/ || [ -n "$(git -C "$PROJECT" status --porcelain stage0/)" ]; then
  echo -e "\n\e[1;31m⚠️  WARNING: Local modifications or untracked files detected in stage0/ !\e[0m"
  echo -e "\e[31mThese files will be permanently reset/overwritten to match the clean upstream stage0 state.\e[0m"
  echo -e "\e[31mPress Ctrl+C within 3 seconds to abort this script...\e[0m"

  # Pause for 3 seconds to let the user read and optionally abort
  sleep 3

  echo "  Resetting stage0/..."
  git -C "$PROJECT" checkout -- stage0/
  git -C "$PROJECT" clean -fd -- stage0/
else
  echo "  stage0/ is clean. No reset necessary."
fi

# ── 4. Build stage1 ───────────────────────────────────────────────────────────
# cmake configure generates the stage1 build environment:
#   - leanc.sh      (compiler/linker wrapper with correct NIX store paths)
#   - lakefile.toml (lake project descriptor)
#   - stdlib.make   (make-based lean stdlib builder)
# cmake build compiles:
#   - C++ objects (kernel, util, shell, runtime, library → object files)
#   - Rust lean_runtime (src/rust/lean_runtime → libleanshell.a)
#
# stdlib.make then drives:
#   - stage0's lean binary compiles lean stdlib → C files (EmitC, since stage0 has EmitC)
#     NOTE: the lean SOURCES we're compiling include EmitRust.lean, so stage1's lean
#     binary will contain the EmitRust backend and generate .rs files when run.
#   - C files → shared libs (libInit_shared.so, libleanshared.so, etc.)
#   - lean binary linked: libleanshell.a (Rust runtime) + shared libs
echo "=== Building stage1 ==="
make -C "$BUILD" -j"$NPROC" stage1

# ── 5. Build stage2 ───────────────────────────────────────────────────────────
# Uses stage1's lean binary (with EmitRust) to compile all lean stdlib .lean files
# to .rs files, then builds a pure-Rust lean binary with cargo.
#
# Generated .rs files go into build/release/stage2/src/generated/.
# A generated lean_stdlib crate wraps them all with mod { include!(...) }.
# lean_shell_main depends on lean_stdlib + lean_runtime → stage2/bin/lean.
#
# Note: lean_runtime still links stdc++ for runtime_exception.rs (C++ RTTI shim).
# That is the only remaining C++ dependency.  Removing it requires porting
# lean_throwable to a pure-Rust panic mechanism.
echo ""
echo "=== Stage2: generating .rs files from lean stdlib ==="

STAGE1_LEAN="$BUILD/stage1/bin/lean"
STAGE1_OLEAN="$BUILD/stage1/lib/lean"
STAGE2_DIR="$BUILD/stage2"
STAGE2_RS="$STAGE2_DIR/src/generated"
STAGE2_OLEAN="$STAGE2_DIR/olean"

mkdir -p "$STAGE2_RS" "$STAGE2_OLEAN"

# Build a list of (src_file, rs_out, olean_out) for every module that has both
# a stage1 olean and a source file in src/.
COMPILE_LIST=()
while IFS= read -r olean_path; do
  rel="${olean_path#$STAGE1_OLEAN/}"
  module_path="${rel%.olean}"          # e.g. Init/Prelude
  src_file="$PROJECT/src/${module_path}.lean"
  if [ ! -f "$src_file" ]; then
    continue
  fi
  rs_out="$STAGE2_RS/${module_path}.rs"
  olean_out="$STAGE2_OLEAN/${module_path}.olean"
  mkdir -p "$(dirname "$rs_out")" "$(dirname "$olean_out")"
  COMPILE_LIST+=("$src_file|$rs_out|$olean_out")
done < <(find "$STAGE1_OLEAN" -name "*.olean" | sort)

echo "  Found ${#COMPILE_LIST[@]} modules to compile to Rust"

# Compile each module in parallel using xargs.
# Each job: LEAN_PATH=... lean --c=out.rs --o=out.olean --root=src input.lean
compile_one() {
  local src="$1" rs_out="$2" olean_out="$3"
  LEAN_PATH="$STAGE1_OLEAN" "$STAGE1_LEAN" \
    --c="$rs_out" \
    --o="$olean_out" \
    --root="$PROJECT/src" \
    "$src" 2>&1 || echo "WARN: failed to compile $src" >&2
}
export -f compile_one
export STAGE1_OLEAN STAGE1_LEAN PROJECT

printf '%s\n' "${COMPILE_LIST[@]}" | xargs -P "$NPROC" -I{} bash -c '
  IFS="|" read -r src rs_out olean_out <<< "$1"
  compile_one "$src" "$rs_out" "$olean_out"
' _ {}

shopt -s globstar
RS_FILES=("$STAGE2_RS"/**/*.rs "$STAGE2_RS"/*.rs)
echo "  Generated $(find "$STAGE2_RS" -name "*.rs" | wc -l) .rs files"

# ── 5b. Generate lean_stdlib crate ──────────────────────────────────────────
echo "=== Stage2: generating lean_stdlib crate ==="

LEAN_STDLIB_DIR="$STAGE2_DIR/lean_stdlib"
mkdir -p "$LEAN_STDLIB_DIR/src"

# Generate Cargo.toml
cat > "$LEAN_STDLIB_DIR/Cargo.toml" << 'TOML'
[package]
name = "lean_stdlib"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["staticlib"]

[dependencies]
lean_runtime = { path = "../../../../src/rust/lean_runtime" }
TOML

# Generate src/lib.rs: one flat module per generated .rs file
# Module name = path with / replaced by _ (e.g. Init/Prelude.rs → lean_Init_Prelude)
{
  echo "#![allow(warnings)]"
  echo "extern crate lean_runtime;"
  echo ""
  while IFS= read -r rs_file; do
    rel="${rs_file#$STAGE2_RS/}"
    mod_name="lean_$(echo "${rel%.rs}" | tr '/' '_')"
    # include! path is relative to this lib.rs, which is at lean_stdlib/src/lib.rs
    # generated .rs files are at stage2/src/generated/...
    # so the path from lean_stdlib/src/ is ../../src/generated/...
    rel_path="../../src/generated/${rel}"
    echo "#[allow(non_upper_case_globals,non_snake_case,non_camel_case_types,dead_code,unused_imports,clashing_extern_declarations)]"
    echo "mod ${mod_name} { include!(\"${rel_path}\"); }"
  done < <(find "$STAGE2_RS" -name "*.rs" | sort)
} > "$LEAN_STDLIB_DIR/src/lib.rs"

echo "  Generated lean_stdlib crate with $(grep -c '^mod ' "$LEAN_STDLIB_DIR/src/lib.rs") modules"

# ── 5c. Build lean_stdlib ───────────────────────────────────────────────────
# lean_stdlib lives outside src/rust/ so it cannot be a workspace member.
# Build it as a standalone crate using --manifest-path.
echo "=== Stage2: building lean_stdlib with cargo ==="
cargo build --release --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml" 2>&1 | tail -5

if [ "$RUN_TESTS" = "true" ]; then
  echo "=== Running cargo tests ==="
  (
    cd ./src/rust/lean_runtime/
    echo "cargo test -p lean_runtime"
    cargo test -p lean_runtime
    echo "cargo test -p lean_shell"
    cargo test -p lean_shell
    echo "cargo build -p lean_runtime"
    cargo build -p lean_runtime
    echo "cargo build -p lean_shell"
    cargo build -p lean_shell
  )

  echo "=== Running CTest ==="

  CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release/stage2 -j "$(nproc)" test ARGS='-E bench/mvcgen/sym'
  # CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 make -C build/release/stage2 -j "$(nproc)" test ARGS='-E bench/mvcgen/sym -R "elab/1921|elab/4306"'
else
  echo "=== Skipping tests. Use --run-tests to execute them. ==="
fi

# ── Done ──────────────────────────────────────────────────────────────────────
echo ""
echo "=== Done ==="
echo "  stage0 lean : $BUILD/stage0/bin/lean"
echo "  stage1 lean : $BUILD/stage1/bin/lean"
echo "  stage2 stdlib: $LEAN_STDLIB_DIR (liblean_stdlib.a)"
echo ""
echo "Verify:"
echo "  cd src/rust/lean_runtime && cargo test -p lean_runtime && cargo test -p lean_shell"
echo "  CTEST_PARALLEL_LEVEL=\$(nproc) CTEST_OUTPUT_ON_FAILURE=1 \\"
echo "    make -C build/release -j\$(nproc) test ARGS='-E bench/mvcgen/sym -R \"elab/1921|elab/4306\"'"

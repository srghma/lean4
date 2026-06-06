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
#   stage2 — Rust runtime + EmitRust. (TODO: bash/cargo build using stage1 lean output)

set -euo pipefail

PROJECT="$(cd "$(dirname "$0")" && pwd)"
BUILD="$PROJECT/build/release"
NPROC=$(nproc)

# ── 1. Clean ─────────────────────────────────────────────────────────────────
echo "=== Cleaning build ==="
rm -rdf "$PROJECT/build"

# ── 2. Check / update stage0 against upstream/master ─────────────────────────
echo "=== Checking stage0 against upstream/master ==="
cd "$PROJECT"
if ! git remote get-url upstream &>/dev/null; then
  echo "WARNING: remote 'upstream' not found; skipping stage0 check."
  echo "  Add it: git remote add upstream https://github.com/leanprover/lean4.git"
else
  git fetch upstream master --quiet
  STAGE0_DIFF="$(git diff upstream/master -- stage0/ 2>&1)"
  if [ -n "$STAGE0_DIFF" ]; then
    echo "  stage0/ differs from upstream/master — updating..."
    git checkout upstream/master -- stage0/
    echo "  stage0/ updated."
  else
    echo "  stage0/ matches upstream/master. OK."
  fi
fi

# ── 3. Build stage0 via cmake ─────────────────────────────────────────────────
# cmake is used ONLY for stage0.  It downloads cadical/leantar, compiles the
# original C++ lean, and produces stage0/bin/lean (EmitC backend).
echo "=== Configuring cmake ==="
cmake -S "$PROJECT" -B "$BUILD" -DCMAKE_BUILD_TYPE=Release

echo "=== Building stage0 (cmake) ==="
make -C "$BUILD" -j"$NPROC" stage0

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

# ── 5. Build stage2 (TODO) ────────────────────────────────────────────────────
# Stage2 uses stage1's lean binary (which has EmitRust) to compile the lean
# stdlib to Rust, then builds a pure-Rust lean binary with cargo.
#
# The EmitRust flag: stage1's Shell.lean repurposes --c= to invoke EmitRust:
#   "$BUILD/stage1/bin/lean" --c=Module.rs --root=... Module.lean
# generates valid Rust (verified: produces correct Rust with mangled identifiers).
#
# Blocking issue: the kernel (kernel_environment, kernel_expr, etc.) still
# calls back into C++ via lean_cxx_* FFI functions.  Until those are ported
# to pure Rust, a fully C++-free stage2 binary is not achievable.
# Tracking: see src/rust/lean_runtime/src/kernel_*.rs for the remaining stubs.
#
# When the kernel port is complete, stage2 will be:
#   a. Run stage1 lean on every stdlib .lean file → .rs files in stage2/lib/temp/
#      (use the same lake build pipeline from stdlib.make but override the lean binary
#      to stage1 and set irDir to a stage2 output directory)
#   b. The generated .rs files form a cargo crate alongside src/rust/lean_runtime
#   c. cargo build --release -p lean_shell_main (pure Rust binary)
#   d. No C++ objects; build.rs must not link stdc++ once kernel_exception.rs
#      is ported away from C++ RTTI (currently uses _ZTVN10__cxxabiv120... symbols)
echo ""
echo "=== Stage2: kernel C→Rust port required first (see setup.sh step 5) ==="

# ── Done ──────────────────────────────────────────────────────────────────────
echo ""
echo "=== Done ==="
echo "  stage0 lean : $BUILD/stage0/bin/lean"
echo "  stage1 lean : $BUILD/stage1/bin/lean"
echo ""
echo "Verify:"
echo "  cd src/rust/lean_runtime && cargo test -p lean_runtime && cargo test -p lean_shell"
echo "  CTEST_PARALLEL_LEVEL=\$(nproc) CTEST_OUTPUT_ON_FAILURE=1 \\"
echo "    make -C build/release -j\$(nproc) test ARGS='-E bench/mvcgen/sym -R \"elab/1921|elab/4306\"'"

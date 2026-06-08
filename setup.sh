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

RUN_TESTS=false
FROM_STAGE="clean"  # clean | stage0 | stage1 | rs | cargo | setup

while [[ $# -gt 0 ]]; do
  case "$1" in
    --run-tests)    RUN_TESTS=true; shift ;;
    --from=*)       FROM_STAGE="${1#--from=}"; shift ;;
    *)
      echo "Unknown option: $1" >&2
      cat >&2 << 'EOF'
Usage: setup.sh [--from=STAGE] [--run-tests]

  --from=clean   (default) full rebuild from scratch
  --from=stage0  skip clean
  --from=stage1  skip clean + stage0
  --from=rs      skip clean + stage0 + stage1  (reuse stage1 binary, regen .rs)
  --from=cargo   skip clean + stage0 + stage1 + .rs gen  (reuse .rs, rebuild cargo)
  --from=setup   skip all builds, just cmake-configure stage2 + optional tests

  --run-tests    run ctest against stage2 after setup
EOF
      exit 1
      ;;
  esac
done

# Derive skip flags from FROM_STAGE (pipeline is linear: each stage implies all before it)
SKIP_CLEAN=false; SKIP_STAGE0=false; SKIP_STAGE1=false; SKIP_RS=false; SKIP_CARGO=false
case "$FROM_STAGE" in
  clean)  ;;
  stage0) SKIP_CLEAN=true ;;
  stage1) SKIP_CLEAN=true; SKIP_STAGE0=true ;;
  rs)     SKIP_CLEAN=true; SKIP_STAGE0=true; SKIP_STAGE1=true ;;
  cargo)  SKIP_CLEAN=true; SKIP_STAGE0=true; SKIP_STAGE1=true; SKIP_RS=true ;;
  setup)  SKIP_CLEAN=true; SKIP_STAGE0=true; SKIP_STAGE1=true; SKIP_RS=true; SKIP_CARGO=true ;;
  *)
    echo "Unknown stage '$FROM_STAGE'; valid: clean stage0 stage1 rs cargo setup" >&2
    exit 1
    ;;
esac

# ── 1. Clean ─────────────────────────────────────────────────────────────────
if [[ "$SKIP_CLEAN" == "true" ]]; then
  echo "=== Skipping clean (--from=$FROM_STAGE) ==="
  [[ "$SKIP_RS"    != "true" ]] && rm -rf "$PROJECT/build/release/stage2/src/generated/"
  [[ "$SKIP_CARGO" != "true" ]] && rm -rf "$PROJECT/build/release/stage2/lean_stdlib/"
else
  echo "=== Cleaning build ==="
  rm -rdf "$PROJECT/build"
  git clean -d --force -x \
    -e ".direnv/" \
    -e ".envrc" \
    -e ".gemini/"
fi

# ── 2. Check / update stage0 against upstream/master ─────────────────────────
if [[ "$SKIP_STAGE0" == "true" ]]; then
  echo "=== Skipping stage0 check (--from=$FROM_STAGE) ==="
else
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
  echo "=== Configuring cmake ==="
  cmake -S "$PROJECT" -B "$BUILD" -DCMAKE_BUILD_TYPE=Release

  echo "=== Building stage0 (cmake) ==="
  make -C "$BUILD" -j"$NPROC" stage0

  # Check if stage0/ has dirty files or untracked changes
  if ! git -C "$PROJECT" diff --quiet -- stage0/ || [ -n "$(git -C "$PROJECT" status --porcelain stage0/)" ]; then
    echo -e "\n\e[1;31m⚠️  WARNING: Local modifications or untracked files detected in stage0/ !\e[0m"
    echo -e "\e[31mThese files will be permanently reset/overwritten to match the clean upstream stage0 state.\e[0m"
    echo -e "\e[31mPress Ctrl+C within 3 seconds to abort this script...\e[0m"
    sleep 3
    echo "  Resetting stage0/..."
    git -C "$PROJECT" checkout -- stage0/
    git -C "$PROJECT" clean -fd -- stage0/
  else
    echo "  stage0/ is clean. No reset necessary."
  fi
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
if [[ "$SKIP_STAGE1" == "true" ]]; then
  echo "=== Skipping stage1 build (--from=$FROM_STAGE) ==="
else
  echo "=== Building stage1 ==="
  make -C "$BUILD" -j"$NPROC" stage1
fi

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
STAGE1_LEAN="$BUILD/stage1/bin/lean"
STAGE1_OLEAN="$BUILD/stage1/lib/lean"
STAGE2_DIR="$BUILD/stage2"
STAGE2_RS="$STAGE2_DIR/src/generated"
STAGE2_OLEAN="$STAGE2_DIR/olean"
LEAN_STDLIB_DIR="$STAGE2_DIR/lean_stdlib"

if [[ "$SKIP_RS" != "true" ]]; then

echo ""
echo "=== Stage2: generating .rs files from lean stdlib ==="

mkdir -p "$STAGE2_RS" "$STAGE2_OLEAN"

# Build a list of (src_file, rs_out, olean_out) for every module that has both
# a stage1 olean and a source file in src/.
COMPILE_LIST=()
while IFS= read -r olean_path; do
  rel="${olean_path#$STAGE1_OLEAN/}"
  module_path="${rel%.olean}"          # e.g. Init/Prelude or Lake/Build/Common
  src_file="$PROJECT/src/${module_path}.lean"
  # Lake sources live under src/lake/, not src/
  if [ ! -f "$src_file" ] && [[ "$module_path" == Lake/* || "$module_path" == "Lake" ]]; then
    src_file="$PROJECT/src/lake/${module_path}.lean"
  fi
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

echo "  Generated $(find "$STAGE2_RS" -name "*.rs" | wc -l) .rs files"

fi  # end SKIP_RS gate

if [[ "$SKIP_CARGO" != "true" ]]; then

# ── 5b. Generate lean_stdlib workspace (4 per-package rlibs) ─────────────────
# Each Lean package (Init, Std, Lean, Lake) becomes its own rlib crate.
# Cargo builds them sequentially by dependency order, so only one rustc process
# runs at a time.  Generated .rs files use `use crate::Mod::Path::*` and
# `use lean_PACKAGE::Mod::Path::*` instead of extern "C" blocks.
echo "=== Stage2: generating lean_stdlib workspace (4 packages) ==="

mkdir -p "$LEAN_STDLIB_DIR"

# Write the Python tree-builder script used to generate nested pub mod trees
# from flat lists of .rs file paths.
cat > /tmp/lean_gen_lib_rs.py << 'PYEOF'
import sys
from collections import OrderedDict

paths = [l.strip() for l in sys.stdin if l.strip()]

class Node:
    def __init__(self):
        self.has_file = False
        self.children = OrderedDict()

root = Node()
for p in sorted(paths):
    parts = p.replace('.rs', '').split('/')
    node = root
    for i, part in enumerate(parts):
        if part not in node.children:
            node.children[part] = Node()
        if i == len(parts) - 1:
            node.children[part].has_file = True
        node = node.children[part]

def emit(node, prefix, indent):
    pad = '    ' * indent
    for name, child in node.children.items():
        print(f'{pad}pub mod {name} {{')
        if child.has_file:
            file_path = prefix + name + '.rs'
            print(f'{pad}    include!("../../../src/generated/{file_path}");')
        if child.children:
            emit(child, prefix + name + '/', indent + 1)
        print(f'{pad}}}')

emit(root, '', 0)
PYEOF

# Package order follows the dependency DAG: init → std → lean → lake
# Each package only includes .rs files under its top-level prefix directory.
declare -A PKG_PREFIX PKG_DEPS
PKG_PREFIX=([lean_init]="Init/" [lean_std]="Std/" [lean_lean]="Lean/" [lean_lake]="Lake/")
# Paths relative to lean_PACKAGE/Cargo.toml (= lean_stdlib/lean_PACKAGE/):
#   lean_runtime: ../../../../../src/rust/lean_runtime
#   (lean_PACKAGE → lean_stdlib → stage2 → release → build → project)
PKG_DEPS[lean_init]='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }'
PKG_DEPS[lean_std]='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }'
PKG_DEPS[lean_lean]='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }'
PKG_DEPS[lean_lake]='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }
lean_lean = { path = "../lean_lean" }'

PACKAGES=(lean_init lean_std lean_lean lean_lake)
WORKSPACE_MEMBERS=""

for pkg in "${PACKAGES[@]}"; do
  prefix="${PKG_PREFIX[$pkg]}"
  pkg_dir="$LEAN_STDLIB_DIR/$pkg"
  mkdir -p "$pkg_dir/src"

  cat > "$pkg_dir/Cargo.toml" << PKG_TOML
[package]
name = "${pkg}"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${PKG_DEPS[$pkg]}
PKG_TOML

  # Collect .rs files for this package.
  # Includes the top-level package file (e.g. Init.rs) AND all files under the prefix dir.
  local_prefix="${prefix%/}"   # "Init" from "Init/"
  mapfile -t pkg_files < <({
    [[ -f "$STAGE2_RS/${local_prefix}.rs" ]] && echo "${local_prefix}.rs"
    { find "$STAGE2_RS/$prefix" -name "*.rs" 2>/dev/null || true; } | sed "s|$STAGE2_RS/||"
  } | sort)
  total_pkg="${#pkg_files[@]}"

  # Generate lib.rs with nested pub mod tree via the Python helper.
  # The tree handles both leaf modules and directory+file collisions (e.g.
  # Init/Data.rs exists alongside Init/Data/List.rs).
  {
    echo "#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]"
    if [[ ${#pkg_files[@]} -gt 0 ]]; then
      printf '%s\n' "${pkg_files[@]}" | python3 /tmp/lean_gen_lib_rs.py
    fi
  } > "$pkg_dir/src/lib.rs"

  echo "  Package $pkg: $total_pkg modules"

  WORKSPACE_MEMBERS+="  \"${pkg}\","$'\n'
done

# Root lean_stdlib crate: workspace root + staticlib that links all packages.
# Paths relative to lean_stdlib/Cargo.toml (= lean_stdlib/):
#   lean_runtime: ../../../../src/rust/lean_runtime
#   (lean_stdlib → stage2 → release → build → project)
mkdir -p "$LEAN_STDLIB_DIR/src"

# lean_binary: the stage2 lean executable.
# Depends on lean_shell (rlib, provides lean_main) + all stdlib rlibs.
# lean_shell calls lean_shell_main() which lives in lean_lean (Lean.Shell).
mkdir -p "$LEAN_STDLIB_DIR/lean_binary/src"

cat > "$LEAN_STDLIB_DIR/lean_binary/Cargo.toml" << 'BINARY_TOML'
[package]
name = "lean_binary"
version = "0.1.0"
edition = "2021"
publish = false

[[bin]]
name = "lean"
path = "src/main.rs"

[dependencies]
lean_shell = { path = "../../../../../src/rust/lean_shell" }
lean_init  = { path = "../lean_init" }
lean_std   = { path = "../lean_std" }
lean_lean  = { path = "../lean_lean" }
lean_lake  = { path = "../lean_lake" }
BINARY_TOML

cat > "$LEAN_STDLIB_DIR/lean_binary/src/main.rs" << 'MAIN_RS'
fn main() {
    let args: Vec<std::ffi::CString> = std::env::args()
        .map(|a| std::ffi::CString::new(a).unwrap_or_default())
        .collect();
    let mut cargs: Vec<*mut core::ffi::c_char> =
        args.iter().map(|a| a.as_ptr() as *mut _).collect();
    cargs.push(core::ptr::null_mut());
    let exit_code = unsafe {
        lean_shell::lean_main(args.len() as core::ffi::c_int, cargs.as_mut_ptr())
    };
    std::process::exit(exit_code);
}
MAIN_RS

cat > "$LEAN_STDLIB_DIR/Cargo.toml" << ROOT_TOML
[workspace]
members = [
${WORKSPACE_MEMBERS}  "lean_binary",
]

[package]
name = "lean_stdlib"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["staticlib"]

[dependencies]
lean_runtime = { path = "../../../../src/rust/lean_runtime", features = ["export-runtime-ffi"] }
lean_init  = { path = "lean_init" }
lean_std   = { path = "lean_std" }
lean_lean  = { path = "lean_lean" }
lean_lake  = { path = "lean_lake" }

[profile.release]
opt-level = 1
codegen-units = 1
lto = false

# lean_lean has ~1189 modules.  Even codegen-units=16 OOMs because Rayon runs
# all units in parallel across CPU cores.  opt-level=0 skips most LLVM passes
# (memory drops ~10×); RAYON_NUM_THREADS=1 is passed in the build step below to
# run codegen units sequentially.  Trade-off: lean stdlib runs slower, but that
# is acceptable for a correctness-testing build.
[profile.release.package.lean_lean]
opt-level = 0
codegen-units = 16
incremental = true
ROOT_TOML

printf '%s\n' \
  "#![allow(warnings)]" \
  "extern crate lean_runtime;" \
  "extern crate lean_init;" \
  "extern crate lean_std;" \
  "extern crate lean_lean;" \
  "extern crate lean_lake;" \
  > "$LEAN_STDLIB_DIR/src/lib.rs"

echo "  Generated lean_stdlib workspace"

# ── 5c. Build lean_stdlib (sequential by dependency order) ─────────────────
# Build packages in DAG order so Cargo never tries to run two large rustc
# invocations at the same time.  lean_lean (~900 modules) is the memory peak.
echo "=== Stage2: building lean_stdlib with cargo (sequential packages) ==="
for pkg in "${PACKAGES[@]}"; do
  echo "  cargo build $pkg..."
  # lean_lean: opt-level=0 + RAYON_NUM_THREADS=1 runs 16 codegen units
  # sequentially with no optimization passes — peak RAM stays manageable.
  if [[ "$pkg" == "lean_lean" ]]; then
    RAYON_NUM_THREADS=1 RUSTFLAGS="-C link-arg=-fuse-ld=lld" cargo build --release -p "$pkg" \
      --jobs 1 \
      --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"
  else
    cargo build --release -p "$pkg" \
      --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"
  fi
done
echo "  cargo build final lean_stdlib staticlib..."
cargo build --release -p lean_stdlib \
  --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"

# ── 5d. Build the stage2 lean binary ──────────────────────────────────────────
# lean_binary depends on lean_shell (rlib) + all 4 stdlib packages.
# lean_shell.lean_main → lean_shell_main (from Lean.Shell in lean_lean).
echo "=== Stage2: building lean binary ==="
echo "  cargo build lean_binary..."
cargo build --release -p lean_binary \
  --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"

mkdir -p "$STAGE2_DIR/bin"
cp "$LEAN_STDLIB_DIR/target/release/lean" "$STAGE2_DIR/bin/lean"
echo "  stage2 lean binary: $STAGE2_DIR/bin/lean"

fi  # end SKIP_CARGO gate

# ── 5e. Populate stage2 layout for cmake test infrastructure ─────────────────
# Copy oleans + support binaries so the test env matches what cmake tests expect.
echo "=== Stage2: setting up cmake test infrastructure ==="
mkdir -p "$STAGE2_DIR/lib/lean" "$STAGE2_DIR/bin"
# Oleans: use stage2-generated ones (identical content to stage1 since same sources)
rsync -a --delete "$STAGE2_OLEAN/" "$STAGE2_DIR/lib/lean/"
# Tests also need cadical, leantar, and leanc.sh from stage1
for f in cadical leantar leanc.sh; do
  [[ -e "$BUILD/stage1/bin/$f" ]] && cp -f "$BUILD/stage1/bin/$f" "$STAGE2_DIR/bin/$f"
done
# Generate leanc wrapper that uses stage2 lean binary
cat > "$STAGE2_DIR/bin/leanc" << LEANC_SH
#!/usr/bin/env bash
exec "$STAGE2_DIR/bin/lean" --run "\$@"
LEANC_SH
chmod +x "$STAGE2_DIR/bin/leanc"

# cmake configure for stage2 (just generates CTestTestfile.cmake +
# with_stage2_test_env.sh — no build step, no Lean → C compilation).
# We pass PREV_STAGE=stage1 so cmake can find libs/headers; our Rust lean
# binary at stage2/bin/lean will be used by tests via the generated PATH.
cmake -S "$PROJECT/src" -B "$STAGE2_DIR" \
  -DCMAKE_BUILD_TYPE=Release \
  -DSTAGE=2 \
  -DPREV_STAGE="$BUILD/stage1"
echo "  stage2 cmake configured — tests point at $STAGE2_DIR/bin/lean"

if [ "$RUN_TESTS" = "true" ]; then
  echo "=== Running cargo tests ==="
  (
    cd "$PROJECT/src/rust/lean_runtime/"
    cargo test -p lean_runtime
    cargo test -p lean_shell
    cargo build -p lean_runtime
    cargo build -p lean_shell
  )

  echo "=== Running CTest against stage2 (Rust lean binary) ==="
  CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
    ctest --test-dir "$STAGE2_DIR" -E bench -j "$(nproc)" --output-on-failure
else
  echo "=== Skipping tests. Use --run-tests to execute them. ==="
fi

# ── Done ──────────────────────────────────────────────────────────────────────
echo ""
echo "=== Done ==="
echo "  stage0 lean : $BUILD/stage0/bin/lean"
echo "  stage1 lean : $BUILD/stage1/bin/lean"
echo "  stage2 lean : $STAGE2_DIR/bin/lean  (pure Rust)"
echo "  stage2 stdlib: $LEAN_STDLIB_DIR (liblean_stdlib.a)"
echo ""
echo "Run tests against stage2 (Rust lean binary):"
echo "  CTEST_PARALLEL_LEVEL=\$(nproc) CTEST_OUTPUT_ON_FAILURE=1 \\"
echo "    ctest --test-dir $STAGE2_DIR -E bench -j\$(nproc)"
echo ""
echo "Run a single test manually:"
echo "  tests/with_stage2_test_env.sh tests/elab/run_test.sh grind_ematch.lean"

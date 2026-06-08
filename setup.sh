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
#             lean_lean (~503 MB of .rs source) is topo-sorted and split into N
#             sub-crates (~130 MB each) so each rustc invocation fits in RAM.
#             cargo builds lean_init → lean_std → lean_lean_0..N → lean_lean
#             (umbrella) → lean_lake → lean_binary.

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
# lean_lean (~503 MB) is topologically split into N sub-crates (~130 MB each)
# so each rustc invocation fits within 15 GB RAM.
# lean_shell_main depends on lean_binary → lean_shell → all stdlib packages.
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

# ── 5b. Generate lean_stdlib workspace ────────────────────────────────────────
# lean_lean (~503 MB) is too large for a single rustc invocation on 15 GB RAM.
# Solution: topological sort of Lean/* modules → split into N sub-crates (~130 MB).
# Each sub-crate includes its own files and re-exports modules from lower groups.
# lean_lean umbrella crate (pub use lean_lean_{N-1}::*) keeps the public API stable.
# lean_lake files use `use lean_lake::...` (self-reference) so we add
# `extern crate self as lean_lake;` to lean_lake's lib.rs.
echo "=== Stage2: generating lean_stdlib workspace ==="

mkdir -p "$LEAN_STDLIB_DIR"

# ── Python: simple pub mod tree generator (lean_init, lean_std, lean_lake)
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

# ── Python: topological sort of lean_lean modules → group assignments
cat > /tmp/lean_lean_topo_split.py << 'PYEOF'
import sys, os, re
from collections import defaultdict, deque

base_dir = sys.argv[1]
target = int(sys.argv[2]) if len(sys.argv) > 2 else 130_000_000

lean_dir = os.path.join(base_dir, 'Lean')
modules = {}  # key: "Lean/Meta/Basic", value: file size

for dirpath, _, filenames in os.walk(lean_dir):
    for fn in filenames:
        if fn.endswith('.rs'):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, base_dir)  # "Lean/Meta/Basic.rs"
            modules[rel[:-3]] = os.path.getsize(full)

top = os.path.join(base_dir, 'Lean.rs')
if os.path.exists(top):
    modules['Lean'] = os.path.getsize(top)

# Parse use crate::Lean::... dependencies from each file
use_re = re.compile(r'\buse crate::(Lean(?:::[A-Za-z_][A-Za-z0-9_]*)+)')

deps = defaultdict(set)   # mod_key -> set of mod_keys it depends on
rdeps = defaultdict(set)  # reverse: mod_key -> set that depend on it

for mod_key in modules:
    rs = os.path.join(base_dir, mod_key + '.rs')
    try:
        content = open(rs, errors='replace').read()
        seen = set()
        for m in use_re.finditer(content):
            parts = m.group(1).split('::')
            # Find longest prefix that is a module in our dict
            dep = None
            for i in range(len(parts), 0, -1):
                k = '/'.join(parts[:i])
                if k in modules and k != mod_key:
                    dep = k
                    break
            if dep and dep not in seen:
                seen.add(dep)
                deps[mod_key].add(dep)
    except:
        pass

for m, ds in deps.items():
    for d in ds:
        rdeps[d].add(m)

# Kahn's topological sort (deps-first ordering)
in_deg = {k: len(deps.get(k, set())) for k in modules}
q = deque(sorted(k for k in modules if in_deg[k] == 0))
order = []
while q:
    k = q.popleft()
    order.append(k)
    for d in sorted(rdeps.get(k, set())):
        in_deg[d] -= 1
        if in_deg[d] == 0:
            q.append(d)
# Append any remaining (cycles shouldn't happen in valid Lean code)
order.extend(sorted(set(modules) - set(order)))

# Split into groups by cumulative file size
groups = [[]]
cur_sz = 0
for k in order:
    sz = modules[k]
    if cur_sz + sz > target and groups[-1]:
        groups.append([])
        cur_sz = 0
    groups[-1].append(k)
    cur_sz += sz

for gi, grp in enumerate(groups):
    for k in grp:
        print(f'{gi}\t{k}')
PYEOF

# ── Python: lib.rs generator for lean_lean sub-packages (split with re-exports)
# For group G's lib.rs:
#   - modules in group G: use include!()
#   - modules in groups < G: use `pub use lean_lean_M::path::*;` (re-export)
# When a file node emits a wildcard re-export, its children in groups <= that file's
# group are already covered by the wildcard, so we skip them (min_emit_group tracks this).
cat > /tmp/lean_lean_gen_lib_rs.py << 'PYEOF'
import sys
from collections import OrderedDict

tsv_file = sys.argv[1]
cur_grp = int(sys.argv[2])

# Load assignments for groups 0..cur_grp
assignments = {}
with open(tsv_file) as f:
    for line in f:
        parts = line.rstrip('\n').split('\t', 1)
        if len(parts) == 2:
            g, k = int(parts[0]), parts[1]
            if g <= cur_grp:
                assignments[k] = g

class Node:
    def __init__(self):
        self.grp = None  # group of .rs file for this node (None if no file)
        self.children = OrderedDict()

root = Node()
for k in sorted(assignments):
    parts = k.split('/')
    node = root
    for part in parts:
        if part not in node.children:
            node.children[part] = Node()
        node = node.children[part]
    node.grp = assignments[k]

LIB = '../../../src/generated'

def has_in_range(node, lo, hi):
    """True if this subtree has any .rs file with group in [lo, hi]."""
    if node.grp is not None and lo <= node.grp <= hi:
        return True
    return any(has_in_range(c, lo, hi) for c in node.children.values())

def emit(node, path, indent, lo):
    """
    Emit pub mod tree for lean_lean_{cur_grp}.
    lo: minimum group index to emit (modules in groups < lo are covered by parent wildcard).
    """
    pad = '    ' * indent
    for name, child in node.children.items():
        cp = path + name
        if not has_in_range(child, lo, cur_grp):
            continue
        print(f'{pad}pub mod {name} {{')
        nxt_lo = lo
        if child.grp is not None and lo <= child.grp <= cur_grp:
            if child.grp == cur_grp:
                # Include this file's content directly
                print(f'{pad}    include!("{LIB}/{cp}.rs");')
                # include!() doesn't cover sub-modules, keep lo unchanged
            else:
                # Re-export from lower group crate (wildcard covers all of that crate's
                # sub-modules too, so advance lo to avoid re-defining those sub-modules)
                g = child.grp
                rp = cp.replace('/', '::')
                print(f'{pad}    pub use lean_lean_{g}::{rp}::*;')
                nxt_lo = g + 1
        if child.children:
            emit(child, cp + '/', indent + 1, nxt_lo)
        print(f'{pad}}}')

emit(root, '', 0, 0)
PYEOF

# ── Run topo-split to determine lean_lean group assignments
echo "  Topo-sorting lean_lean modules (target 130 MB per group)..."
python3 /tmp/lean_lean_topo_split.py "$STAGE2_RS" 130000000 > /tmp/lean_lean_groups.tsv
NUM_LEAN_GROUPS=$(awk -F'\t' 'BEGIN{m=-1}{n=$1+0; if(n>m)m=n}END{print m+1}' /tmp/lean_lean_groups.tsv)
echo "  lean_lean split into $NUM_LEAN_GROUPS groups:"
for ((G=0; G<NUM_LEAN_GROUPS; G++)); do
  cnt=$(grep -c "^${G}	" /tmp/lean_lean_groups.tsv 2>/dev/null || echo 0)
  sz=$(awk -F'\t' -v g="$G" '$1==g{s+=1}END{print s+0}' /tmp/lean_lean_groups.tsv)
  echo "    lean_lean_${G}: ${cnt} modules"
done

# ── Package generation helpers
PKG_DEPS_lean_init='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }'
PKG_DEPS_lean_std='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }'
PKG_DEPS_lean_lake='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }
lean_lean = { path = "../lean_lean" }'

declare -a PACKAGES=()

# ── Generate lean_init and lean_std (simple include!-based packages)
for pkg in lean_init lean_std; do
  case "$pkg" in
    lean_init) prefix="Init/"  ; pkg_deps="$PKG_DEPS_lean_init" ;;
    lean_std)  prefix="Std/"   ; pkg_deps="$PKG_DEPS_lean_std"  ;;
  esac
  PACKAGES+=("$pkg")
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
${pkg_deps}
PKG_TOML

  local_prefix="${prefix%/}"
  mapfile -t pkg_files < <({
    [[ -f "$STAGE2_RS/${local_prefix}.rs" ]] && echo "${local_prefix}.rs"
    { find "$STAGE2_RS/$prefix" -name "*.rs" 2>/dev/null || true; } | sed "s|$STAGE2_RS/||"
  } | sort)
  {
    echo "#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]"
    [[ ${#pkg_files[@]} -gt 0 ]] && printf '%s\n' "${pkg_files[@]}" | python3 /tmp/lean_gen_lib_rs.py
  } > "$pkg_dir/src/lib.rs"
  echo "  Package $pkg: ${#pkg_files[@]} modules"
done

# ── Generate lean_lean_0..N-1 (topological split sub-packages)
LEAN_SUB_PKGS=()
for ((G=0; G<NUM_LEAN_GROUPS; G++)); do
  pkg="lean_lean_${G}"
  LEAN_SUB_PKGS+=("$pkg")
  PACKAGES+=("$pkg")
  pkg_dir="$LEAN_STDLIB_DIR/$pkg"
  mkdir -p "$pkg_dir/src"

  # Deps: lean_runtime + lean_init + lean_std + all lower lean_lean_G sub-packages
  dep_lines='lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }'
  for ((H=0; H<G; H++)); do
    dep_lines+="
lean_lean_${H} = { path = \"../lean_lean_${H}\" }"
  done

  cat > "$pkg_dir/Cargo.toml" << PKG_TOML
[package]
name = "${pkg}"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${dep_lines}
PKG_TOML

  cnt=$(grep -c "^${G}	" /tmp/lean_lean_groups.tsv 2>/dev/null || echo 0)
  {
    echo "#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]"
    python3 /tmp/lean_lean_gen_lib_rs.py /tmp/lean_lean_groups.tsv "$G"
  } > "$pkg_dir/src/lib.rs"
  echo "  Package $pkg: ${cnt} modules"
done

# ── Generate lean_lean umbrella (re-exports the top sub-package chain)
# lean_lake files use `use lean_lean::Lean::...` so they need this umbrella.
LAST_G=$((NUM_LEAN_GROUPS - 1))
pkg="lean_lean"
PACKAGES+=("$pkg")
pkg_dir="$LEAN_STDLIB_DIR/$pkg"
mkdir -p "$pkg_dir/src"

cat > "$pkg_dir/Cargo.toml" << UMBRELLA_TOML
[package]
name = "lean_lean"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
lean_lean_${LAST_G} = { path = "../lean_lean_${LAST_G}" }
UMBRELLA_TOML

printf '%s\n' \
  '#![allow(warnings)]' \
  "pub use lean_lean_${LAST_G}::*;" \
  > "$pkg_dir/src/lib.rs"
echo "  Package lean_lean: umbrella → lean_lean_${LAST_G}"

# ── Generate lean_lake
# Lake .rs files are compiled with module name "lake.Lake.*" which EmitRust maps to
# the cross-package form `use lean_lake::Lake::...` even for intra-lake deps.
# `extern crate self as lean_lake;` aliases the current crate so those use paths work.
pkg="lean_lake"
PACKAGES+=("$pkg")
pkg_dir="$LEAN_STDLIB_DIR/$pkg"
mkdir -p "$pkg_dir/src"

cat > "$pkg_dir/Cargo.toml" << PKG_TOML
[package]
name = "lean_lake"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${PKG_DEPS_lean_lake}
PKG_TOML

mapfile -t pkg_files < <({
  [[ -f "$STAGE2_RS/Lake.rs" ]] && echo "Lake.rs"
  { find "$STAGE2_RS/Lake/" -name "*.rs" 2>/dev/null || true; } | sed "s|$STAGE2_RS/||"
} | sort)
{
  echo "#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]"
  echo "extern crate self as lean_lake;"
  [[ ${#pkg_files[@]} -gt 0 ]] && printf '%s\n' "${pkg_files[@]}" | python3 /tmp/lean_gen_lib_rs.py
} > "$pkg_dir/src/lib.rs"
echo "  Package lean_lake: ${#pkg_files[@]} modules"

# ── Root workspace Cargo.toml + lean_stdlib staticlib + lean_binary
mkdir -p "$LEAN_STDLIB_DIR/src"
mkdir -p "$LEAN_STDLIB_DIR/lean_binary/src"

WORKSPACE_MEMBERS=""
for pkg in "${PACKAGES[@]}"; do
  WORKSPACE_MEMBERS+="  \"${pkg}\","$'\n'
done
WORKSPACE_MEMBERS+='  "lean_binary",'$'\n'

# Profile overrides: lean_lean sub-packages get opt-level=0 + codegen-units=1
# to minimize peak RAM per rustc invocation (type checking + codegen).
PROFILE_OVERRIDES=""
for pkg in "${LEAN_SUB_PKGS[@]}"; do
  PROFILE_OVERRIDES+="
[profile.release.package.${pkg}]
opt-level = 0
codegen-units = 1
"
done

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
${WORKSPACE_MEMBERS}]

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
${PROFILE_OVERRIDES}
ROOT_TOML

printf '%s\n' \
  "#![allow(warnings)]" \
  "extern crate lean_runtime;" \
  "extern crate lean_init;" \
  "extern crate lean_std;" \
  "extern crate lean_lean;" \
  "extern crate lean_lake;" \
  > "$LEAN_STDLIB_DIR/src/lib.rs"

echo "  Generated lean_stdlib workspace (${#PACKAGES[@]} packages)"

# ── 5c. Build lean_stdlib (sequential by dependency order) ─────────────────────
# lean_lean sub-packages (~130 MB each) use opt-level=0 + codegen-units=1.
# Building sequentially ensures only one rustc invocation at a time.
echo "=== Stage2: building lean_stdlib with cargo (sequential packages) ==="
for pkg in "${PACKAGES[@]}"; do
  echo "  cargo build $pkg..."
  cargo build --release -p "$pkg" \
    --future-incompat-report \
    --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"
done
echo "  cargo build final lean_stdlib staticlib..."
cargo build --release -p lean_stdlib \
  --future-incompat-report \
  --manifest-path "$LEAN_STDLIB_DIR/Cargo.toml"

# ── 5d. Build the stage2 lean binary ──────────────────────────────────────────
echo "=== Stage2: building lean binary ==="
cargo build --release -p lean_binary \
  --future-incompat-report \
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

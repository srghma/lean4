#!/usr/bin/env python3
"""
Extract all public function names from generated_abi.rs and update headerExternNames
in EmitRust.lean between the GEN/ENDGEN markers.

Usage: python3 srghmascripts/gen_abi_names.py [--check]

  --check   exit 1 if EmitRust.lean is out of date (CI mode)
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).parent.parent
ABI_RS = ROOT / "src/rust/lean_runtime/src/generated_abi.rs"
EMIT_LEAN = ROOT / "src/Lean/Compiler/LCNF/EmitRust.lean"

# Struct/type names in generated_abi.rs that are NOT functions
NON_FN_IDENTS = {
    "lean_object", "lean_once_cell", "lean_sarray_object",
    "lean_ctor_object", "lean_closure_object", "lean_array_object",
    "lean_string_object", "lean_thunk_object",
}

def extract_names(content: str) -> list[str]:
    names = set()

    # 1. Top-level pub (unsafe )? fn NAME  — these are INLINE Rust functions
    # NOTE: do NOT include pub fn inside extern "C" { } blocks — those are C symbols
    # with potentially different arities from what Lean's LCNF expects. The generated
    # .rs files will emit their own extern "C" declarations for those.
    in_extern = False
    depth = 0
    for line in content.split('\n'):
        if re.search(r'extern\s+"C"\s*\{', line):
            in_extern = True; depth = 1; continue
        if in_extern:
            depth += line.count('{') - line.count('}')
            if depth <= 0:
                in_extern = False
            continue
        m = re.match(r'^pub (?:unsafe )?fn (\w+)\s*[<(]', line)
        if m:
            names.add(m.group(1))

    # 2. pub use re-exports: pub use ...::NAME;
    for m in re.finditer(r'^pub use .*::(\w+);', content, re.MULTILINE):
        names.add(m.group(1))

    # 3. Macro invocations: extract lean_* idents from macro call bodies.
    #    Strategy: for each macro invocation (NAME! { ... } or NAME! { ... }),
    #    collect all lean_[a-z][a-z0-9_]* tokens that aren't known struct types.
    #    This catches lean_uint_ops!, lean_ctor_scalar_accessors!, lean_heap_boxing!,
    #    lean_apply_fns!, lean_scalar_once! etc.
    for m in re.finditer(r'\b\w+!\s*\{([^}]*(?:\{[^}]*\}[^}]*)*)\}', content, re.DOTALL):
        body = m.group(1)
        for ident in re.finditer(r'\blean_[a-z][a-z0-9_]*\b', body):
            n = ident.group(0)
            if n not in NON_FN_IDENTS:
                names.add(n)

    # Filter: only keep lean_* names
    return sorted(n for n in names if n.startswith('lean_'))


def format_lean_array(names: list[str]) -> str:
    lines = []
    for n in names:
        lines.append(f'  "{n}",')
    # Remove trailing comma from last entry
    if lines:
        lines[-1] = lines[-1].rstrip(',')
    return '\n'.join(lines)


MARKER_START = "-- BEGIN GENERATED headerExternNames"
MARKER_END   = "-- END GENERATED headerExternNames"


def main():
    check_mode = '--check' in sys.argv

    content = ABI_RS.read_text()
    names = extract_names(content)

    new_block = (
        f"{MARKER_START}\n"
        f"private def headerExternNames : Array String := #[\n"
        f"{format_lean_array(names)}\n"
        f"]\n"
        f"{MARKER_END}"
    )

    lean_src = EMIT_LEAN.read_text()

    start_idx = lean_src.find(MARKER_START)
    end_idx   = lean_src.find(MARKER_END)

    if start_idx == -1 or end_idx == -1:
        print(f"ERROR: markers not found in {EMIT_LEAN}", file=sys.stderr)
        print(f"  Expected: {MARKER_START!r} ... {MARKER_END!r}", file=sys.stderr)
        sys.exit(1)

    end_idx += len(MARKER_END)
    current_block = lean_src[start_idx:end_idx]

    if current_block == new_block:
        print("headerExternNames is up to date.")
        return

    if check_mode:
        print("ERROR: headerExternNames is out of date. Run gen_abi_names.py to regenerate.", file=sys.stderr)
        sys.exit(1)

    updated = lean_src[:start_idx] + new_block + lean_src[end_idx:]
    EMIT_LEAN.write_text(updated)
    print(f"Updated {EMIT_LEAN} with {len(names)} names.")


if __name__ == "__main__":
    main()

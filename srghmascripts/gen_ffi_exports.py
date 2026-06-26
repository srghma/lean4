#!/usr/bin/env python3
"""
gen_ffi_exports.py
==================
Transforms lean_runtime source files to the ffi_exports.rs shim pattern.

For every function annotated with:
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
OR  #[no_mangle]

this script:
  1. Removes the no_mangle attribute line.
  2. Adds #[inline] before the function.
  3. Changes `pub unsafe extern "C" fn` -> `pub(crate) unsafe fn`
     and `pub extern "C" fn` -> `pub(crate) fn`
  4. Emits a thin #[no_mangle] shim in ffi_exports.rs.

Usage:
  python3 srghmascripts/gen_ffi_exports.py [--dry-run] [--pilot]
"""

import re
import sys
from pathlib import Path
from typing import Optional

# Read from temporary origin-rust-rewrite-src directory containing original files
SRC_DIR = Path(__file__).parent.parent / "origin-rust-rewrite-src"
# Write to the local lean_runtime source directory
OUTPUT_FILE = Path(__file__).parent.parent / "src/rust/lean_runtime/src/ffi_exports.rs"

PILOT_FUNCTIONS = {
    "lean_box", "lean_unbox", "lean_is_scalar", "lean_box_uint64", "lean_box_usize"
}

# ── parameter parsing ────────────────────────────────────────────────────────

def split_by_comma_top(s: str) -> list[str]:
    """Split string by commas at depth 0 (respects <>, (), [], {})."""
    parts, depth, cur = [], 0, []
    openers = set('(<[{')
    closers = set(')>]}')
    for ch in s:
        if ch in openers:
            depth += 1; cur.append(ch)
        elif ch in closers:
            depth -= 1; cur.append(ch)
        elif ch == ',' and depth == 0:
            parts.append(''.join(cur).strip()); cur = []
        else:
            cur.append(ch)
    last = ''.join(cur).strip()
    if last:
        parts.append(last)
    return parts

def extract_param_names(params_str: str) -> list[str]:
    """Extract parameter names from a Rust parameter list string."""
    names = []
    for i, param in enumerate(split_by_comma_top(params_str)):
        param = param.strip()
        if not param or param == '...':
            continue
        if ':' in param:
            name_part = param.split(':', 1)[0].strip()
            # Strip leading mut / ref / & / &mut
            name_part = re.sub(r'^(mut\s+|ref\s+|&\s*(mut\s+)?)', '', name_part).strip()
            if name_part.startswith(('(', '{')):
                names.append(f'_p{i}')
            elif name_part.startswith('_') or name_part.isidentifier():
                names.append(name_part)
            else:
                names.append(f'_p{i}')
        # else: self-like, skip
    return names

# ── function signature parsing ───────────────────────────────────────────────

# Regex for a function opening line. We handle multi-line by joining.
FN_RE = re.compile(
    r'(pub(?:\(\s*crate\s*\)|\([^)]+\))?)\s+'
    r'(unsafe\s+)?'
    r'(extern\s+"C"\s+)?'
    r'fn\s+(\w+)'
    r'(?:<[^>]*>)?\s*'     # optional generics (simplified)
    r'\('
)

def parse_fn_at(lines: list[str], start: int) -> Optional[dict]:
    """
    Parse the function signature that begins at or near `start`.
    Returns a dict or None.
    """
    # Collect lines until we see a `{` (function body start)
    collected = []
    i = start
    while i < len(lines):
        collected.append(lines[i])
        joined = ' '.join(l.strip() for l in collected)
        if '{' in joined:
            break
        i += 1
        if i - start > 20:  # safety bail-out
            break

    joined = ' '.join(l.strip() for l in collected)
    joined = re.sub(r'\s+', ' ', joined)

    m = FN_RE.search(joined)
    if not m:
        return None

    is_unsafe = bool(m.group(2))
    fn_name = m.group(4)

    # Extract everything between the opening ( and the closing ) before ->
    after_open = joined[m.end():]  # after the '('
    # Find matching closing paren
    depth = 1
    pos = 0
    for pos, ch in enumerate(after_open):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                break
    params_str = after_open[:pos].strip()
    rest_after_params = after_open[pos+1:].strip()  # -> RetType {

    # Extract return type
    return_type = ''
    ret_match = re.match(r'->\s*([^{]+?)\s*\{', rest_after_params)
    if ret_match:
        return_type = ret_match.group(1).strip()

    return {
        'name': fn_name,
        'params_str': params_str,
        'return_type': return_type,
        'is_unsafe': is_unsafe,
        'n_lines': len(collected),
    }

# ── attribute detection ──────────────────────────────────────────────────────

NO_MANGLE_PATTERNS = [
    '#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]',
    '#[no_mangle]',
]

def is_no_mangle_line(line: str) -> bool:
    stripped = line.strip()
    for pat in NO_MANGLE_PATTERNS:
        if stripped == pat:
            return True
    # multi-line cfg_attr
    if stripped.startswith('#[cfg_attr(') and 'no_mangle' in stripped:
        return True
    return False

# ── source file transformation ───────────────────────────────────────────────

def compute_call_prefix(filepath: Path, glob_imported: set) -> str:
    """Compute the crate:: path prefix used when calling this module's fns."""
    stem = filepath.stem
    if stem == 'lib':
        return 'crate::'
        
    content = filepath.read_text()
    if f'mod {stem}_impl' in content:
        return f'crate::{stem}::{stem}_impl::'
        
    return f'crate::{stem}::'

def count_braces(line: str) -> int:
    # Remove string literals and comments to avoid false brace counts
    line = re.sub(r'//.*$', '', line)
    line = re.sub(r'"[^"\\]*(?:\\.[^"\\]*)*"', '', line)
    line = re.sub(r"'[^'\\]*(?:\\.[^'\\]*)*'", '', line)
    return line.count('{') - line.count('}')

def transform_file(
    filepath: Path,
    glob_imported: set,
    dry_run: bool,
    pilot_only: bool,
    shim_entries: list,
) -> bool:
    call_prefix = compute_call_prefix(filepath, glob_imported)
    text = filepath.read_text()
    lines = text.splitlines(keepends=True)
    out = []
    i = 0
    changed = False

    brace_depth = 0
    mod_stack = []  # stack of (start_brace_depth, cfg_attribute)
    last_cfg = None

    while i < len(lines):
        line = lines[i]

        # Track cfg attributes at any time
        cfg_match = re.match(r'^\s*#\[cfg\((.+)\)\]\s*$', line)
        if cfg_match:
            last_cfg = cfg_match.group(1)
        elif line.strip() and not line.strip().startswith('//'):
            if not line.strip().startswith('#['):
                if not re.search(r'\bmod\s+\w+\b', line):
                    last_cfg = None

        net_braces = count_braces(line)
        new_brace_depth = brace_depth + net_braces

        # If we see a mod definition, push it to mod_stack
        if re.search(r'\bmod\s+\w+\b', line):
            target_depth = max(brace_depth, new_brace_depth)
            mod_stack.append((target_depth, last_cfg))
            last_cfg = None

        # Pop from mod_stack as brace depth decreases
        while mod_stack and mod_stack[-1][0] > new_brace_depth:
            mod_stack.pop()

        if is_no_mangle_line(line):
            attr_idx = i
            attr_indent = re.match(r'(\s*)', line).group(1)

            j = attr_idx + 1
            while j < len(lines) and lines[j].strip().startswith('#[') and not lines[j].strip().startswith('#[cfg_attr') and not lines[j].strip() == '#[no_mangle]':
                j += 1

            fn_start = j
            sig = parse_fn_at(lines, fn_start)

            if sig is None:
                brace_depth = new_brace_depth
                if brace_depth <= 0:
                    brace_depth = 0
                    mod_stack = []
                out.append(line)
                i += 1
                continue

            if pilot_only and sig['name'] not in PILOT_FUNCTIONS:
                brace_depth = new_brace_depth
                if brace_depth <= 0:
                    brace_depth = 0
                    mod_stack = []
                out.append(line)
                i += 1
                continue

            fn_name = sig['name']
            params_str = sig['params_str']
            return_type = sig['return_type']
            is_unsafe = sig['is_unsafe']
            n_sig_lines = sig['n_lines']

            fn_cfgs = []
            
            # Check lines immediately preceding the no_mangle line (up to 3 lines)
            k = attr_idx - 1
            while k >= 0 and (lines[k].strip().startswith('#[') or not lines[k].strip()):
                if lines[k].strip().startswith('#[cfg('):
                    fn_cfgs.insert(0, lines[k].strip())
                k -= 1
                
            # Check lines between no_mangle and fn_start
            k = attr_idx + 1
            while k < fn_start:
                if lines[k].strip().startswith('#[cfg('):
                    fn_cfgs.append(lines[k].strip())
                k += 1

            # Build shim
            param_names = extract_param_names(params_str)
            call_args = ', '.join(param_names)
            ret_ann = f' -> {return_type}' if return_type else ''
            unsafe_kw = 'unsafe ' if is_unsafe else ''
            call_expr = f'{call_prefix}{fn_name}({call_args})'

            shim_cfgs = []
            active_cfgs = [cfg for _, cfg in mod_stack if cfg]
            if len(active_cfgs) > 1:
                shim_cfgs.append(f"#[cfg(all({', '.join(active_cfgs)}))]")
            elif len(active_cfgs) == 1:
                shim_cfgs.append(f"#[cfg({active_cfgs[0]})]")

            for cfg in fn_cfgs:
                shim_cfgs.append(cfg)
                
            cfgs_block = '\n'.join(shim_cfgs) + '\n' if shim_cfgs else ''

            shim = (
                f'{cfgs_block}'
                f'#[no_mangle]\n'
                f'pub {unsafe_kw}extern "C" fn {fn_name}({params_str}){ret_ann} {{\n'
                f'    unsafe {{ {call_expr} }}\n'
                f'}}\n'
            )
            shim_entries.append((fn_name, shim))
            changed = True

            out.append(f'{attr_indent}#[inline]\n')
            i = attr_idx + 1

            while i < fn_start:
                net = count_braces(lines[i])
                new_brace_depth = brace_depth + net
                while mod_stack and mod_stack[-1][0] > new_brace_depth:
                    mod_stack.pop()
                brace_depth = new_brace_depth
                if brace_depth <= 0:
                    brace_depth = 0
                    mod_stack = []
                out.append(lines[i])
                i += 1

            sig_lines = []
            k = fn_start
            brace_found = False
            while k < len(lines) and not brace_found:
                sig_lines.append(lines[k])
                if '{' in lines[k]:
                    brace_found = True
                k += 1
                if k - fn_start > n_sig_lines + 2:
                    break

            for sl in sig_lines:
                net = count_braces(sl)
                new_brace_depth = brace_depth + net
                while mod_stack and mod_stack[-1][0] > new_brace_depth:
                    mod_stack.pop()
                brace_depth = new_brace_depth
                if brace_depth <= 0:
                    brace_depth = 0
                    mod_stack = []

            sig_text = ''.join(sig_lines)
            sig_text = re.sub(
                r'\bpub(?:\([^)]*\))?\s+(unsafe\s+)extern\s+"C"\s+fn\b',
                r'pub(crate) \1fn',
                sig_text,
            )
            sig_text = re.sub(
                r'\bpub(?:\([^)]*\))?\s+extern\s+"C"\s+fn\b',
                r'pub(crate) fn',
                sig_text,
            )
            out.append(sig_text)
            i = k
        else:
            while mod_stack and mod_stack[-1][0] > new_brace_depth:
                mod_stack.pop()
            brace_depth = new_brace_depth
            if brace_depth <= 0:
                brace_depth = 0
                mod_stack = []
            out.append(line)
            i += 1

    if changed:
        if not dry_run:
            filepath.write_text(''.join(out))
            print(f'  Modified: {filepath.name}')
        else:
            print(f'  [dry-run] Would modify: {filepath.name}')

    return changed

# ── ffi_exports.rs generation ─────────────────────────────────────────────────

def generate_ffi_exports(shim_entries: list, dry_run: bool):
    header = '''\
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

//! FFI export shims — auto-generated by srghmascripts/gen_ffi_exports.py
//!
//! Each function here is a thin #[no_mangle] C-ABI wrapper around the
//! #[inline] pub(crate) implementation in its source module.
//!
//! DO NOT add #[inline] to any function in this file.
//! DO NOT add #[cfg_attr(…, no_mangle)] in source modules; use only #[inline].

#![allow(unused_unsafe)]

use crate::*;

'''
    shim_block = '\n'.join(s for _, s in shim_entries)
    content = header + shim_block + '\n'

    if dry_run:
        print(f'\n[dry-run] Would write {OUTPUT_FILE} ({len(shim_entries)} shims)')
        lines = content.splitlines()
        print('\n'.join(lines[:40]))
        if len(lines) > 40:
            print(f'  ... ({len(lines) - 40} more lines)')
    else:
        OUTPUT_FILE.write_text(content)
        print(f'\nWrote {OUTPUT_FILE} ({len(shim_entries)} shims, {len(content)} bytes)')

# ── lib.rs: add mod ffi_exports ──────────────────────────────────────────────

def add_ffi_exports_mod(lib_rs: Path, dry_run: bool):
    pass

# ── entry point ───────────────────────────────────────────────────────────────

def build_glob_imported(lib_rs: Path) -> set:
    text = lib_rs.read_text()
    result = set()
    for m in re.finditer(r'pub\(crate\)\s+use\s+(\w+)::\*;', text):
        result.add(m.group(1))
    return result

def main():
    dry_run = '--dry-run' in sys.argv
    pilot_only = '--pilot' in sys.argv

    # Read glob imported from original lib.rs in SRC_DIR
    lib_rs = SRC_DIR / 'lib.rs'
    glob_imported = build_glob_imported(lib_rs)

    src_files = sorted(SRC_DIR.glob('*.rs'))
    ordered = (
        [lib_rs]
        + [f for f in src_files if f.name not in ('lib.rs', 'ffi_exports.rs')]
    )

    shim_entries: list[tuple[str, str]] = []
    total_modified = 0

    for filepath in ordered:
        was_modified = transform_file(
            filepath, glob_imported,
            dry_run=dry_run, pilot_only=pilot_only,
            shim_entries=shim_entries,
        )
        if was_modified:
            total_modified += 1

    print(f'\nProcessed {len(ordered)} files, {total_modified} modified')
    print(f'Collected {len(shim_entries)} shims')

    generate_ffi_exports(shim_entries, dry_run)

if __name__ == '__main__':
    main()

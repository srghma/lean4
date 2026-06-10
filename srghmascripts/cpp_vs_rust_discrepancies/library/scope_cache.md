# Comparison: scope_cache

## Files

- C++ Header: `library/scope_cache.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

A templated C++ data structure (`scope_cache`) designed to cache computation results that depend on the current scope (e.g., local contexts in type checking). It used generations and nested mappings to effectively reuse cached results across compatible scopes without excessive copying.

## Corresponding Rust Implementation

There is no direct mapping to `scope_cache` in the `lean_runtime` Rust codebase. Logic regarding scoping, environments, and caching has moved into Lean itself in Lean 4. The C++ kernel has been entirely removed, so these highly specific C++ templated structures are obsolete.

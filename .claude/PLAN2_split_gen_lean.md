**Proposal**
Split into **8 generated implementation crates + 1 facade crate**.

Current measured size: `src/rust/gen_lean/src/gen/Lean` is about **12.48M lines** across **1189 files**.

Recommended split:

| Crate | Contents | Approx lines |
|---|---|---:|
| `gen_lean_base` | Lean core modules, `Data`, `Parser`, `PrettyPrinter`, `Util`, `Widget`, `LibrarySuggestions`, misc non-`Meta`/`Elab`/`Compiler`/`Server`/`Linter` | 1.96M |
| `gen_lean_meta` | `Lean.Meta` excluding `Meta.Tactic` | 1.61M |
| `gen_lean_meta_tactic` | `Lean.Meta.Tactic` excluding `Grind` | 1.42M |
| `gen_lean_meta_grind` | `Lean.Meta.Tactic.Grind` | 1.56M |
| `gen_lean_compiler` | `Lean.Compiler` | 1.01M |
| `gen_lean_elab_frontend` | large core `Lean.Elab` frontend modules: `PreDefinition`, `Term`, `App`, `Structure`, `Command`, `Declaration`, etc. | 1.74M |
| `gen_lean_elab_support` | support-ish `Lean.Elab` modules: `DocString`, `Deriving`, `Do`, `ConfigEval`, `BuiltinDo`, etc. | 1.05M |
| `gen_lean_elab_tactic` | `Lean.Elab.Tactic` plus small late modules `Server` + `Linter` | 2.12M |
| `gen_lean` | facade only; joins/re-exports all above under the same public paths | tiny |

This is not perfectly equal, but it respects likely Lean import layering better than pure LOC partitioning. The biggest crate is ~2.1M lines instead of the current 12.5M-line monolith.

**Why This Split**
- `Meta.Tactic.Grind` is huge by itself: ~1.56M lines.
- `Meta.Tactic` without `Grind` is still ~1.42M lines.
- `Elab.Tactic` is ~1.46M lines and naturally belongs late in the dependency order.
- `Compiler` is smaller, but it likely depends on `Meta`, so keeping it separate avoids cycles.
- `Server` and `Linter` are small and late; putting them with `Elab.Tactic` keeps crate count reasonable.

**Dependency Shape**
Target DAG:

```text
gen_init, gen_std, gen_lean_ffi
        ↓
gen_lean_base
        ↓
gen_lean_meta
        ↓
gen_lean_meta_tactic
        ↓
gen_lean_meta_grind
        ↓
gen_lean_compiler
        ↓
gen_lean_elab_frontend / gen_lean_elab_support
        ↓
gen_lean_elab_tactic
        ↓
gen_lean facade
```

Before implementing, the generator should verify actual `use crate::r#gen::Lean::...` references and reject any bucket assignment that creates a backward dependency cycle.

**How `gen_lean` Should Join Them**
Keep the existing public API stable:

```rust
pub mod r#gen {
    pub use gen_init::r#gen::Init;
    pub use gen_std::r#gen::Std;

    pub mod Lean {
        pub use gen_lean_base::r#gen::Lean::*;
        pub use gen_lean_meta::r#gen::Lean::*;
        pub use gen_lean_meta_tactic::r#gen::Lean::*;
        pub use gen_lean_meta_grind::r#gen::Lean::*;
        pub use gen_lean_compiler::r#gen::Lean::*;
        pub use gen_lean_elab_frontend::r#gen::Lean::*;
        pub use gen_lean_elab_support::r#gen::Lean::*;
        pub use gen_lean_elab_tactic::r#gen::Lean::*;
    }
}
```

Each implementation crate also needs its own full visible `crate::r#gen` namespace, because generated files currently use paths like:

```rust
use crate::r#gen::Lean::Meta::...
```

So each leaf crate’s generated `gen.rs` should re-export dependency crates into its local `crate::r#gen::Lean`, then declare its own modules.

**Implementation Plan**
1. Teach `srghmascripts/regenerate_module_tree.ts` bucket assignment.
2. Generate one crate per bucket with its own `Cargo.toml`, `src/lib.rs`, and `src/gen.rs`.
3. Keep generated Rust source files bucket-local, not manually moved.
4. For every bucket, generate dependency re-exports first, then local modules.
5. Make `gen_lean` a facade crate only.
6. Add all new crates to `src/rust/Cargo.toml`.
7. Run `cargo check -p gen_lean` and fix bucket cycles by moving offending modules later/earlier.

**Main Risk**
The split must follow generated Lean import order, not only directory names. If `Elab.Support` imports `Elab.Frontend` or vice versa in unexpected ways, those two may need merging or rebalancing. The generator should compute cross-bucket imports from generated `use crate::r#gen::Lean::...` lines and print cycles.


----------

Implemented the analyzer:

- [`analyze_gen_lean_import_split.ts`](/home/srghma/projects/lean4/srghmascripts/analyze_gen_lean_import_split.ts)
- Output written to [`import-split-analysis.md`](/home/srghma/projects/lean4/src/rust/gen_lean/import-split-analysis.md)

Result:
- `src/Lean/**/*.lean`: `1,189` modules
- Module import SCCs: `0 cyclic`
- So splitting is possible.
- Directory-level grouping creates cycles only because some directories are too coarse.
- Recursive directory refinement reduces the big cycle to one small required merge:
  - `Lean.Meta.MethodSpecs + Lean.Meta.Tactic.Simp`
  - ~`522k` generated Rust LOC

**Proposal**
Use recursive directory refinement, not topo ranges:

1. Keep directory structure as the primary unit.
2. Treat umbrella/index modules like `Lean.Meta.lean`, `Lean.Elab.lean`, `Lean.Compiler.LCNF.lean` as late `.__index` atoms/facades.
3. Split only directories that participate in oversized cycles.
4. Allow individual-file atoms only where directory grouping creates Cargo cycles.
5. Merge only the one remaining cycle:
   - `Lean.Meta.MethodSpecs`
   - `Lean.Meta.Tactic.Simp`

Practical first crate layout:

- `gen_lean_data`
  - `Lean.Data.*`
  - includes `Lean.Data.Lsp` as a large subdir but still directory-safe

- `gen_lean_parser`
  - `Lean.Parser.*`
  - parser index modules as late local facades

- `gen_lean_pretty_printer`
  - `Lean.PrettyPrinter.*`

- `gen_lean_compiler_ir`
  - `Lean.Compiler.IR`

- `gen_lean_compiler_lcnf`
  - `Lean.Compiler.LCNF`
  - biggest compiler atom: ~`819k` generated Rust LOC

- `gen_lean_meta_core`
  - refined `Lean.Meta.*` atoms excluding tactic/grind/sym-heavy dirs

- `gen_lean_meta_sym`
  - `Lean.Meta.Sym.*`

- `gen_lean_meta_tactic_simp`
  - `Lean.Meta.Tactic.Simp`
  - plus `Lean.Meta.MethodSpecs`

- `gen_lean_meta_tactic_grind`
  - `Lean.Meta.Tactic.Grind`
  - biggest atom: ~`1.53M` generated Rust LOC

- `gen_lean_meta_tactic_other`
  - remaining `Lean.Meta.Tactic.*`
  - includes `BVDecide`, `Cbv`, `FunInd`, etc.

- `gen_lean_elab_core`
  - refined `Lean.Elab.*` non-tactic modules

- `gen_lean_elab_tactic`
  - `Lean.Elab.Tactic.*`
  - keep large subdirs like `Do`, `Grind`, `Omega` intact unless check time remains too high

- `gen_lean_server_linter`
  - `Lean.Server.*`
  - `Lean.Linter.*`

- `gen_lean_facade`
  - old `gen_lean` name
  - re-exports all split crates
  - contains generated `.__index` umbrella modules that only aggregate/re-export where needed

This is semi-topological: directory-shaped crates first, import graph only decides ordering and required merges.

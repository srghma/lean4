Now I have a thorough picture of nanoda's design. Let me explain it clearly.
──────
##  still-nanoda  vs. the Lean Runtime — Architecture Explained

### What nanoda actually is

It's a kernel type-checker, not a runtime. Its job is: read an export file ( .olean ), verify that every declaration is well-typed, then exit. It is a verification tool, not an execution engine.
──────
### The core design choice: indices instead of pointers, no refcounting

Look at util.rs:

  pub struct Ptr<A> {
      raw: u32,   // bit 31 = which DAG, bits 0-30 = index
      ph: PhantomData<A>,
  }

Every  ExprPtr ,  NamePtr ,  LevelPtr  is a 32-bit integer index into one of two append-only  IndexSet s (called DAGs):
•  ExportFile.dag  — persistent, lives the entire run
•  TcCtx.dag  — temporary, lives only during one declaration's check

No heap pointers. No reference counts. No  Arc / Rc . No  Drop  impls on values.
This works because:

1. The DAGs are append-only — entries are never removed, indices never become invalid.
2. The entire program exits when done — any live memory is just reclaimed by the OS.
3. Expressions are interned (hash-consed): equal expressions share the same index. No duplicate allocations, ever.
──────
### Why this is unsuitable for the Lean runtime
The runtime is fundamentally different:

                                                                            | nanoda (checker)                                                          | Lean runtime
---------------------------------------------------------------------------|---------------------------------------------------------------------------|--------------------------------------------------------------------------
  Lifetime                                                                  | Parse → check → exit                                                      | Long-lived process, persistent heap
  Memory                                                                    | Two static DAGs + leak                                                    | Dynamic allocation per  LeanObject
  Sharing                                                                   | Index equality = structural equality                                      | RC to track live references
  Threads                                                                   | Single-threaded                                                           | Multi-threaded (task system)
  GC model                                                                  | None (bulk-free on exit)                                                  | Reference counting
  Values                                                                    | Immutable kernel AST                                                      | Mutable runtime objects (e.g.  IORef )

The moment you have an object that can be:

• shared across multiple owners (e.g. a  List  node referenced by two closures)
• dropped at unpredictable times (when the last reference disappears)
• mutated (IORef, array update-in-place)

…you need per-object lifetime tracking. That's what RC gives you. The "exit and let the OS clean up" trick is gone.
──────
### What ideas CAN be borrowed from nanoda

Despite the fundamental difference, there are several concrete techniques worth understanding:

#### 1. Index-based interning (hash-consing)

nanoda's  ExprIndexSet  /  LeanDag  are a textbook implementation of hash-consing. The idea: if two expressions are structurally equal, they get the same index, so structural equality becomes  u32 == u32 . The runtime already
does this for some things (like universe level caching), but nanoda's two-level DAG (persistent + temporary) is an elegant pattern for scoped interning.

#### 2. The two-DAG split (ExportFile vs TcCtx)

The  DagMarker  bit encodes which arena an index lives in using a single bit in the pointer. This is a clean way to distinguish long-lived vs. short-lived allocations without a separate allocator or generational GC. The
runtime
could apply this idea to distinguish "module-loaded definitions" from "per-call temporaries."

#### 3. Local-first cache lookup

See util.rs and the README's "5% + 10% speedup" in mathlib. The insight: check the temporary (local) DAG before the persistent (global) one, because during type-checking most new expressions reference recently-created
locals. The runtime's elaboration cache could apply the same locality heuristic.

#### 4. Baked-in hash fields on every node

Every  Expr  variant carries a precomputed  hash: u64 . Structural hash on a tree node = O(1) because children's hashes were already computed at allocation time. The runtime's  LeanObject  uses a different scheme, but this
pattern is worth knowing — especially if the runtime ever needs fast hash-consing of LCNF expressions.

#### 5.  Copy  + value semantics for small AST nodes

All nanoda  Expr ,  Level ,  Name  are  #[derive(Copy, Clone)] . They're tiny enum values (a few words), so copying them is cheaper than chasing a pointer. The runtime can't do this for arbitrary user values, but for fixed
compiler-internal AST nodes (like LCNF), this is a valid design.
──────
### Summary

nanoda's lack of RC isn't a limitation — it's a deliberate fit to its use case (one-shot verification). The runtime needs RC because it manages a general-purpose heap with unpredictable sharing and object lifetimes.

The exportable ideas are architectural patterns: index-based interning, arena-tagged pointers, local-first cache ordering, and precomputed hashes — none of which require RC and all of which are independently applicable to the
runtime's internal structures (especially the compiler pipeline, not the user heap).

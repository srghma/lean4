# EmitEs6 Implementation

The ES6 emitter is implemented in `src/Lean/Compiler/LCNF/EmitEs6.lean`. It translates Lean Compiler Normal Form (LCNF) code from the **Impure** phase into JavaScript (ES6) source code.

## Design

The emitter uses a `ReaderT Context $ StateRefT State CompilerM` stack to manage:
- **`out`**: The generated JavaScript string.
- **`funMangleCache`**: A cache for mangled function names.
- **`indent`**: The current indentation level for formatted output.

## Core Functions

- **`emitCode`**: Recursively traverses LCNF `Code` objects, translating `let` bindings to `const`, `cases` to `switch`, and `jp` to arrow functions.
- **`emitLetValue`**: Translates LCNF `LetValue` (e.g., constant applications, projections, boxing) into JS expressions.
- **`toJsName`**: Mangels Lean names into valid JS identifiers using `Name.mangle`.

## Usage Example

```lean
import Lean.Compiler.LCNF.EmitEs6

open Lean.Compiler.LCNF

def compileToJs (decl : Decl) : CompilerM String :=
  EmitEs6.main #[decl]
```

## Status

Currently supports basic arithmetic, string operations, branch logic (cases), and join points. Complex Lean features like closures are already handled by the LCNF pipeline before reaching this emitter.

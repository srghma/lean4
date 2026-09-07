# EmitEs6 Implementation

The ES6 emitter is implemented in `src/Lean/Compiler/LCNF/EmitEs6.lean`. It translates Lean Compiler Normal Form (LCNF) code from the **Impure** phase into JavaScript (ES6) source code.

## Design

The emitter uses a `ReaderT Context $ StateRefT State CompilerM` stack to manage:
- **`out`**: The generated JavaScript string.
- **`funMangleCache`**: A cache for mangled function names.
- **`indent`**: The current indentation level for formatted output.

## Core Features

### Primitive Inlining
Standard operations like `Nat.add`, `Nat.mul`, `Nat.beq`, etc., are inlined into native JavaScript operators (`+`, `*`, `===`).

### Data Structures
- **Sum Types**: Represented as JavaScript objects with a `tag` field and numbered fields for arguments (e.g., `{ tag: "SumType_L", _1: n }`).
- **Newtypes/Structures**: Represented identically to sum types for simplicity, though they may be optimized in the future.
- **Booleans**: Mapped to native JavaScript `true` and `false`.

### Boxing and Unboxing
In JavaScript, boxing and unboxing are treated as identity operations since JavaScript is dynamically typed and handles numbers and objects uniformly.

### Control Flow
- **`let` bindings**: Translated to `const` statements.
- **`cases`**: Translated to `if / else if` chains checking the `.tag` property of objects (or direct value for Booleans).
- **`jp` (Join Points)**: Translated to arrow functions to avoid code duplication and handle complex control flow without native `goto`.

## CI Testing
GitHub CI has been updated to support `_es6.lean` test files. These files are compiled using `lean -j ...` and compared against `.js.expected` snapshots. C++ testing is currently disabled to prioritize JS backend development.

## Usage Example

```bash
lean -j output.js my_file_es6.lean
```

<details>
  <summary>test-app_unexpander.lean</summary>

```lean
import Lean

open Lean PrettyPrinter

-- 1. Define a standard Lean function
def double (n : Nat) : Nat := n + n

-- 2. Define custom syntax for it: dbl(x)
syntax "dbl(" term ")" : term

-- 3. Tell Lean how to EXPAND the syntax into code (Parser/Macro)
macro_rules
  | `(dbl($x)) => `(double $x)

-------------------------------------------------------------
-- SCENARIO 1: WITHOUT app_unexpander
-------------------------------------------------------------

-- Lean understands `dbl(5)`, but when pretty-printing the result,
-- it prints the raw function `double 5`.
#check dbl(5)
-- OUTPUT: double 5 : Nat  <-- Notice `dbl(...)` is gone!

-------------------------------------------------------------
-- SCENARIO 2: WITH app_unexpander
-------------------------------------------------------------

-- Now we tell Lean: "Whenever you see `double x` in AST form,
-- pretty-print it back as `dbl(x)`."
@[app_unexpander double]
def unexpDouble : Unexpander
  | `($_ $x) => `(dbl($x))  -- `$_` matches the function `double`, `$x` matches its argument
  | _ => throw ()

-- Now test it again:
#check dbl(5)
-- OUTPUT: dbl(5) : Nat    <-- Custom syntax is preserved!

#check double 5
-- OUTPUT: dbl(5) : Nat    <-- Even raw function calls get pretty-printed

```

</details>



<details>
  <summary>test-app_delab.lean</summary>

```lean
import Lean

open Lean PrettyPrinter Delaborator SubExpr

-- 1. Define a function with an implicit argument `{α : Type}`
def Box.mk {α : Type} (val : α) : α := val

-- 2. Define custom notation syntax: 📦(x)
syntax "📦(" term ")" : term
macro_rules
  | `(📦($x)) => `(Box.mk $x)


-------------------------------------------------------------
-- SCENARIO 1: WITHOUT app_delab
-------------------------------------------------------------

-- Lean can parse `📦(42)`, but prints it back as `Box.mk 42`
#check 📦(42)
-- OUTPUT: Box.mk 42 : Nat


-------------------------------------------------------------
-- SCENARIO 2: WITH app_delab
-------------------------------------------------------------

@[app_delab Box.mk]
def delabBoxMk : Delab := do
  -- GUARD 1: If the user turned on `pp.explicit`, do NOT use custom notation!
  if ← getPPOption getPPExplicit then failure

  -- GUARD 2: Extract the AST expression `Box.mk {α} val`
  let e ← getExpr
  let_expr Box.mk α val := e | failure

  -- GUARD 3: Only use box notation if the type `α` is `Nat`!
  if !α.isConstOf ``Nat then failure

  -- RECURSION: Delaborate the child expression `val` into syntax
  let valSyntax ← delab val

  -- RECONSTRUCT: Return custom syntax `📦(...)`
  `(📦($valSyntax))


-------------------------------------------------------------
-- TESTING THE BEHAVIOR
-------------------------------------------------------------

-- Test A: Type is `Nat` -> Uses custom syntax 📦(...)
#check Box.mk 42
-- OUTPUT: 📦(42) : Nat

-- Test B: Type is `String` -> Guard 3 triggers `failure`, falls back to default!
#check Box.mk "hello"
-- OUTPUT: Box.mk "hello" : String

-- Test C: User enabled `pp.explicit` -> Guard 1 triggers `failure`!
set_option pp.explicit true in
#check Box.mk 42
-- OUTPUT: @Box.mk Nat 42 : Nat
```

</details>


<details>
  <summary>test-app_unexpander.lean</summary>

```lean
```

</details>

<details>
  <summary>test-app_unexpander.lean</summary>

```lean
```

</details>

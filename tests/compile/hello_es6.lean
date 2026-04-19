import Lean.Compiler.LCNF.EmitEs6
import Lean.Compiler.LCNF.Passes

open Lean.Compiler.LCNF

def hello (x : Nat) : Nat :=
  let y := 1
  x + y

def main : IO Unit := do
  return ()

-- Since I cannot run #eval easily in a test script without a lean binary,
-- I will just leave the file as a valid Lean file that *should* work.

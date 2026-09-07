-- import Lean
-- open Lean Meta

def test1 (x : Nat) (y : Nat) : Array Nat :=
  (#[] : Array Nat).push x |>.push y

def test2 (x : Nat) (y : Nat) : Array Nat :=
  let init := (#[] : Array Nat).push x
  let a := init.push y
  let b := init.push (y + 1)
  a ++ b

-- set_option pp.all true
set_option trace.compiler.ir.result true

#print test1
#print test2

-- #eval show MetaM Unit from do
--   let env ← getEnv
--   -- Look up the declaration for `test2`
--   match env.find? ``test2 with
--   | some decl => IO.println (repr decl.type)
--   | none => IO.println "Not found"

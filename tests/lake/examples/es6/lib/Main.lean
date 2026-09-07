import FFI

def main : IO Unit := do
  IO.println "EXECUTING lib.Main.lean"
  IO.println <| myAdd 1 2
  IO.println (← myLeanFun)
  IO.println "EXECUTING lib.Main.lean ENDED"

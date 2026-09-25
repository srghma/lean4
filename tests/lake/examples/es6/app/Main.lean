import FFI

def main : IO Unit := do
  IO.println "EXECUTING app.Main.lean"
  IO.println <| myAdd 1 2
  IO.println "EXECUTING app.Main.lean ENDED"

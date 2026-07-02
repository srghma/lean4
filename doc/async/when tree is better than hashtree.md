import Std.Data.HashSet
import Std.Data.TreeSet

-- Settings: Large keys, but relatively small N
def n : Nat := 500
def stringSize : Nat := 20000
def iterations : Nat := 10

-- Generate long strings that are identical except for the very last characters
def generateLongStrings (count : Nat) : Array String := Id.run do
  let mut arr := #[]
  let base := String.ofList (List.replicate stringSize 'a')
  for i in [0:count] do
    -- Append the index to the end so the hash function MUST read the whole string
    arr := arr.push (base ++ toString i)
  return arr

def getTimeNanos : IO Nat := do
  return (← IO.monoNanosNow)

def benchHashSet (keys : Array String) : IO Nat := do
  let start ← getTimeNanos
  for _ in [0:iterations] do
    let mut s : Std.HashSet String := {}
    for k in keys do
      s := s.insert k
    for k in keys do
      if !s.contains k then
        IO.println "Error"
  let finish ← getTimeNanos
  pure (finish - start)

def benchTreeSet (keys : Array String) : IO Nat := do
  let start ← getTimeNanos
  for _ in [0:iterations] do
    let mut s : Std.TreeSet String := {}
    for k in keys do
      s := s.insert k
    for k in keys do
      if !s.contains k then
        IO.println "Error"
  let finish ← getTimeNanos
  pure (finish - start)

def main : IO Unit := do
  IO.println "Generating long string keys..."
  let keys := generateLongStrings n

  IO.println s!"Starting benchmark: N={n}, KeySize={stringSize} chars"

  let tHash ← benchHashSet keys
  IO.println s!"Hash Set: {tHash / 1000000}ms"

  let tTree ← benchTreeSet keys
  IO.println s!"Tree Set: {tTree / 1000000}ms"

  if tTree < tHash then
    IO.println s!"SUCCESS: Tree Set was {(tHash.toFloat / tTree.toFloat).toString}x faster than Hash Set"
  else
    IO.println "Hash Set still won. Increase stringSize or decrease N."

#eval main

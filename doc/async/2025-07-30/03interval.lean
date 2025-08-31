import Std.Time
import Std.Internal.Async
import Std.Internal.UV.Timer

open Std.Internal.IO.Async

def main : IO Unit := do
  -- Record start time
  let start ← IO.monoMsNow

  -- Create an interval that ticks every 1000 ms (1s).
  let interval ← Interval.mk (⟨1000⟩ : Std.Time.Millisecond.Offset)

  let rec loop (n : Nat) : IO Unit := do
    if n <= 0 then
      IO.println "Stopping interval"
      interval.stop
    else
      -- Wait until the next tick
      let tickTask ← interval.tick
      tickTask.block   -- wait for tick to complete

      let now ← IO.monoMsNow
      let elapsed := now - start

      IO.println s!"[+{elapsed}ms] tick {n}"

      -- Example of resetting: after 3 ticks, restart the timer
      if n = 3 then
        IO.sleep 1500
        -- IO.println s!"[+{elapsed}ms] Resetting interval"
        -- interval.reset

      loop (n - 1)

  loop 5

#eval main

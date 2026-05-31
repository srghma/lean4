# with

```py
import Std.Sync.Channel
import Std.Internal.Async
import Std.Time

def logWithTime (start : Nat) (tag msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  IO.println s!"[+{elapsed}ms][{tag}] {msg}"

def loop (stepsLeft : Nat) (ch1 ch2 : Std.CloseableChannel Nat) (start : Nat)
    : IO (Std.Internal.IO.Async.AsyncTask Unit) := do
  let ch1c ← ch1.isClosed
  let ch2c ← ch2.isClosed
  logWithTime start "loop" s!"stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}"

  if stepsLeft <= 0 then
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "max steps reached, exiting loop"
    return Std.Internal.IO.Async.AsyncTask.pure .unit
  else if ch1c && ch2c then
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "both channels closed, exiting loop"
    return Std.Internal.IO.Async.AsyncTask.pure .unit
  else
    let stepsLeft' := stepsLeft - 1
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "starting select"
    Std.Internal.IO.Async.Selectable.one
      #[ .case ch1.recvSelector fun msg? => do
            logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx1 got {msg?}"
            loop stepsLeft' ch1 ch2 start
         , .case ch2.recvSelector fun msg? => do
            logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx2 got {msg?}"
            loop stepsLeft' ch1 ch2 start
      ]


def main : IO Unit := do
  let start ← IO.monoMsNow -- reference time

  let ch1 ← Std.CloseableChannel.new (some 10)
  let ch2 ← Std.CloseableChannel.new (some 10)

  let t1 : Std.Internal.IO.Async.Async Unit := do
    let send (n: Nat) := do logWithTime start "t1" s!"waiting 100 before sending {n}"; IO.sleep 100; logWithTime start "t1" s!"sending {n}"; ch1.sync.send n
    logWithTime start "t1" "sending 1"; ch1.sync.send 1
    send 2
    logWithTime start "t1" "waiting 100 before closing channel"; IO.sleep 100; logWithTime start "t1" "closing channel"; ch1.close
    logWithTime start "t1" "closed"

  let t2 : Std.Internal.IO.Async.Async Unit := do
    let send (n: Nat) := do logWithTime start "t2" s!"waiting 100 before sending {n}"; IO.sleep 100; logWithTime start "t2" s!"sending {n}"; ch2.sync.send n
    logWithTime start "t2" "sending 10"; ch2.sync.send 10
    send 20
    send 30
    send 40
    send 50
    logWithTime start "t2" "waiting 100 before closing channel"; IO.sleep 100; logWithTime start "t2" "closing channel"; ch2.close
    logWithTime start "t2" "closed"

  logWithTime start "main" "runTask1"
  let t1' ← t1.asTask
  logWithTime start "main" "runTask1 started"

  logWithTime start "main" "runTask2"
  let t2' ← t2.asTask
  logWithTime start "main" "runTask2 started"

  logWithTime start "main" "loop start"
  let t3 ← loop 300 ch1 ch2 start
  logWithTime start "main" "loop created"
  let n ← t3.block
  logWithTime start "main" s!"loop finished, received {n}"
  t1'.block
  logWithTime start "main" "t1 finished"
  t2'.block
  logWithTime start "main" "t2 finished"
```

I get

```bash
[+0ms][main] runTask1
[+1ms][main] runTask1 started
[+1ms][main] runTask2
[+1ms][main] runTask2 started
[+1ms][main] loop start
[+1ms][loop] stepsLeft=300, ch1c=false, ch2c=false
[+1ms][loop stepsLeft=300, ch1c=false, ch2c=false] starting select
[+1ms][main] loop created
[+1ms][t2] sending 10
[+1ms][t1] sending 1
[+1ms][t2] waiting 100 before sending 20
[+1ms][t1] waiting 100 before sending 2
[+2ms][loop stepsLeft=300, ch1c=false, ch2c=false] rx2 got (some 10)
[+2ms][loop] stepsLeft=299, ch1c=false, ch2c=false
[+2ms][loop stepsLeft=299, ch1c=false, ch2c=false] starting select
[+2ms][loop stepsLeft=299, ch1c=false, ch2c=false] rx1 got (some 1)
[+2ms][loop] stepsLeft=298, ch1c=false, ch2c=false
[+2ms][loop stepsLeft=298, ch1c=false, ch2c=false] starting select
[+101ms][t2] sending 20
[+102ms][t1] sending 2
[+102ms][t2] waiting 100 before sending 30
[+102ms][t1] waiting 100 before closing channel
[+102ms][loop stepsLeft=298, ch1c=false, ch2c=false] rx2 got (some 20)
[+102ms][loop] stepsLeft=297, ch1c=false, ch2c=false
[+102ms][loop stepsLeft=297, ch1c=false, ch2c=false] starting select
[+102ms][loop stepsLeft=297, ch1c=false, ch2c=false] rx1 got (some 2)
[+102ms][loop] stepsLeft=296, ch1c=false, ch2c=false
[+102ms][loop stepsLeft=296, ch1c=false, ch2c=false] starting select
[+202ms][t2] sending 30
[+202ms][t2] waiting 100 before sending 40
[+202ms][t1] closing channel
[+202ms][t1] closed
[+202ms][loop stepsLeft=296, ch1c=false, ch2c=false] rx1 got none
[+202ms][loop] stepsLeft=295, ch1c=true, ch2c=false
[+202ms][loop stepsLeft=295, ch1c=true, ch2c=false] starting select
[+202ms][loop stepsLeft=295, ch1c=true, ch2c=false] rx2 got (some 30)
[+202ms][loop] stepsLeft=294, ch1c=true, ch2c=false
[+202ms][loop stepsLeft=294, ch1c=true, ch2c=false] starting select
[+202ms][loop stepsLeft=294, ch1c=true, ch2c=false] rx1 got none
[+202ms][loop] stepsLeft=293, ch1c=true, ch2c=false
....
[+212ms][loop stepsLeft=1, ch1c=true, ch2c=false] starting select
[+212ms][loop stepsLeft=1, ch1c=true, ch2c=false] rx1 got none
[+212ms][loop] stepsLeft=0, ch1c=true, ch2c=false
[+212ms][loop stepsLeft=0, ch1c=true, ch2c=false] max steps reached, exiting loop
[+212ms][main] loop finished, received ()
[+212ms][main] t1 finished
[+302ms][t2] sending 40
[+302ms][t2] waiting 100 before sending 50
[+403ms][t2] sending 50
[+403ms][t2] waiting 100 before closing channel
[+503ms][t2] closing channel
[+503ms][t2] closed
[+503ms][main] t2 finished
```

Summary: if I dont filter closed channels - .none's always come / the closed channel ALWAYS throws none. Thus - cycles are waisted. TODO: filter out

# with

```patch
--- a/pipes/PipesTest.lean
+++ b/pipes/PipesTest.lean
@@ -23,16 +23,19 @@ def loop (stepsLeft : Nat) (ch1 ch2 : Std.CloseableChannel Nat) (start : Nat)
    return Std.Internal.IO.Async.AsyncTask.pure .unit
  else
    let stepsLeft' := stepsLeft - 1
+    let mut cases := #[]
+    if !ch1c then
+      cases := cases.push <|
+        .case ch1.recvSelector fun msg? => do
+          logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx1 got {msg?}"
+          loop stepsLeft' ch1 ch2 start
+    if !ch2c then
+      cases := cases.push <|
+        .case ch2.recvSelector fun msg? => do
+          logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx2 got {msg?}"
+          loop stepsLeft' ch1 ch2 start
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "starting select"
-    Std.Internal.IO.Async.Selectable.one
-      #[ .case ch1.recvSelector fun msg? => do
-            logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx1 got {msg?}"
-            loop stepsLeft' ch1 ch2 start
-         , .case ch2.recvSelector fun msg? => do
-            logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx2 got {msg?}"
-            loop stepsLeft' ch1 ch2 start
-      ]
-
+    Std.Internal.IO.Async.Selectable.one cases

def main : IO Unit := do
  let start ← IO.monoMsNow -- reference time
```

picture is much more efficient

```bash
~/projects/lean-pipes/pipes  ↱ main ±✚  lake exe PipesTest
[+0ms][main] runTask1
[+0ms][main] runTask1 started
[+0ms][main] runTask2
[+0ms][main] runTask2 started
[+0ms][main] loop start
[+0ms][loop] stepsLeft=300, ch1c=false, ch2c=false
[+0ms][loop stepsLeft=300, ch1c=false, ch2c=false] starting select
[+0ms][main] loop created
[+0ms][t2] sending 10
[+0ms][t1] sending 1
[+1ms][t2] waiting 100 before sending 20
[+1ms][t1] waiting 100 before sending 2
[+2ms][loop stepsLeft=300, ch1c=false, ch2c=false] rx2 got (some 10)
[+2ms][loop] stepsLeft=299, ch1c=false, ch2c=false
[+2ms][loop stepsLeft=299, ch1c=false, ch2c=false] starting select
[+2ms][loop stepsLeft=299, ch1c=false, ch2c=false] rx1 got (some 1)
[+2ms][loop] stepsLeft=298, ch1c=false, ch2c=false
[+2ms][loop stepsLeft=298, ch1c=false, ch2c=false] starting select
[+101ms][t2] sending 20
[+101ms][t2] waiting 100 before sending 30
[+101ms][t1] sending 2
[+101ms][t1] waiting 100 before closing channel
[+101ms][loop stepsLeft=298, ch1c=false, ch2c=false] rx1 got (some 2)
[+101ms][loop] stepsLeft=297, ch1c=false, ch2c=false
[+101ms][loop stepsLeft=297, ch1c=false, ch2c=false] starting select
[+101ms][loop stepsLeft=297, ch1c=false, ch2c=false] rx2 got (some 20)
[+101ms][loop] stepsLeft=296, ch1c=false, ch2c=false
[+101ms][loop stepsLeft=296, ch1c=false, ch2c=false] starting select
[+202ms][t2] sending 30
[+202ms][t1] closing channel
[+202ms][t1] closed
[+202ms][t2] waiting 100 before sending 40
[+202ms][loop stepsLeft=296, ch1c=false, ch2c=false] rx1 got none
[+202ms][loop] stepsLeft=295, ch1c=true, ch2c=false
[+202ms][loop stepsLeft=295, ch1c=true, ch2c=false] starting select
[+202ms][loop stepsLeft=295, ch1c=true, ch2c=false] rx2 got (some 30)
[+202ms][loop] stepsLeft=294, ch1c=true, ch2c=false
[+202ms][loop stepsLeft=294, ch1c=true, ch2c=false] starting select
[+302ms][t2] sending 40
[+302ms][t2] waiting 100 before sending 50
[+303ms][loop stepsLeft=294, ch1c=true, ch2c=false] rx2 got (some 40)
[+303ms][loop] stepsLeft=293, ch1c=true, ch2c=false
[+303ms][loop stepsLeft=293, ch1c=true, ch2c=false] starting select
[+403ms][t2] sending 50
[+403ms][t2] waiting 100 before closing channel
[+403ms][loop stepsLeft=293, ch1c=true, ch2c=false] rx2 got (some 50)
[+403ms][loop] stepsLeft=292, ch1c=true, ch2c=false
[+403ms][loop stepsLeft=292, ch1c=true, ch2c=false] starting select
[+503ms][t2] closing channel
[+503ms][t2] closed
[+503ms][loop stepsLeft=292, ch1c=true, ch2c=false] rx2 got none
[+503ms][loop] stepsLeft=291, ch1c=true, ch2c=true
[+503ms][loop stepsLeft=291, ch1c=true, ch2c=true] both channels closed, exiting loop
[+503ms][main] loop finished, received ()
[+503ms][main] t1 finished
[+503ms][main] t2 finished
```

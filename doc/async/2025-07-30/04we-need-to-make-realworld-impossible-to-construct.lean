def main1 : IO Unit := do
  IO.println "1.1"
  IO.println "1.2"

/-- info: 1.1
1.2 -/
#guard_msgs in #eval main1

def main2 : IO Unit := do
  IO.println "2.1"
  match IO.println "2.2" ⟨⟩ with -- will be executed as if outside of IO
  | .error e _rw => IO.println s!"2. error2 {e}"
  | .ok .unit _rw => pure ()

/-- info: 2.1
2.2 -/
#guard_msgs in #eval main2

def main3 : EIO IO.Error Unit := do
  match IO.println "3.1" ⟨⟩ with -- will be executed as if outside of IO
  | .error e _rw => IO.println s!"3. error1 {e}"
  | .ok .unit _rw =>
    match IO.println "3.2" ⟨⟩ with -- will be executed as if outside of IO
    | .ok .unit _rw => pure ()
    | .error e _rw => IO.println s!"3. error2 {e}"

/-- info: 3.1
3.2 -/
#guard_msgs in #eval main3

def main4 : Except IO.Error Unit := do
  match IO.println "4.1" ⟨⟩ with -- will be executed as if outside of IO
  | .error _e _rw => return
  | .ok .unit _rw =>
    match IO.println "4.2" ⟨⟩ with -- will be executed as if outside of IO
    | .ok .unit _rw => pure ()
    | .error _e _rw => return

/-- info: ok: () -/
#guard_msgs in #eval main4

def main5 (rw : IO.RealWorld) : Except IO.Error Unit := do
  match IO.println "5.1" rw with -- will be executed as if outside of IO
  | .error _e _rw => return
  | .ok .unit _rw =>
    match IO.println "5.2" rw with -- will be executed as if outside of IO
    | .ok .unit _rw => pure ()
    | .error _e _rw => return

/-- info: ok: () -/
#guard_msgs in #eval main5 ⟨⟩

def main6 : EStateM IO.Error IO.RealWorld Unit := do
  match IO.println "6.1" ⟨⟩ with -- not executed
  | .error _e _rw => return
  | .ok .unit _rw =>
    match IO.println "6.2" ⟨⟩ with -- not executed
    | .ok .unit _rw => pure ()
    | .error _e _rw => return

def main6' : EIO IO.Error Unit := main6
def main6'' : IO Unit := main6

-- #guard_msgs in #eval main6 -- unable to synthesize 'MonadEval'

/-- -/
#guard_msgs in #eval main6'

/-- -/
#guard_msgs in #eval main6''

def main : IO Unit := do
  IO.println "========= 1"; main1
  IO.println "========= 2"; main2
  IO.println "========= 3"; main3
  IO.println "========= 4"; IO.println main4
  IO.println "========= 5"; IO.println (main5 ⟨⟩)
  IO.println "========= 6 (EStateM IO.Error IO.RealWorld Unit)"; main6
  IO.println "========= 6 (EIO IO.Error Unit)"; main6'
  IO.println "========= 6 (IO Unit)"; main6''

-- $ lake exe MyExe
-- 2.2
-- 3.1
-- 3.2
-- 4.1
-- 4.2
-- 5.1
-- 5.2
-- ========= 1
-- 1.1
-- 1.2
-- ========= 2
-- 2.1
-- ========= 3
-- ========= 4
-- ok: ()
-- ========= 5
-- ok: ()
-- ========= 6 (EStateM IO.Error IO.RealWorld Unit)
-- ========= 6 (EIO IO.Error Unit)
-- ========= 6 (IO Unit)

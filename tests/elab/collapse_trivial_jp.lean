module

/-!
This test checks that the compiler collapses trivial impure join points that only forward a value.
-/

/--
trace: [Compiler.saveImpure] size: 25
    def _private.elab.collapse_trivial_jp.0.test @&a b : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          inc[ref] a;
          return a
        | Option.some =>
          let val.1 := oproj[0] a;
          let val.2 := oproj[0] b;
          jp resetjp.3 _x.4 isShared.5 : tobj :=
            let _x.6 := Nat.add val.1 val.2;
            dec val.2;
            cases isShared.5 : tobj
            | Bool.false =>
              oset _x.4 [0] := _x.6;
              return _x.4
            | Bool.true =>
              let reuseFailAlloc.7 := ctor_1[Option.some] _x.6;
              return reuseFailAlloc.7;
          let isSharedCheck.8 := isShared b;
          cases isSharedCheck.8 : tobj
          | Bool.false =>
            goto resetjp.3 b isSharedCheck.8
          | Bool.true =>
            inc val.2;
            dec b;
            goto resetjp.3 ◾ isSharedCheck.8
[Compiler.saveImpure] size: 2
    def _private.elab.collapse_trivial_jp.0.test._boxed a b : tobj :=
      let res := _private.elab.collapse_trivial_jp.0.test a b;
      dec a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
def test (a b : Option Nat) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b => some (a + b)
    | none => some a
  | none => none

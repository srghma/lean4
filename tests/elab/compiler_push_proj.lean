/-! This does some basic unit tests for the pushProj pass in LCNF  -/


/--
trace: [Compiler.pushProj] size: 5
    def test1 a : tobj :=
      cases a : tobj
      | Option.none =>
        let _x.1 : tagged := 0;
        return _x.1
      | Option.some =>
        let val.2 : tobj := oproj[0] a;
        return val.2
[Compiler.pushProj] size: 6
    def test1 @&a : tobj :=
      cases a : tobj
      | Option.none =>
        let _x.1 : tagged := 0;
        return _x.1
      | Option.some =>
        let val.2 : tobj := oproj[0] a;
        inc val.2;
        return val.2
[Compiler.pushProj] size: 2
    def test1._boxed a : tobj :=
      let res : tobj := test1 a;
      dec a;
      return res
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test1 (a : Option Nat) : Nat :=
  match a with
  | some a => a
  | none => 0


/--
trace: [Compiler.pushProj] size: 10
    def test2 a b : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          return a
        | Option.some =>
          let val.1 : tobj := oproj[0] a;
          let val.2 : tobj := oproj[0] b;
          let _x.3 : tobj := Nat.add val.1 val.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
[Compiler.pushProj] size: 25
    def test2 @&a b : tobj :=
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
          let val.1 : tobj := oproj[0] a;
          let val.2 : tobj := oproj[0] b;
          jp resetjp.3 _x.4 isShared.5 : tobj :=
            let _x.6 : tobj := Nat.add val.1 val.2;
            dec val.2;
            cases isShared.5 : tobj
            | Bool.false =>
              oset _x.4 [0] := _x.6;
              return _x.4
            | Bool.true =>
              let reuseFailAlloc.7 : obj := ctor_1[Option.some] _x.6;
              return reuseFailAlloc.7;
          let isSharedCheck.8 : UInt8 := isShared b;
          cases isSharedCheck.8 : tobj
          | Bool.false =>
            goto resetjp.3 b isSharedCheck.8
          | Bool.true =>
            inc val.2;
            dec b;
            goto resetjp.3 ◾ isSharedCheck.8
[Compiler.pushProj] size: 2
    def test2._boxed a b : tobj :=
      let res : tobj := test2 a b;
      dec a;
      return res
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test2 (a b : Option Nat) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b => some (a + b)
    | none => some a
  | none => none

/--
trace: [Compiler.pushProj] size: 14
    def test3 a b : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
        | Option.some =>
          let val.5 : tobj := oproj[0] a;
          let val.6 : tobj := oproj[0] b;
          let _x.7 : tobj := Nat.add val.5 val.6;
          let _x.8 : obj := ctor_1[Option.some] _x.7;
          return _x.8
[Compiler.pushProj] size: 44
    def test3 a b : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          jp resetjp.2 _x.3 isShared.4 : tobj :=
            let _x.5 : tagged := 1;
            let _x.6 : tobj := Nat.add val.1 _x.5;
            dec val.1;
            cases isShared.4 : tobj
            | Bool.false =>
              oset _x.3 [0] := _x.6;
              return _x.3
            | Bool.true =>
              let reuseFailAlloc.7 : obj := ctor_1[Option.some] _x.6;
              return reuseFailAlloc.7;
          let isSharedCheck.8 : UInt8 := isShared a;
          cases isSharedCheck.8 : tobj
          | Bool.false =>
            goto resetjp.2 a isSharedCheck.8
          | Bool.true =>
            inc val.1;
            dec a;
            goto resetjp.2 ◾ isSharedCheck.8
        | Option.some =>
          let val.9 : tobj := oproj[0] a;
          inc val.9;
          dec[ref][1 objs] a;
          let val.10 : tobj := oproj[0] b;
          jp resetjp.11 _x.12 isShared.13 : tobj :=
            let _x.14 : tobj := Nat.add val.9 val.10;
            dec val.10;
            dec val.9;
            cases isShared.13 : tobj
            | Bool.false =>
              oset _x.12 [0] := _x.14;
              return _x.12
            | Bool.true =>
              let reuseFailAlloc.15 : obj := ctor_1[Option.some] _x.14;
              return reuseFailAlloc.15;
          let isSharedCheck.16 : UInt8 := isShared b;
          cases isSharedCheck.16 : tobj
          | Bool.false =>
            goto resetjp.11 b isSharedCheck.16
          | Bool.true =>
            inc val.10;
            dec b;
            goto resetjp.11 ◾ isSharedCheck.16
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test3 (a b : Option Nat) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b => some (a + b)
    | none => some (a + 1)
  | none => none

/--
trace: [Compiler.pushProj] size: 18
    def test4 a b c : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
        | Option.some =>
          cases c : tobj
          | Bool.false =>
            let _x.5 : tagged := ctor_0[Option.none];
            return _x.5
          | Bool.true =>
            let val.6 : tobj := oproj[0] a;
            let val.7 : tobj := oproj[0] b;
            let _x.8 : tobj := Nat.add val.6 val.7;
            let _x.9 : obj := ctor_1[Option.some] _x.8;
            return _x.9
[Compiler.pushProj] size: 50
    def test4 a b c : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          jp resetjp.2 _x.3 isShared.4 : tobj :=
            let _x.5 : tagged := 1;
            let _x.6 : tobj := Nat.add val.1 _x.5;
            dec val.1;
            cases isShared.4 : tobj
            | Bool.false =>
              oset _x.3 [0] := _x.6;
              return _x.3
            | Bool.true =>
              let reuseFailAlloc.7 : obj := ctor_1[Option.some] _x.6;
              return reuseFailAlloc.7;
          let isSharedCheck.8 : UInt8 := isShared a;
          cases isSharedCheck.8 : tobj
          | Bool.false =>
            goto resetjp.2 a isSharedCheck.8
          | Bool.true =>
            inc val.1;
            dec a;
            goto resetjp.2 ◾ isSharedCheck.8
        | Option.some =>
          cases c : tobj
          | Bool.false =>
            dec[ref][1 objs] b;
            dec[ref][1 objs] a;
            let _x.9 : tagged := ctor_0[Option.none];
            return _x.9
          | Bool.true =>
            let val.10 : tobj := oproj[0] a;
            inc val.10;
            dec[ref][1 objs] a;
            let val.11 : tobj := oproj[0] b;
            jp resetjp.12 _x.13 isShared.14 : tobj :=
              let _x.15 : tobj := Nat.add val.10 val.11;
              dec val.11;
              dec val.10;
              cases isShared.14 : tobj
              | Bool.false =>
                oset _x.13 [0] := _x.15;
                return _x.13
              | Bool.true =>
                let reuseFailAlloc.16 : obj := ctor_1[Option.some] _x.15;
                return reuseFailAlloc.16;
            let isSharedCheck.17 : UInt8 := isShared b;
            cases isSharedCheck.17 : tobj
            | Bool.false =>
              goto resetjp.12 b isSharedCheck.17
            | Bool.true =>
              inc val.11;
              dec b;
              goto resetjp.12 ◾ isSharedCheck.17
[Compiler.pushProj] size: 2
    def test4._boxed a b c : tobj :=
      let c.boxed : UInt8 := unbox c;
      let res : tobj := test4 a b c.boxed;
      return res
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test4 (a b : Option Nat) (c : Bool) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b =>
      match c with
      | true => some (a + b)
      | false => none
    | none => some (a + 1)
  | none => none

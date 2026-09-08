/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Coe
public import Init.Data.Repr
public import Init.Data.Vector
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section

inductive JSBinOp where
  | and | bitAnd | bitOr | bitXor | divide | eq | ge | gt | in_ | instanceOf | le | lsh | lt | minus | mod | neq | of | or | plus | rsh | strictEq | strictNeq | times | ursh
  deriving Repr, BEq, Inhabited

inductive JSUnaryOp where
  | decr | delete | incr | minus | not | plus | tilde | typeof | void
  deriving Repr, BEq, Inhabited

mutual
  inductive PropExprList : Nat → Type where
    | nil : PropExprList n
    | cons (prop : String) (val : Expr n) (tail : PropExprList n) : PropExprList n
    deriving Repr, BEq, Inhabited

  inductive ExprList : Nat → Type where
    | nil : ExprList n
    | cons (head : Expr n) (tail : ExprList n) : ExprList n
    deriving Repr, BEq, Inhabited

  inductive Expr : Nat → Type where
    | var    (i : Fin n)                                        : Expr n
    | global (name : String)                                    : Expr n
    | num    (val : Nat)                                        : Expr n
    | numLit (val : String)                                     : Expr n
    | str    (val : String)                                     : Expr n
    | bool   (val : Bool)                                       : Expr n
    | obj    (props : PropExprList n)                           : Expr n
    | arr    (elems : ExprList n)                               : Expr n
    | call   (fn : Expr n) (args : ExprList n)                  : Expr n
    | prop   (obj : Expr n) (name : String)                     : Expr n
    | index  (obj idx : Expr n)                                 : Expr n
    | unary  (op : JSUnaryOp) (a : Expr n)                      : Expr n
    | binop  (op : JSBinOp) (a b : Expr n)                      : Expr n
    | cond   (c : BExpr n) (t e : Expr n)                       : Expr n
    | new    (cls : Expr n) (args : ExprList n)                 : Expr n
    | assign (lhs rhs : Expr n)                                 : Expr n
    | arrowExpr (params : Nat) (body : Expr (n + params))       : Expr n
    | leanGeneratedEnumIsTag    (obj : Expr n) (tag : Name)     : Expr n
    | leanGeneratedEnumGetField (obj : Expr n) (idx : Nat)      : Expr n
    | leanGeneratedEnumMk       (tag : Name) (fields : ExprList n) : Expr n
    deriving Repr, BEq, Inhabited

  inductive BExpr : Nat → Type where
    | tt                                         : BExpr n
    | ff                                         : BExpr n
    | truthy (e : Expr n)                        : BExpr n
    | lt (a b : Expr n)                          : BExpr n
    | le (a b : Expr n)                          : BExpr n
    | eq (a b : Expr n)                          : BExpr n
    | strictEq (a b : Expr n)                    : BExpr n
    | not (c : BExpr n)                          : BExpr n
    | and (c d : BExpr n)                        : BExpr n
    | or (c d : BExpr n)                         : BExpr n
    deriving Repr, BEq, Inhabited
end

public def PropExprList.toList : PropExprList n → List (String × Expr n)
  | .nil => []
  | .cons p v tail => (p, v) :: tail.toList

public def PropExprList.ofList : List (String × Expr n) → PropExprList n
  | [] => .nil
  | (p, v) :: tail => .cons p v (ofList tail)

public def ExprList.toList : ExprList n → List (Expr n)
  | .nil => []
  | .cons h t => h :: t.toList

public def ExprList.toArray : ExprList n → Array (Expr n)
  | .nil => #[]
  | .cons h t => #[h] ++ t.toArray

public def ExprList.ofList : List (Expr n) → ExprList n
  | [] => .nil
  | x :: xs => .cons x (ofList xs)

public def ExprList.ofArray (a : Array (Expr n)) : ExprList n :=
  ofList a.toList

inductive Ownership where
  | borrowed
  | owned
  deriving Repr, BEq, Inhabited

mutual
  inductive Stmt : Nat → Type where
    | ret        (e : Expr n)                                                    : Stmt n
    | letIn      (val : Expr n) (k : Stmt (n+1))                                 : Stmt n
    | letClosure {m : Nat} (f : InlinableFunc m) (captures : ExprList n) (k : Stmt (n+1)) : Stmt n
    | seq        (e : Expr n) (k : Stmt n)                                       : Stmt n
    | ifElse     (cond : BExpr n) (t e : Stmt n) (k : Stmt n)                   : Stmt n
    | loop       (m : Nat) (stateNames : Array String)
                 (state0 : ExprList n)
                 (cond : BExpr (n+m)) (body : Stmt (n+m))
                 (k : Stmt (n+m))                                               : Stmt n
    | continue   (newState : ExprList n)                                         : Stmt n
    | break_                                                                    : Stmt n
    deriving Repr, BEq, Inhabited

  inductive InlinableFunc : Nat → Type where
    | mk (paramNames : Array String) (paramOwn : Array Ownership) (body : Stmt n) (returns : Option (Expr n)) : InlinableFunc n
    deriving Repr, BEq, Inhabited
end

def throwNewError (msg : String) : Expr n :=
  .call (.global "throw") (.cons (.new (.global "Error") (.cons (.str msg) .nil)) .nil)

def plus (a b : Expr n) := Expr.binop .plus a b
def minus (a b : Expr n) := Expr.binop .minus a b
def times (a b : Expr n) := Expr.binop .times a b
def divide (a b : Expr n) := Expr.binop .divide a b
def mod (a b : Expr n) := Expr.binop .mod a b
def pow (a b : Expr n) := Expr.call (.prop (.global "Math") "pow") (.cons a (.cons b .nil))

instance : Add (Expr n) where add := plus
instance : Sub (Expr n) where sub := minus
instance : Mul (Expr n) where mul := times
instance : Div (Expr n) where div := divide
instance : Mod (Expr n) where mod := mod
instance : Pow (Expr n) (Expr n) where pow := pow

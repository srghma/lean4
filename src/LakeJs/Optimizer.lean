/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Data.Repr
public import Std.Data.HashMap
public import LakeJs.Js

public section

namespace Lean.Compiler.JS

mutual
  public partial def partialEval (e : JsInlineExpr) (env : Std.HashMap String JsInlineExpr := {}) : JsInlineExpr :=
    match e with
    | .identifier name =>
      match env.get? name with
      | some v => v
      | none => .identifier name
    | .isTag obj tag =>
      let obj' := partialEval obj env
      match obj' with
      | .mkObject actualTag _ => .boolLiteral (actualTag == tag)
      | .objectLiteral fields =>
        match fields.find? (fun (k, _) => k == "tag") with
        | some (_, .stringLiteral actualTagStr) => .boolLiteral (actualTagStr == mangleName tag)
        | _ => .isTag obj' tag
      | _ => .isTag obj' tag
    | .getField obj idx =>
      let obj' := partialEval obj env
      match obj' with
      | .mkObject _ fields =>
        if h : idx < fields.size then
          partialEval fields[idx] env
        else
          .getField obj' idx
      | .objectLiteral fields =>
        let key := s!"_{idx + 1}"
        match fields.find? (fun (k, _) => k == key) with
        | some (_, val) => partialEval val env
        | none => .getField obj' idx
      | _ => .getField obj' idx
    | .mkObject tag fields =>
      .mkObject tag (fields.map (partialEval · env))
    | .arrayLiteral elems =>
      .arrayLiteral (elems.map (partialEval · env))
    | .objectLiteral fields =>
      .objectLiteral (fields.map fun (k, v) => (k, partialEval v env))
    | .expressionBinary op lhs rhs =>
      let lhs' := partialEval lhs env
      let rhs' := partialEval rhs env
      match op, lhs', rhs' with
      | .strictEq, .boolLiteral a, .boolLiteral b => .boolLiteral (a == b)
      | .eq, .boolLiteral a, .boolLiteral b => .boolLiteral (a == b)
      | .strictEq, .decimal a, .decimal b => .boolLiteral (a == b)
      | .strictEq, .stringLiteral a, .stringLiteral b => .boolLiteral (a == b)
      | .plus, .decimal a, .decimal b => .decimal (a + b)
      | .minus, .decimal a, .decimal b => .decimal (a - b)
      | .times, .decimal a, .decimal b => .decimal (a * b)
      | _, _, _ => .expressionBinary op lhs' rhs'
    | .expressionTernary cond t e =>
      let cond' := partialEval cond env
      match cond' with
      | .boolLiteral true => partialEval t env
      | .boolLiteral false => partialEval e env
      | _ => .expressionTernary cond' (partialEval t env) (partialEval e env)
    | .callExpression fn args =>
      let fn' := partialEval fn env
      let args' := args.map (partialEval · env)
      match fn' with
      | .arrowFunction params body =>
        if params.size == args'.size then
          let env' := (params.zip args').foldl (fun e (p, a) => e.insert p a) env
          partialEval body env'
        else
          .callExpression fn' args'
      | .arrowFunctionBlock params stmts =>
        if params.size == args'.size then
          let env' := (params.zip args').foldl (fun e (p, a) => e.insert p a) env
          evalStmts stmts env'
        else
          .callExpression fn' args'
      | _ => .callExpression fn' args'
    | other => other

  public partial def evalStmts (stmts : Array JsInlineStmt) (env : Std.HashMap String JsInlineExpr) : JsInlineExpr :=
    match stmts.toList with
    | [] => .identifier "undefined"
    | stmt :: rest =>
      match stmt with
      | .const name val | .letVar name val =>
        let env' := env.insert name (partialEval val env)
        evalStmts rest.toArray env'
      | .assign (.identifier name) val =>
        let env' := env.insert name (partialEval val env)
        evalStmts rest.toArray env'
      | .expr (.callExpression (.memberDot (.identifier arrName) "push") #[item]) =>
        let item' := partialEval item env
        let env' := match env.get? arrName with
          | some (.arrayLiteral elems) => env.insert arrName (.arrayLiteral (elems.push item'))
          | _ => env
        evalStmts rest.toArray env'
      | .while cond body =>
        evalWhile cond body rest.toArray env 10000
      | .return val =>
        partialEval val env
      | _ =>
        evalStmts rest.toArray env

  public partial def evalWhile (cond : JsInlineExpr) (body : Array JsInlineStmt) (rest : Array JsInlineStmt)
      (env : Std.HashMap String JsInlineExpr) (fuel : Nat) : JsInlineExpr :=
    if fuel == 0 then
      evalStmts rest env
    else
      let cond' := partialEval cond env
      match cond' with
      | .boolLiteral true =>
        let env' := stepLoopBody body env
        evalWhile cond body rest env' (fuel - 1)
      | .boolLiteral false =>
        evalStmts rest env
      | _ =>
        -- Cannot statically determine loop condition: residualize
        let outExpr := env.get? "out" |>.getD (.arrayLiteral #[])
        let currExpr := env.get? "curr" |>.getD cond'
        .callExpression
          (.arrowFunctionBlock #["curr"]
            #[.const "out" outExpr,
              .while (partialEval cond env) body,
              .return (.identifier "out")])
          #[currExpr]

  public partial def stepLoopBody (body : Array JsInlineStmt) (env : Std.HashMap String JsInlineExpr) : Std.HashMap String JsInlineExpr :=
    body.foldl (init := env) fun e stmt =>
      match stmt with
      | .const name val | .letVar name val =>
        e.insert name (partialEval val e)
      | .assign (.identifier name) val =>
        e.insert name (partialEval val e)
      | .expr (.callExpression (.memberDot (.identifier arrName) "push") #[item]) =>
        let item' := partialEval item e
        match e.get? arrName with
        | some (.arrayLiteral elems) => e.insert arrName (.arrayLiteral (elems.push item'))
        | _ => e
      | _ => e
end

public def applyInline (fn : JsInlineExpr) (args : Array JsInlineExpr) : JsInlineExpr :=
  match fn with
  | .callExpression (.arrowFunctionBlock params stmts) #[.funArg 0] =>
    if args.size > 0 then
      partialEval (.callExpression (.arrowFunctionBlock params stmts) #[args[0]!])
    else
      .callExpression fn args
  | .callExpression fnInner #[.funArg 0] =>
    if args.size > 0 then
      partialEval (.callExpression fnInner #[args[0]!])
    else
      .callExpression fn args
  | _ =>
    partialEval (.callExpression fn args)

end Lean.Compiler.JS

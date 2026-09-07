/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Data.Repr
public import LakeJs.Js

public section

namespace Lean.Compiler.JS

mutual
  public partial def renderJs (e : JsInlineExpr) : String :=
    match e with
    | .funArg idx => s!"#${idx}"
    | .identifier name => name
    | .decimal val => s!"{val}"
    | .hex val => s!"0x{Nat.toDigits 16 val |> String.ofList}"
    | .stringLiteral val => s!"\"{val}\""
    | .boolLiteral val => if val then "true" else "false"
    | .arrayLiteral elems =>
      "[" ++ ", ".intercalate (elems.map renderJs).toList ++ "]"
    | .objectLiteral fields =>
      if fields.isEmpty then "{}"
      else "({ " ++ ", ".intercalate (fields.map fun (k, v) => s!"{k}: {renderJs v}").toList ++ " })"
    | .isTag obj tag =>
      s!"({renderJs obj}.tag === \"{mangleName tag}\")"
    | .getField obj idx =>
      s!"{renderJs obj}._{idx + 1}"
    | .mkObject tag fields =>
      if fields.isEmpty then
        s!"(\{ tag: \"{mangleName tag}\" })"
      else
        let fieldStrs := fields.mapIdx fun i f => s!"_{i + 1}: {renderJs f}"
        s!"(\{ tag: \"{mangleName tag}\", {", ".intercalate fieldStrs.toList} })"
    | .callExpression fn args =>
      s!"{renderJs fn}({", ".intercalate (args.map renderJs).toList})"
    | .memberDot obj name =>
      s!"{renderJs obj}.{name}"
    | .memberSquare obj idx =>
      s!"{renderJs obj}[{renderJs idx}]"
    | .unaryExpression op arg =>
      let opStr := match op with
        | .not => "!" | .minus => "-" | .tilde => "~" | .typeof => "typeof " | _ => ""
      s!"{opStr}{renderJs arg}"
    | .expressionBinary op lhs rhs =>
      let opStr := match op with
        | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
        | .eq => "==" | .strictEq => "===" | .neq => "!=" | .strictNeq => "!=="
        | .le => "<=" | .lt => "<" | .gt => ">" | .ge => ">="
        | .and => "&&" | .or => "||"
        | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
        | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
        | _ => "=="
      s!"({renderJs lhs} {opStr} {renderJs rhs})"
    | .expressionTernary cond t e =>
      s!"({renderJs cond} ? {renderJs t} : {renderJs e})"
    | .memberNew expr args =>
      s!"new {renderJs expr}({", ".intercalate (args.map renderJs).toList})"
    | .throw expr =>
      s!"throw {renderJs expr}"
    | .arrowFunction params body =>
      s!"(({", ".intercalate params.toList}) => {renderJs body})"
    | .arrowFunctionBlock params stmts =>
      let stmtsStr := String.join (stmts.toList.map fun s => "  " ++ renderJsStmt s ++ "\n")
      s!"(({", ".intercalate params.toList}) => \{\n{stmtsStr}})"

  public partial def renderJsStmt (s : JsInlineStmt) : String :=
    match s with
    | .const name val => s!"const {name} = {renderJs val};"
    | .letVar name val => s!"let {name} = {renderJs val};"
    | .assign lhs rhs => s!"{renderJs lhs} = {renderJs rhs};"
    | .expr e => s!"{renderJs e};"
    | .return e => s!"return {renderJs e};"
    | .while cond body =>
      let bodyStr := String.join (body.toList.map fun st => "    " ++ renderJsStmt st ++ "\n")
      s!"while ({renderJs cond}) \{\n{bodyStr}  }"
end

end Lean.Compiler.JS

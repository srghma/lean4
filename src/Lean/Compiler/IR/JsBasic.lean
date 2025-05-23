/-
Copyright (c) 2024 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
prelude
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt
import Lean.CoreM
import Lean.Environment

namespace Lean.Compiler.ToJS

/-!
# LCNF to JavaScript AST Transformation

This module defines a JavaScript-like AST and provides functions
to translate LCNF declarations into this AST.
-/

-- TODO: Robust name mangling
def mangleName (n : Name) : String :=
  n.toString.replace "." "_" |>.replace "[" "$o" |>.replace "]" "$c"

/-!
## JavaScript AST Definitions
-/

inductive JsLit where
  | num (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  | null
  | undefined
  deriving Inhabited, Repr, BEq

inductive JsBinOp where
  | add | sub | mul | div | mod
  | eq | neq | lt | le | gt | ge
  | and | or
  deriving Inhabited, Repr, BEq

-- Simplified JS Expression AST
inductive JsExpr where
  | lit (l : JsLit)
  | ident (name : String)
  | call (fn : JsExpr) (args : Array JsExpr)
  | propAccess (obj : JsExpr) (prop : String) -- obj.prop
  | elemAccess (obj : JsExpr) (index : JsExpr) -- obj[index]
  | anonFn (params : Array String) (body : Array JsExpr ) --/* JsStmt */  Simplified: body is array of expressions
  | binOp (op : JsBinOp) (lhs : JsExpr) (rhs : JsExpr)
  | new (ctor : JsExpr) (args : Array JsExpr)
  | array (elems : Array JsExpr)
  | object (props : Array (String × JsExpr))
  deriving Inhabited, Repr, BEq

inductive JsStmt where
  | expr (e : JsExpr) -- For expressions used as statements (e.g., function calls)
  | varDecl (name : String) (init? : Option JsExpr) -- `let name = init?` or `let name`
  | assign (lhs : JsExpr) (rhs : JsExpr)
  | return (e? : Option JsExpr)
  | if (cond : JsExpr) (thenBranch : Array JsStmt) (elseBranch? : Option (Array JsStmt))
  | while (cond : JsExpr) (body : Array JsStmt)
  | block (stmts : Array JsStmt)
  -- Add more: for loops, try-catch, switch, etc.
  deriving Inhabited, Repr, BEq

-- Top-level JavaScript Declarations
inductive JsDecl where
  | funDecl (name : String) (params : Array String) (body : Array JsStmt)
  | constDecl (name : String) (value : JsExpr)
  | classDecl (name : String) (constructor? : Option JsDecl) (methods : Array JsDecl) -- Simplified
  | importDecl (names : Array String) (module : String) -- Simplified
  | raw (js : String) -- For injecting raw JS
  deriving Inhabited, Repr, BEq


/-!
## LCNF to JS AST Transformation
-/

open Lean.Compiler.LCNF (Alt Arg Code Decl DeclValue LCtx LetDecl LetValue LitValue Param getMonoDecl?)

structure ToJsState where
  -- Potentially a map from LCNF FVarId to JS variable names if complex scoping/shadowing needs handling
  fvarMapping : Std.HashMap FVarId String := {}
  -- For generating unique temporary variable names
  nextTmpVarIdx : Nat := 0
  -- For collecting top-level JS declarations (e.g. helper functions)
  topLevelDecls : Array JsDecl := #[]

abbrev M := StateT ToJsState CoreM

def M.run (x : M α) : CoreM (α × ToJsState) :=
  StateT.run x {}

def freshJsName (base : String := "tmp") : M String := do
  let idx ← modifyGet fun s => (s.nextTmpVarIdx, {s with nextTmpVarIdx := s.nextTmpVarIdx + 1})
  return s!"{base}_{idx}"

def getJsFVar (fvarId : FVarId) : M String := do
  let s ← get
  match s.fvarMapping.getKey? fvarId with
  | some name => return name
  | none =>
    let name ← freshJsName ("v_" ++ fvarId.name.eraseMacroScopes.toString)
    modify fun s => {s with fvarMapping := s.fvarMapping.insert fvarId name}
    return name

def bindFVar (fvarId : FVarId) (jsName : String) : M Unit := do
  modify fun s => {s with fvarMapping := s.fvarMapping.insert fvarId jsName}


-- TODO: This needs to be much more sophisticated, handling Lean's type system,
-- especially for algebraic data types, enums, and how they map to JS (objects, tagged unions, etc.)
def lowerTypeToJsComment (_e : Lean.Expr) : M String := do
  -- For now, we just make a comment. A real implementation would map Lean types to JS runtime types/checks
  -- or integrate with something like TypeScript.
  -- return s!"/* TODO: type {_e} */"
  return "" -- Or omit for cleaner JS for now

def lowerLCNFLitValue (v : LCNF.LitValue) : JsLit :=
  match v with
  | .natVal n => .num n
  | .strVal s => .str s

def lowerLCNFArg (arg : LCNF.Arg) : M (Option JsExpr) := do
  match arg with
  | .fvar fvarId => return some (.ident (← getJsFVar fvarId))
  | .erased => return none -- Erased arguments don't translate to JS values directly
  | .type _e => return none -- Type arguments are compile-time, not runtime JS values

def lowerLCNFParams (params : Array LCNF.Param) : M (Array String) := do
  params.mapM fun p => do
    let jsName ← freshJsName p.binderName.toString
    bindFVar p.fvarId jsName
    return jsName

mutual
  partial def lowerLCNFCode (code : LCNF.Code) : M (Array JsStmt) := do
    match code with
    | .let decl k =>
      let jsValName ← freshJsName decl.binderName.toString
      bindFVar decl.fvarId jsValName
      let jsInit? ← lowerLCNFLetValue decl.value
      let valStmt : JsStmt := .varDecl jsValName jsInit?
      let kStmts ← lowerLCNFCode k
      return #[valStmt] ++ kStmts

    | .fun decl k =>
      -- Local functions in LCNF. These would become nested functions or IIFEs in JS.
      -- For simplicity, we might assume lambda lifting has occurred, or generate helpers.
      -- This is a complex part. A simple approach for now:
      let fnName := mangleName decl.binderName -- Might need to be unique
      let jsParams ← lowerLCNFParams decl.params
      let bodyStmts ← lowerLCNFCode decl.value
      let funDecl : JsDecl := .funDecl fnName jsParams bodyStmts
      modify fun s => {s with topLevelDecls := s.topLevelDecls.push funDecl}
      -- The continuation `k` would typically see `fnName` in scope.
      -- If `k` uses `decl.fvarId`, it should now refer to `fnName`.
      -- This requires careful handling of the `fvarMapping`.
      -- For now, assume `k` doesn't immediately reuse `decl.fvarId` for the function itself
      -- in a way that requires a JS variable holding the function.
      -- If `decl.fvarId` is used later, `getJsFVar` will need to know it's this function.
      -- This might be better handled by having `lowerLCNFLetValue` handle `.fun` cases
      -- if they are assigned to variables.
      -- For now, we'll just proceed with `k`.
      let kStmts ← lowerLCNFCode k
      return kStmts -- This is too simple; `funDecl` should be callable via `decl.fvarId`

    | .jp decl k =>
      -- Join points are like GOTO labels with parameters. Tricky to map directly to idiomatic JS.
      -- Often compiled to loops or nested functions.
      -- For now, we'll treat them like local functions for simplicity, but this needs refinement.
      let jpName := mangleName decl.binderName -- Needs to be unique
      let jsParams ← lowerLCNFParams decl.params
      let bodyStmts ← lowerLCNFCode decl.value
      let jpFunDecl : JsDecl := .funDecl jpName jsParams bodyStmts
      modify fun s => {s with topLevelDecls := s.topLevelDecls.push jpFunDecl}
      -- Continuation
      let kStmts ← lowerLCNFCode k
      return kStmts -- This is too simple

    | .jmp fvarId args =>
      -- This should call the "function" corresponding to the join point `fvarId`.
      let jpName ← getJsFVar fvarId -- Assuming `fvarId` for JP was mapped to a function name
      let jsArgs ← args.filterMapM lowerLCNFArg
      return #[.expr (.call (.ident jpName) jsArgs)] -- Or a return if it's tail position

    | .cases cases =>
      let discrVarName ← getJsFVar cases.discr
      let mut jsCases : Array (JsExpr × Array JsStmt) := #[]
      let mut defaultBranch? : Option (Array JsStmt) := none

      -- This is highly dependent on how ADTs are represented in JS.
      -- PureScript typically uses objects with a tag field (e.g., `{ tag: "ConstructorName", fields: [...] }`)
      -- or a specific structure for 0-arity constructors.
      -- We'll sketch a switch-like structure on a tag.
      let tagAccess := JsExpr.propAccess (.ident discrVarName) "tag" -- Assuming a 'tag' property

      for alt in cases.alts do
        match alt with
        | .alt ctorName params code =>
          let ctorJsName := mangleName ctorName
          -- Bind params: Assuming fields are accessible on `discrVarName` (e.g., `discrVarName.fields[0]`)
          let mut paramBindings : Array JsStmt := #[]
          for i in [:params.size] do
            let p := params[i]!
            let pJsName ← freshJsName p.binderName.toString
            bindFVar p.fvarId pJsName
            -- This access pattern is a placeholder for how fields are actually laid out
            let fieldAccess := JsExpr.elemAccess (JsExpr.propAccess (.ident discrVarName) "_fields") (.lit (.num i))
            paramBindings := paramBindings.push (.varDecl pJsName (some fieldAccess))

          let altBody ← lowerLCNFCode code
          jsCases := jsCases.push (.lit (.str ctorJsName), paramBindings ++ altBody)

        | .default code =>
          defaultBranch? := some (← lowerLCNFCode code)

      -- Constructing the if/else if/else chain or switch
      if jsCases.isEmpty then
        if let some defaultStmts := defaultBranch? then
          return defaultStmts
        else
          return #[.expr (.call (.ident "lean_panic") #[.lit (.str "Empty cases with no default")])]
      else
        let rec buildIfChain (idx : Nat) (currentCases : Array (JsExpr × Array JsStmt)) : Array JsStmt :=
          if idx >= currentCases.size then
            defaultBranch?.getD #[]
          else
            let (caseVal, thenBody) := currentCases[idx]!
            let cond := JsExpr.binOp .eq tagAccess caseVal
            #[.if cond thenBody (some <| buildIfChain (idx+1) currentCases)]
        return buildIfChain 0 jsCases


    | .return fvarId =>
      match ← lowerLCNFArg (.fvar fvarId) with
      | some expr => return #[.return (some expr)]
      | none => return #[.return none] -- Returning an erased value (e.g. Unit)

    | .unreach _type =>
      -- Could throw an error or call a runtime panic function
      return #[.expr (.call (.ident "lean_unreachable") #[])]


  partial def lowerLCNFLetValue (value : LCNF.LetValue) : M (Option JsExpr) := do
    match value with
    | .value lit => return some (.lit (lowerLCNFLitValue lit))
    | .erased => return none
    | .proj typeName ctorIdx structFVarId =>
        let structJsName ← getJsFVar structFVarId
        -- This requires knowing the layout of the constructor `typeName` in JS.
        -- Assuming fields are in an array property `_fields`.
        -- And the constructor index `ctorIdx` here refers to the *field* index.
        return some (.elemAccess (JsExpr.propAccess (.ident structJsName) "_fields") (.lit (.num ctorIdx)))

    | .const declName _us args =>
        let jsDeclName := mangleName declName
        let jsArgs ← args.filterMapM lowerLCNFArg
        -- Special handling for known constants
        if declName == ``Nat.add then
            if jsArgs.size == 2 then return some (JsExpr.binOp .add jsArgs[0]! jsArgs[1]!) else none
        else if declName == ``Nat.sub then
            if jsArgs.size == 2 then return some (JsExpr.binOp .sub jsArgs[0]! jsArgs[1]!) else none
        -- ... more numeric ops ...
        else if declName == ``decide then -- Assuming `decide p` translates to `p` if p is boolean expr
             if jsArgs.size == 1 then return some jsArgs[0]! else none
        else
          -- TODO: Check if `declName` is a constructor
          let env ← getEnv
          if isConstructor env declName then
            -- Constructor call: { tag: "CtorName", _fields: [...] }
            let fieldArgs := jsArgs -- This is a simplification, might need to skip erased args from LCNF.args
            return some (JsExpr.object #[
              ("tag", .lit (.str (mangleName declName))),
              ("_fields", .array fieldArgs)
            ])
          else
            return some (JsExpr.call (.ident jsDeclName) jsArgs)

    | .fvar fvarId args =>
        let fnJsName ← getJsFVar fvarId
        let jsArgs ← args.filterMapM lowerLCNFArg
        return some (JsExpr.call (.ident fnJsName) jsArgs)
end


def lowerLCNFDecl (decl : LCNF.Decl) : M (Option JsDecl) := do
  match decl.value with
  | .code code =>
    let jsParams ← lowerLCNFParams decl.params
    let bodyStmts ← lowerLCNFCode code
    let mangledDeclName := mangleName decl.name
    return some (.funDecl mangledDeclName jsParams bodyStmts)
  | .extern externAttrData =>
    -- For externs, we need to know the JS name.
    -- This information is in `externAttrData`.
    -- We'll assume a simple case where there's one JS entry.
    match externAttrData.getBackendEntry "javascript" with
    | some (.strVal jsName) =>
      -- This declaration is implemented by an external JS function `jsName`.
      -- We might not need to generate a JsDecl for it if it's purely external.
      -- Or, we might generate a JS constant that refers to it if the Lean name
      -- needs to be callable from other generated JS.
      -- For now, let's assume it means we *don't* generate a body.
      -- We could generate a constant:
      -- return some (.constDecl (mangleName decl.name) (.ident jsName))
      -- Or, more commonly, we'd make sure calls to `decl.name` use `jsName`.
      -- This is implicitly handled if `mangleName decl.name` happens to be `jsName`
      -- or if we have a mapping for externs.
      -- For now, skip generating a JS declaration for it, assuming it's provided.
      return none
    | _ =>
      -- No JS extern entry, or not a simple string.
      -- Could try to generate a default stub or error.
      println! "[Warning] No 'javascript' string entry for extern {decl.name}"
      return none


def lcnfToJs (lcnfDecls: Array LCNF.Decl) : CoreM (Array JsDecl) := do
  let ((_mainResults, finalState) : Unit × ToJsState) ← (lcnfDecls.forM fun decl => do discard <| lowerLCNFDecl decl).run
  -- The `lowerLCNFDecl` for the main declarations would have added them to `topLevelDecls` as well.
  -- Or we can collect them explicitly:
  let mut allJsDecls := finalState.topLevelDecls
  for lcnfDecl in lcnfDecls do
    let ((jsDecl?, _s) : Option JsDecl × ToJsState) ← (lowerLCNFDecl lcnfDecl).run
    if let some jsDecl := jsDecl? then
      allJsDecls := allJsDecls.push jsDecl

  -- Add any runtime functions needed
  -- allJsDecls := allJsDecls.push (.raw "function lean_panic(s) { console.error('PANIC:', s); throw new Error(s); }")
  -- allJsDecls := allJsDecls.push (.raw "function lean_unreachable() { lean_panic('Reached unreachable code'); }")

  return allJsDecls

/-!
## Pretty Printing JS AST (Simplified)
-/

def JsLit.toCode : JsLit → String
  | .num n => toString n
  | .str s => "\"" ++ s.replace "\\" "\\\\" ++ "\"" -- Basic escaping
  | .bool b => if b then "true" else "false"
  | .null => "null"
  | .undefined => "undefined"

def JsBinOp.toCode : JsBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "===" | .neq => "!==" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

partial def JsExpr.toCode : JsExpr → String
  | .lit l => l.toCode
  | .ident name => name
  | .call fn args => s!"{fn.toCode}({", ".intercalate (args.map JsExpr.toCode).toList})"
  | .propAccess obj prop => s!"{obj.toCode}.{prop}"
  | .elemAccess obj idx => s!"{obj.toCode}[{idx.toCode}]"
  | .anonFn params body =>
    let bodyStr := body.map (fun e => s!"  return ${e.toCode};\n") -- Simplified: each expr is a return
    s!"function(${", ".intercalate params.toList}) {\n${"".intercalate bodyStr.toList}}"
  | .binOp op lhs rhs => s!"(${lhs.toCode} ${op.toCode} ${rhs.toCode})"
  | .new ctor args => s!"new {ctor.toCode}({", ".intercalate (args.map JsExpr.toCode).toList})"
  | .array elems => s!"[${", ".intercalate (elems.map JsExpr.toCode).toList}]"
  | .object props =>
    let propsStr := props.map fun (k, v) => s!"  ${k}: ${v.toCode}"
    s!"{\n${",\n".intercalate propsStr.toList}\n}"


partial def JsStmt.toCode (indent : String) : JsStmt → String
  | .expr e => s!"{indent}{e.toCode};\n"
  | .varDecl name init? =>
    match init? with
    | some init => s!"{indent}let {name} = {init.toCode};\n"
    | none => s!"{indent}let {name};\n"
  | .assign lhs rhs => s!"{indent}{lhs.toCode} = {rhs.toCode};\n"
  | .return (some e) => s!"{indent}return {e.toCode};\n"
  | .return none => s!"{indent}return;\n"
  | .if cond thenB elseB? =>
    let thenStr := thenB.map (JsStmt.toCode (indent ++ "  ")) |> "".intercalate
    let elseStr := match elseB? with
      | some elseB => s!"{indent}else {\n{"".intercalate (elseB.map (JsStmt.toCode (indent ++ "  ")))}\n{indent}}\n"
      | none => ""
    s!"{indent}if (${cond.toCode}) {\n{thenStr}{indent}}\n{elseStr}"
  | .while cond body =>
    let bodyStr := body.map (JsStmt.toCode (indent ++ "  ")) |> "".intercalate
    s!"{indent}while (${cond.toCode}) {\n{bodyStr}{indent}}\n"
  | .block stmts =>
    let stmtsStr := stmts.map (JsStmt.toCode (indent ++ "  ")) |> "".intercalate
    s!"{indent}{\n{stmtsStr}{indent}}\n"

def JsDecl.toCode : JsDecl → String
  | .funDecl name params body =>
    let bodyStr := body.map (JsStmt.toCode "  ") |> "".intercalate
    s!"function {name}({", ".intercalate params.toList}) {\n{bodyStr}}\n"
  | .constDecl name value => s!"const {name} = {value.toCode};\n"
  | .classDecl name _constructor? methods => -- Simplified
    let methodsStr := methods.map (fun m => "  " ++ m.toCode.replace "\n" ("\n  ")) -- Basic indent for methods
    s!"class {name} {\n${"".intercalate methodsStr.toList}}\n"
  | .importDecl _names _module => "// TODO: importDecl\n"
  | .raw js => js ++ "\n"

end Lean.Compiler.ToJS

-- Example Usage (you'd call this from a compiler pass or a #eval)
-- open Lean
-- open Lean.Compiler
-- open Lean.Compiler.LCNF
-- open Lean.Compiler.ToJS

-- private def testLCNFToJs (lcnfDecls : Array LCNF.Decl) : CoreM String := do
--   let jsDecls ← lcnfToJs lcnfDecls
--   return "\n".intercalate (jsDecls.map JsDecl.toCode).toList

-- You would get `lcnfDecls` from the Lean compilation pipeline after the LCNF stage.

/-
Copyright (c) 2024 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
prelude
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing

namespace Lean.IR.EmitJavascript
open ExplicitBoxing (requiresBoxedVersion mkBoxedName isBoxedName)

----------------------------

structure Context where
  env        : Environment
  modName    : Name
  -- jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]

abbrev M := ReaderT Context (EStateM String String)

def getEnv : M Environment := Context.env <$> read
def getModName : M Name := Context.modName <$> read
def getDecl (n : Name) : M Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration '{n}'"

@[inline] def emit {α : Type} [ToString α] (a : α) : M Unit :=
  modify fun out => out ++ toString a

@[inline] def emitLn {α : Type} [ToString α] (a : α) : M Unit := do
  emit a; emit "\n"

def emitLns {α : Type} [ToString α] (as : List α) : M Unit :=
  as.forM fun a => emitLn a

def argToJsString (x : Arg) : String :=
  match x with
  | Arg.var x => toString x
  | _         => "WHATTT???"

def emitArg (x : Arg) : M Unit :=
  emit (argToJsString x)

def throwInvalidExportName {α : Type} (n : Name) : M α :=
  throw s!"invalid export name '{n}'"

----------------------------

def emitFileHeader : M Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn ("// Module: " ++ toString modName)
  emit "// Imports:"
  env.imports.forM fun m => emit (" " ++ toString m)
  emitLn ""

def leanMainFn := "_lean_main"

def toCName (n : Name) : M String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

-- def toCType : IRType → String
--   | IRType.float      => "double"
--   | IRType.float32    => "float"
--   | IRType.uint8      => "uint8_t"
--   | IRType.uint16     => "uint16_t"
--   | IRType.uint32     => "uint32_t"
--   | IRType.uint64     => "uint64_t"
--   | IRType.usize      => "size_t"
--   | IRType.object     => "lean_object*"
--   | IRType.tobject    => "lean_object*"
--   | IRType.irrelevant => "lean_object*"
--   | IRType.struct _ _ => panic! "not implemented yet"
--   | IRType.union _ _  => panic! "not implemented yet"

partial def emitFnBody (b : FnBody) : M Unit := do
  emitLn "emitFnBody{"
  -- let declared ← declareVars b false
  -- if declared then emitLn ""
  -- emitBlock b
  -- emitJPs b
  emitLn "emitFnBody}"

def emitDeclAux (d : Decl) : M Unit := do
  let env ← getEnv
  let (_, jpMap) := mkVarJPMaps d
  withReader (fun ctx => ctx) do -- { ctx with jpMap := jpMap }) do
  unless hasInitAttr env d.name do
    match d with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let baseName ← toCName f;
      if xs.size == 0 then
        emit "xssize0 "
      else
        emit "xssize1 "  -- make symbol visible to the interpreter
      if xs.size > 0 then
        emit baseName;
        emit "(";
        if xs.size > closureMaxArgs && isBoxedName d.name then
          emit "xs.size > closureMaxArgs && isBoxedName d.name"
        else
          xs.size.forM fun i _ => do
            if i > 0 then emit ", "
            let x := xs[i]
            emit " "; emit x.x
        emit ")"
      else
        emit ("_init_" ++ baseName ++ "()")
      emitLn " {";
      withReader (fun ctx => { ctx with mainFn := f, mainParams := xs }) (emitFnBody b);
      emitLn "}"
    | _ => pure ()

def emitDecl (d : Decl) : M Unit := do
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux d
  catch err =>
    throw s!"{err}\ncompiling:\n{d}"

def emitFns : M Unit := do
  let env ← getEnv;
  let decls := getDecls env;
  decls.reverse.forM emitDecl

def emitMainFn : M Unit := do
  let d ← getDecl `main
  match d with
  | .fdecl (xs := xs) .. => do
    unless xs.size == 2 || xs.size == 1 do throw "invalid main function, incorrect arity when generating code"
    let env ← getEnv
    -- let usesLeanAPI := usesModuleFrom env `Lean
    -- if usesLeanAPI then
    --    emitLn "void lean_initialize();"
    -- else
    --    emitLn "void lean_initialize_runtime_module();";
    emitLn "
  var main = /* #__PURE__ */ (function () {
";
    -- if usesLeanAPI then
    --   emitLn "lean_initialize();"
    -- else
    --   emitLn "lean_initialize_runtime_module();"
    let modName ← getModName
    /- We disable panic messages because they do not mesh well with extracted closed terms.
       See issue #534. We can remove this workaround after we implement issue #467. -/
    emitLn "}"
    -- `IO _`
    let retTy := env.find? `main |>.get! |>.type |>.getForallBody
    -- either `UInt32` or `(P)Unit`
    let retTy := retTy.appArg!
    -- finalize at least the task manager to avoid leak sanitizer false positives from tasks outliving the main thread
    emitLn "}"
  | _     => throw "function declaration expected"

def hasMainFn : M Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : M Unit := do
  if (← hasMainFn) then emitMainFn

def main : M Unit := do
  emitFileHeader
  -- emitFnDecls
  emitFns
  -- emitInitFn
  emitMainFnIfNeeded
  -- emitFileFooter

end EmitJavascript

set_option diagnostics true

@[export lean_ir_emit_javascript]
def emitJavascript (env : Environment) (modName : Name) : Except String String := do
  dbg_trace env
  match (EmitJavascript.main { env := env, modName := modName }).run "" with
  | EStateM.Result.ok    _   s => Except.ok s
  | EStateM.Result.error err _ => Except.error err

end Lean.IR

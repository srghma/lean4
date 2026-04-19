/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jules
-/
module

prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.NameMangling
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.ExportAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.InitAttr

namespace Lean.Compiler.LCNF

namespace EmitEs6

structure State where
  out : String := ""
  funMangleCache : NameMap String := {}
  indent : Nat := 0

abbrev EmitM := ReaderT Context $ StateRefT State CompilerM

@[inline] def emit [EmitToString α] (a : α) : EmitM Unit := do
  modify fun s => { s with out := s.out ++ toString a }

def emitIndent : EmitM Unit := do
  let s ← get
  for _ in [:s.indent] do
    emit "  "

@[inline] def emitLn [EmitToString α] (a : α) : EmitM Unit := do
  emitIndent
  emit a
  emit "\n"

def withIndent (x : EmitM α) : EmitM α := do
  modify fun s => { s with indent := s.indent + 1 }
  let a ← x
  modify fun s => { s with indent := s.indent - 1 }
  return a

def toJsName (n : Name) : EmitM String := do
  if let some cached := (← get).funMangleCache[n]? then
    return cached
  let mangled ← go
  modify fun s => { s with funMangleCache := s.funMangleCache.insert n mangled }
  return mangled
where
  go : EmitM String := do
    let env ← getEnv
    match getExportNameFor? env n with
    | some (.str .anonymous s) => return s
    | some _                   => throwError "invalid export name '{n}'"
    | none                     => return n.mangle.replace "." "_"

def emitArg (a : Arg pu) : EmitM Unit := do
  match a with
  | .fvar fvarId => emit fvarId.name.mangle
  | .erased => emit "null"

def emitArgs (args : Array (Arg pu)) : EmitM Unit := do
  for i in [:args.size] do
    if i > 0 then emit ", "
    emitArg args[i]!

def emitLetValue (v : LetValue pu) : EmitM Unit := do
  match v with
  | .value (.natVal n) => emit (toString n ++ "n")
  | .value (.strVal s) => emit (s!"\"{s}\"")
  | .const declName _ as _ =>
    emit (← toJsName declName)
    emit "("
    emitArgs as
    emit ")"
  | .fvar fvarId as =>
    emit fvarId.name.mangle
    emit "("
    emitArgs as
    emit ")"
  | .fap fn as _ | .pap fn as _ =>
    emit (← toJsName fn)
    emit "("
    emitArgs as
    emit ")"
  | .ctor i as _ =>
    emit "lean_ctor("
    emit i.cidx
    emit ", "
    emitArgs as
    emit ")"
  | .box _ fvarId _ =>
    emit "lean_box("
    emit fvarId.name.mangle
    emit ")"
  | .unbox fvarId _ =>
    emit "lean_unbox("
    emit fvarId.name.mangle
    emit ")"
  | .proj _ i fvarId _ =>
    emit fvarId.name.mangle
    emit "["
    emit i
    emit "]"
  | _ => emit "/* unsupported value */"

partial def emitCode (code : Code pu) : EmitM Unit := do
  match code with
  | .let decl k =>
    emitIndent
    emit "const "
    emit decl.fvarId.name.mangle
    emit " = "
    emitLetValue decl.value
    emitLn ";"
    emitCode k
  | .return fvarId =>
    emitLn (s!"return {fvarId.name.mangle};")
  | .cases c =>
    emitLn (s!"switch (lean_obj_tag({c.discr.name.mangle})) \{")
    withIndent do
      for alt in c.alts do
        match alt with
        | .alt _ params k _ =>
          emitLn "/* alt params not supported yet */"
          emitCode k
        | .ctorAlt i k _ =>
          emitLn (s!"case {i.cidx}:")
          withIndent (emitCode k)
          emitLn "break;"
        | .default k =>
          emitLn "default:"
          withIndent (emitCode k)
    emitLn "}"
  | .jmp fvarId args =>
    emitIndent
    emit fvarId.name.mangle
    emit "("
    emitArgs args
    emitLn ");"
  | .jp decl k =>
    emitIndent
    emit "const "
    emit decl.fvarId.name.mangle
    emit " = ("
    for i in [:decl.params.size] do
      if i > 0 then emit ", "
      emit decl.params[i]!.fvarId.name.mangle
    emitLn ") => {"
    withIndent (emitCode decl.value)
    emitLn "};"
    emitCode k
  | .unreach _ => emitLn "throw \"unreachable\";"
  | _ => emitLn "/* other code */"

def emitDecl (decl : Decl pu) : EmitM Unit := do
  let name ← toJsName decl.name
  emit "export function "
  emit name
  emit "("
  for i in [:decl.params.size] do
    if i > 0 then emit ", "
    emit decl.params[i]!.fvarId.name.mangle
  emitLn ") {"
  withIndent (emitCode decl.value)
  emitLn "}"

def main (decls : Array (Decl pu)) : CompilerM String := do
  let (_, s) ← (for decl in decls do emitDecl decl).run {} |>.run { env := (← getEnv), terminal := #[] }
  return s.out

end EmitEs6

end Lean.Compiler.LCNF

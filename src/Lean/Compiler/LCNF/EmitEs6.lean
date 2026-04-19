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
    | none                     => return n.toString.replace "." "_"

def emitArg (a : Arg pu) : EmitM Unit := do
  match a with
  | .fvar fvarId => emit (fvarId.name.toString.replace "." "_")
  | .erased => emit "null"

def emitArgs (args : Array (Arg pu)) : EmitM Unit := do
  for i in [:args.size] do
    if i > 0 then emit ", "
    emitArg args[i]!

def getInlinedOp? (n : Name) : Option String :=
  if n == ``Nat.add then some "+"
  else if n == ``Nat.mul then some "*"
  else if n == ``Nat.sub then some "-"
  else if n == ``Nat.div then some "/"
  else if n == ``Nat.mod then some "%"
  else if n == ``Nat.beq then some "==="
  else if n == ``Nat.ble then some "<="
  else if n == ``Nat.lt then some "<"
  else none

def emitLetValue (v : LetValue pu) : EmitM Unit := do
  match v with
  | .value (.natVal n) => emit (toString n ++ "n")
  | .value (.strVal s) => emit (s!"\"{s}\"")
  | .const declName _ as _ =>
    if let some op := getInlinedOp? declName then
      if as.size == 2 then
        emit "("; emitArg as[0]!; emit s!" {op} "; emitArg as[1]!; emit ")"
      else
        emit (← toJsName declName); emit "("; emitArgs as; emit ")"
    else if declName == ``Bool.true then emit "true"
    else if declName == ``Bool.false then emit "false"
    else
      emit (← toJsName declName); emit "("; emitArgs as; emit ")"
  | .fvar fvarId as =>
    emit (fvarId.name.toString.replace "." "_"); emit "("; emitArgs as; emit ")"
  | .fap fn as _ | .pap fn as _ =>
    if let some op := getInlinedOp? fn then
       if as.size == 2 then
        emit "("; emitArg as[0]!; emit s!" {op} "; emitArg as[1]!; emit ")"
      else
        emit (← toJsName fn); emit "("; emitArgs as; emit ")"
    else
      emit (← toJsName fn); emit "("; emitArgs as; emit ")"
  | .ctor i as _ =>
    if i.name == ``Bool.true then emit "true"
    else if i.name == ``Bool.false then emit "false"
    else
      if as.isEmpty then
        emit s!"\{ tag: \"{(← toJsName i.name)}\" \}"
      else
        emit s!"\{ tag: \"{(← toJsName i.name)}\""
        for j in [:as.size] do
          emit s!", _{j+1}: "; emitArg as[j]!
        emit " \}"
  | .box _ fvarId _ => emit (fvarId.name.toString.replace "." "_")
  | .unbox fvarId _ => emit (fvarId.name.toString.replace "." "_")
  | .proj _ i fvarId _
  | .oproj i fvarId _
  | .uproj i fvarId _ =>
    emit (fvarId.name.toString.replace "." "_"); emit s!"._{i+1}"
  | .sproj i _ fvarId _ =>
    emit (fvarId.name.toString.replace "." "_"); emit s!"._{i+1}"
  | _ => emit "/* unsupported value */"

partial def emitCode (code : Code pu) : EmitM Unit := do
  match code with
  | .let decl k =>
    emitIndent
    emit "const "; emit (decl.fvarId.name.toString.replace "." "_"); emit " = "; emitLetValue decl.value; emitLn ";"
    emitCode k
  | .return fvarId =>
    emitLn (s!"return {fvarId.name.toString.replace "." "_"};")
  | .cases c =>
    let discr := c.discr.name.toString.replace "." "_"
    if c.typeName == ``Bool then
      for alt in c.alts do
        match alt with
        | .ctorAlt i k _ =>
          if i.name == ``Bool.true then
            emitIndent; emit s!"if ({discr}) "; emitLn "{"
            withIndent (emitCode k); emitIndent; emitLn "}"
          else
            emitIndent; emit "else "; emitLn "{"
            withIndent (emitCode k); emitIndent; emitLn "}"
        | .default k =>
          emitIndent; emit "else "; emitLn "{"
          withIndent (emitCode k); emitIndent; emitLn "}"
        | .alt .. => unreachable!
    else
      for i in [:c.alts.size] do
        let alt := c.alts[i]!
        if i > 0 then emit " else " else emitIndent
        match alt with
        | .ctorAlt i k _ =>
          emit s!"if ({discr}.tag === \"{(← toJsName i.name)}\") "
          emitLn "{"; withIndent (emitCode k); emitIndent; emit "}"
        | .alt _ _ k _ =>
          emitLn "{"; withIndent (emitCode k); emitIndent; emit "}"
        | .default k =>
          emitLn "{"; withIndent (emitCode k); emitIndent; emit "}"
      emitLn ""
  | .jmp fvarId args =>
    emitIndent; emit (fvarId.name.toString.replace "." "_"); emit "("; emitArgs args; emitLn ");"
  | .jp decl k =>
    emitIndent; emit "const "; emit (decl.fvarId.name.toString.replace "." "_"); emit " = (";
    for i in [:decl.params.size] do
      if i > 0 then emit ", "
      emit (decl.params[i]!.fvarId.name.toString.replace "." "_")
    emitLn ") => {"; withIndent (emitCode decl.value); emitIndent; emitLn "};"
    emitCode k
  | .oset f i y k _ =>
      emitIndent; emit (f.name.toString.replace "." "_"); emit s!"._{i+1} = "; emitArg y; emitLn ";"
      emitCode k
  | .uset f i y k _ =>
      emitIndent; emit (f.name.toString.replace "." "_"); emit s!"._{i+1} = "; emit (y.name.toString.replace "." "_"); emitLn ";"
      emitCode k
  | .sset f i _ y _ k _ =>
      emitIndent; emit (f.name.toString.replace "." "_"); emit s!"._{i+1} = "; emit (y.name.toString.replace "." "_"); emitLn ";"
      emitCode k
  | .unreach _ => emitLn "throw \"unreachable\";"
  | _ => emitLn "/* other code */"

def emitDecl (decl : Decl pu) : EmitM Unit := do
  let name ← toJsName decl.name
  emit "export const "; emit name; emit " = "
  if decl.params.isEmpty then
    emitLn "() => {"; withIndent (emitCode decl.value); emitIndent; emitLn "};"
  else
    emit "("
    for i in [:decl.params.size] do
      if i > 0 then emit ", "
      emit (decl.params[i]!.fvarId.name.toString.replace "." "_")
    emitLn ") => {"; withIndent (emitCode decl.value); emitIndent; emitLn "};"

def emitMain (modName : Name) (decls : Array (Decl .impure)) : EmitM Unit := do
  emitLn s!"// Generated by Lean ES6 emitter from module {modName}"
  for decl in decls do
    emitDecl decl

public def emitEs6 (modName : Name) (decls : Array (Decl .impure)) : CompilerM String := do
  let (_, s) ← (emitMain modName decls).run {} |>.run { env := (← getEnv), terminal := #[] }
  return s.out

end EmitEs6

public def emitEs6 (modName : Name) : CoreM String := do
  let decls ← getLocalImpureDecls
  EmitEs6.emitEs6 modName decls |>.run' {}

end Lean.Compiler.LCNF

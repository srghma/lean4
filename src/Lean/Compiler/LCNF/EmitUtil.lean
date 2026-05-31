/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.InitAttr

namespace Lean.Compiler.LCNF

structure CollectUsedDeclsState where
  visited : NameSet := {}
  localDecls : Array (Decl .impure) := #[]
  extSigs : Array (Signature .impure) := #[]

/--
Find all declarations that the declarations in `decls` transitively depend on. They are returned
partitioned into the declarations from the current module and declarations from other modules.
-/
public partial def collectUsedDecls (decls : Array Name) :
    CoreM (Array (Decl .impure) × Array (Signature .impure)) := do
  let (_, state) ← go decls |>.run {}
  return (state.localDecls, state.extSigs)
where
  go (names : Array Name) : StateRefT CollectUsedDeclsState CoreM Unit :=
    names.forM fun name => do
      if (← get).visited.contains name then return
      modify fun s => { s with visited := s.visited.insert name }
      if let some decl ← getLocalImpureDecl? name then
        decl.value.forCodeM (·.forM visitCode)
        modify fun s => { s with localDecls := s.localDecls.push decl }
        let env ← getEnv
        if let some initializer := getBuiltinInitFnNameFor? env decl.name <|> getInitFnNameFor? env decl.name then
          go #[initializer]
      else if let some sig ← getImpureSignature? name then
        modify fun s => { s with extSigs := s.extSigs.push sig }
      else
        panic! s!"collectUsedDecls: could not find declaration or signature for '{name}'"

  visitCode (code : Code .impure) : StateRefT CollectUsedDeclsState CoreM Unit := do
    match code with
    | .let decl k =>
      match decl.value with
      | .const declName .. | .fap declName .. | .pap declName .. =>
        go #[declName]
      | _ => pure ()
      visitCode k
    | .fun decl k .. | .jp decl k =>
      visitCode decl.value
      visitCode k
    | .cases c =>
      c.alts.forM fun alt => visitCode alt.getCode
    | .oset _ _ _ k .. | .uset _ _ _ k .. | .sset _ _ _ _ _ k .. | .setTag _ _ k ..
    | .inc _ _ _ _ k .. | .dec _ _ _ _ k .. | .del _ k .. =>
      visitCode k
    | .return .. | .jmp .. | .unreach .. => return ()

public def usesModuleFrom (env : Environment) (modulePrefix : Name) : Bool :=
  env.header.modules.any fun mod => mod.irPhases != .comptime && modulePrefix.isPrefixOf mod.module

end Lean.Compiler.LCNF

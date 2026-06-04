/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Data.Range.Basic
public import Lean.Meta.Basic
public import Lean.AddDecl

public section

namespace Lean

open Meta

namespace Meta

private partial def mkPiUnit (type unit : Expr) : MetaM Expr := do
  match type with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      mkForallFVars #[x] (← mkPiUnit (b.instantiate1 x) unit)
  | _ => pure unit

private partial def mkCasesOnFunUnit (type unit : Expr) : MetaM Expr := do
  match type with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      mkLambdaFVars #[x] (← mkCasesOnFunUnit (b.instantiate1 x) unit)
  | _ => pure unit

private partial def forallBody (type : Expr) : Expr :=
  match type with
  | .forallE _ _ b _ => forallBody b
  | _ => type

private def isTypeFormerArg (motiveIds : Array FVarId) (arg : Expr) : Bool :=
  match arg.getAppFn with
  | .fvar id => motiveIds.contains id
  | _ => false

private partial def withMinorParams
    (motiveIds : Array FVarId) (mainMotiveId : FVarId) (unit : Expr)
    (minorType : Expr) (isMain : Bool)
    (minorParams minorNonRecParams : Array Expr)
    (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  match minorType with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let body := b.instantiate1 x
      let argTarget := forallBody d
      if isTypeFormerArg motiveIds argTarget then
        if argTarget.getAppFn.fvarId! == mainMotiveId then
          withMinorParams motiveIds mainMotiveId unit body isMain
            (minorParams.push x) minorNonRecParams k
        else
          let newType ← mkPiUnit d unit
          withLocalDecl n bi newType fun newLocal => do
            withMinorParams motiveIds mainMotiveId unit body isMain
              (minorParams.push newLocal) minorNonRecParams k
      else
        withMinorParams motiveIds mainMotiveId unit body isMain
          (minorParams.push x) (if isMain then minorNonRecParams.push x else minorNonRecParams) k
  | _ => k minorParams minorNonRecParams minorType

private partial def processMinors
    (indNames : Array Name) (numParams numMotives numMinors : Nat)
    (recFVars : Array Expr) (motiveIds : Array FVarId) (mainMotiveId : FVarId) (unit star : Expr)
    (minorEntries : Array (Expr × Bool)) (minorIdx : Nat)
    (casesOnParams recArgs : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if h : minorIdx < minorEntries.size then
    let (minor, isMain) := minorEntries[minorIdx]
    let minorDecl ← minor.fvarId!.getDecl
    withMinorParams motiveIds mainMotiveId unit minorDecl.type isMain #[] #[] fun minorParams minorNonRecParams minorType => do
      if isMain then
        let newCType ← mkForallFVars minorNonRecParams minorType
        withLocalDecl minorDecl.userName minorDecl.binderInfo newCType fun newC => do
          let newCApp := mkAppN newC minorNonRecParams
          let recArg ← mkLambdaFVars minorParams newCApp
          processMinors indNames numParams numMotives numMinors recFVars motiveIds mainMotiveId unit star
            minorEntries (minorIdx + 1) (casesOnParams.push newC) (recArgs.push recArg) k
      else
        let recArg ← mkLambdaFVars minorParams star
        processMinors indNames numParams numMotives numMinors recFVars motiveIds mainMotiveId unit star
          minorEntries (minorIdx + 1) casesOnParams (recArgs.push recArg) k
  else
    k casesOnParams recArgs

private def mkCasesOnDecl (declName : Name) : MetaM Declaration := do
  let indInfo ← getConstInfoInduct declName
  let casesOnName := mkCasesOnName declName
  let recName := mkRecName declName
  let recInfo ← getConstInfoRec recName
  let recConstInfo ← getConstInfo recName
  let numIndices := recInfo.numIndices
  let numMinors := recInfo.numMinors
  let numMotives := recInfo.numMotives
  let numParams := recInfo.numParams
  let indNames := recInfo.all.toArray
  let lvls := recConstInfo.levelParams.map mkLevelParam
  let elimToProp := recConstInfo.levelParams.length == indInfo.levelParams.length
  let elimLvl := if elimToProp then Level.zero else lvls.head!
  let unit := mkConst ``PUnit [elimLvl]
  let star := mkConst ``PUnit.unit [elimLvl]
  let recConst := mkConst recName lvls
  forallTelescope recConstInfo.type fun recFVars recType => do
    let mut casesOnParams : Array Expr := #[]
    let mut recArgs : Array Expr := #[]
    for i in List.range numParams do
      casesOnParams := casesOnParams.push recFVars[i]!
      recArgs := recArgs.push recFVars[i]!
    let mut motiveIds : Array FVarId := #[]
    let mut mainMotiveId? : Option FVarId := none
    for j in List.range numMotives do
      let idx := numParams + j
      let motive := recFVars[idx]!
      motiveIds := motiveIds.push motive.fvarId!
      if j < indNames.size && indNames[j]! == declName then
        casesOnParams := casesOnParams.push motive
        recArgs := recArgs.push motive
        mainMotiveId? := some motive.fvarId!
      else
        recArgs := recArgs.push (← mkCasesOnFunUnit (← inferType motive) unit)
    let some mainMotiveId := mainMotiveId?
      | throwError "error in '{Name.mkStr declName casesOnSuffix}' generation, '{declName}' is not an inductive datatype"
    for i in List.range (numIndices + 1) do
      casesOnParams := casesOnParams.push recFVars[numParams + numMotives + numMinors + i]!

    let mut minorEntries : Array (Expr × Bool) := #[]
    let mut minorIdx := 0
    for indName in indNames do
      let currIndInfo ← getConstInfoInduct indName
      for _ctor in currIndInfo.ctors do
        minorEntries := minorEntries.push (recFVars[numParams + numMotives + minorIdx]!, indName == declName)
        minorIdx := minorIdx + 1
    for _ in List.range (numMinors - minorIdx) do
      minorEntries := minorEntries.push (recFVars[numParams + numMotives + minorIdx]!, false)
      minorIdx := minorIdx + 1

    processMinors indNames numParams numMotives numMinors recFVars motiveIds mainMotiveId unit star minorEntries 0 casesOnParams recArgs
      fun casesOnParams recArgs => do
        let mut recArgs := recArgs
        for i in List.range (numIndices + 1) do
          recArgs := recArgs.push recFVars[numParams + numMotives + numMinors + i]!
        let casesOnType ← mkForallFVars casesOnParams recType
        let casesOnValue ← mkLambdaFVars casesOnParams (mkAppN recConst recArgs)
        let decl ← mkDefinitionValInferringUnsafe
          (name        := casesOnName)
          (levelParams := recConstInfo.levelParams)
          (type        := casesOnType)
          (value       := casesOnValue)
          (hints       := ReducibilityHints.abbrev)
        pure (.defnDecl decl)

end Meta

def mkCasesOn (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkCasesOn (fun _ => return m!"{declName}") do
  let name := mkCasesOnName declName
  let decl ← mkCasesOnDecl declName
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  enableRealizationsForConst name

builtin_initialize
  registerTraceClass `Meta.mkCasesOn

end Lean

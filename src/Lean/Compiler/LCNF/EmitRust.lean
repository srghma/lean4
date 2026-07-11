/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Antigravity
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.NameMangling
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.ExportAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.ClosedTermCache
import Lean.Runtime
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.InitAttr
import Init.Omega
import Init.While
import Lean.Compiler.LCNF.SimpCase
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF

def leanMainFn := "_lean_main"

def leanh (name : String) : String :=
  s!"leanh::{name}"

def leanObjectTy : String :=
  leanh "LeanObject"

def leanObjectPtrTy : String :=
  s!"*mut {leanObjectTy}"

namespace ImpureType

def Lean.Expr.toRustType : Expr → String
  | float => "f64"
  | float32 => "f32"
  | bool => "bool"
  | uint8 => "u8"
  | uint16 => "u16"
  | uint32 => "u32"
  | uint64 => "u64"
  | usize => "usize"
  | object => leanObjectPtrTy
  | tagged => leanObjectPtrTy
  | tobject => leanObjectPtrTy
  | erased => leanObjectPtrTy
  | void => leanObjectPtrTy
  | _ => unreachable!

def Lean.Expr.unboxOpName (t : Expr) : String :=
  match t with
  | usize => "lean_unbox_usize"
  | uint32 => "lean_unbox_uint32"
  | uint64 => "lean_unbox_uint64"
  | float => "lean_unbox_float"
  | float32 => "lean_unbox_float32"
  | _ => "lean_unbox"

def Lean.Expr.boxOpName (t : Expr) : String :=
  match t with
  | usize => "lean_box_usize"
  | uint32 => "lean_box_uint32"
  | uint64 => "lean_box_uint64"
  | float => "lean_box_float"
  | float32 => "lean_box_float32"
  | _ => "lean_box"

def Lean.Expr.sprojOpName (t : Expr) : String :=
  match t with
  | float => "lean_ctor_get_float"
  | float32 => "lean_ctor_get_float32"
  | bool => "lean_ctor_get_uint8"
  | uint8 => "lean_ctor_get_uint8"
  | uint16 => "lean_ctor_get_uint16"
  | uint32 => "lean_ctor_get_uint32"
  | uint64 => "lean_ctor_get_uint64"
  | _ => unreachable!

def Lean.Expr.ssetOpName (t : Expr) : String :=
  match t with
  | float => "lean_ctor_set_float"
  | float32 => "lean_ctor_set_float32"
  | bool => "lean_ctor_set_uint8"
  | uint8 => "lean_ctor_set_uint8"
  | uint16 => "lean_ctor_set_uint16"
  | uint32 => "lean_ctor_set_uint32"
  | uint64 => "lean_ctor_set_uint64"
  | _ => unreachable!

def Lean.Expr.closedTermReadOpName (t : Expr) : String :=
  match t with
  | float => "lean_float_once"
  | float32 => "lean_float32_once"
  | bool => "lean_bool_once"
  | uint8 => "lean_uint8_once"
  | uint16 => "lean_uint16_once"
  | uint32 => "lean_uint32_once"
  | uint64 => "lean_uint64_once"
  | usize => "lean_usize_once"
  | object | tobject | tagged | void => "lean_obj_once"
  | _ => unreachable!

end ImpureType

open ImpureType

def defaultInitializer (t : Expr) : String :=
  match t with
  | float => "0.0"
  | float32 => "0.0f32"
  | bool => "false"
  | uint8 | uint16 | uint32 | uint64 | usize => "0"
  | _ => "core::ptr::null_mut()"

private def scalarPtrLiteral (b1 b2 b3 b4 b5 b6 b7 b8 : UInt8) : String :=
  let pack (b : UInt8) (shift : UInt64) : UInt64 := b.toUInt64 <<< shift
  let v := pack b1 0 ||| pack b2 8 ||| pack b3 16 ||| pack b4 24 |||
           pack b5 32 ||| pack b6 40 ||| pack b7 48 ||| pack b8 56
  s!"{v} as {leanObjectPtrTy}"

structure Context where
  localDecls : Array (Decl .impure)
  otherModuleDecls : Array (Signature .impure)
  modName : Name
  currFn : Name := default
  currParams : Array (Param .impure) := #[]
  inStateMachineLoop : Bool := false

structure State where
  buf : String := ""
  varMangleCache : Std.HashMap Name String := {}
  funMangleCache : Std.HashMap Name String := {}
  funInitMangleCache : Std.HashMap Name String := {}
  stateIds : Std.HashMap FVarId Nat := {}
  nextStateId : Nat := 1

abbrev EmitM := ReaderT Context StateRefT State CompilerM

@[inline] def getModName : EmitM Name := return (← read).modName

@[inline] def getModInitFn (phases : IRPhases) : EmitM String := do
  let pkg? := (← getEnv).getModulePackage?
  return mkModuleInitializationFunctionName (phases := phases) (← getModName) pkg?

@[inline] def getCurrFn : EmitM Name := return (← read).currFn

@[inline] def getCurrParams : EmitM (Array (Param .impure)) := return (← read).currParams

@[inline] def getLocalDecls : EmitM (Array (Decl .impure)) := return (← read).localDecls

@[inline] def getOtherModuleDecls : EmitM (Array (Signature .impure)) :=
  return (← read).otherModuleDecls

class EmitToString (α : Type) where
  toEmitString : α → EmitM String

instance (priority := low) [ToString α] : EmitToString α where
  toEmitString x := return toString x

instance : EmitToString Name where
  toEmitString v := do
    modifyGet fun s =>
      if let some mangled := s.varMangleCache[v]? then
        (mangled, s)
      else
        let mangled := v.mangle (pre := "v_")
        (mangled, { s with varMangleCache := s.varMangleCache.insert v mangled })

instance : EmitToString FVarId where
  toEmitString fvarId := do EmitToString.toEmitString (← getBinderName fvarId)

def addImportName (imports : Array String) (name : String) : Array String :=
  if imports.contains name then imports else imports.push name

def recordLeanhImport (_name : String) : EmitM Unit :=
  pure ()

def recordLeanhImports (names : Array String) : EmitM Unit := do
  for name in names do
    recordLeanhImport name

def Arg.toRustString (a : Arg .impure) : EmitM String := do
  match a with
  | .fvar fvarId => EmitToString.toEmitString fvarId
  | .erased =>
    return s!"{leanh "lean_box"}(0)"

instance : EmitToString (Arg .impure) where
  toEmitString a := a.toRustString

@[inline] def emit [EmitToString α] (a : α) : EmitM Unit := do
  let str ← EmitToString.toEmitString a
  modify fun out => { out with buf := out.buf ++ str }

@[inline] def emitLn [EmitToString α] (a : α) : EmitM Unit := do
  emit a; emit "\n"

@[inline]
def emitCApp1 {α : Type} [EmitToString α] (fn : String) (arg : α) : EmitM Unit := do
  emit (leanh fn); emit "("; emit arg; emit ")"

@[inline]
def emitCApp2 {α β : Type} [EmitToString α] [EmitToString β] (fn : String) (arg1 : α) (arg2 : β) :
    EmitM Unit := do
  emit (leanh fn); emit "("; emit arg1; emit ", "; emit arg2; emit ")"

@[inline]
def emitCApp3 {α β γ : Type} [EmitToString α] [EmitToString β] [EmitToString γ] (fn : String)
    (arg1 : α) (arg2 : β) (arg3 : γ) : EmitM Unit := do
  emit (leanh fn); emit "("; emit arg1; emit ", "; emit arg2; emit ", "; emit arg3; emit ")"

def toStringArgs (ys : Array (Arg .impure)) : EmitM (List String) :=
  ys.toList.mapM (·.toRustString)

def emitArgs (args : Array (Arg .impure)) : EmitM Unit := do
  for h : i in 0...args.size do
    if i > 0 then emit ", "
    emit args[i]

def emitLns [EmitToString α] (as : List α) : EmitM Unit :=
  as.forM fun a => emitLn a

@[inline] def withEmitBlock (x : EmitM α) : EmitM α := do
  emitLn "{"
  let ret ← x
  emitLn "}"
  return ret

def toHexDigit (c : Nat) : String :=
  if c < 10 then toString c else String.singleton (Char.ofNat (97 + c - 10))

def toHex (c : Nat) : String :=
  "\\x" ++ toHexDigit (c / 16) ++ toHexDigit (c % 16)

def quoteString (s : String) : String :=
  let q := "\"";
  let q := s.foldl
    (fun q c => q ++
      if c == '\n' then "\\n"
      else if c == '\r' then "\\r"
      else if c == '\t' then "\\t"
      else if c == '\\' then "\\\\"
      else if c == '\"' then "\\\""
      else if c.toNat <= 31 then
        toHex c.toNat
      else String.singleton c)
    q;
  q ++ "\""

def throwInvalidExportName (n : Name) : EmitM α :=
  throwError s!"invalid export name '{n}'"

def toCName (n : Name) : EmitM String := do
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
    | some _                   => throwInvalidExportName n
    | none                     => return if n == `main then leanMainFn else getSymbolStem env n

def emitCName (n : Name) : EmitM Unit :=
  toCName n >>= emit

def toCInitName (n : Name) : EmitM String := do
  if let some cached := (← get).funInitMangleCache[n]? then
    return cached
  let mangled ← go
  modify fun s => { s with funInitMangleCache := s.funInitMangleCache.insert n mangled }
  return mangled
where
  go : EmitM String := do
    let env ← getEnv;
    match getExportNameFor? env n with
    | some (.str .anonymous s) => return "_init_" ++ s
    | some _                   => throwInvalidExportName n
    | none                     => return "_init_" ++ getSymbolStem env n

def emitCInitName (n : Name) : EmitM Unit :=
  toCInitName n >>= emit

-- Returns the Rust crate name for well-known stdlib packages, or "" for user-defined packages.
def leanModuleToRustPackage (name : Name) : String :=
  let s := name.toString
  if s.startsWith "Init" then "lean_init"
  else if s.startsWith "Std"  then "lean_std"
  else if s.startsWith "Lean" then "lean_lean"
  else if s.startsWith "Lake" then "lean_lake"
  else ""

def leanModuleToRustPath (name : Name) : String :=
  (toString name).replace "." "::"

def UseGroups := Array (String × Array String)

def addUseItem (groups : UseGroups) (path : String) (item : String) : UseGroups := Id.run do
  let mut out := #[]
  let mut inserted := false
  for group in groups.toList do
    if group.1 == path then
      inserted := true
      if group.2.contains item then
        out := out.push group
      else
        out := out.push (group.1, group.2.push item)
    else
      out := out.push group
  if inserted then out else out.push (path, #[item])

def addUseItemFrom (groups : UseGroups) (root : String) (modName : Name) (item : String) :
    UseGroups :=
  addUseItem groups s!"{root}::{leanModuleToRustPath modName}" item

def useGroupsContainsItem (groups : UseGroups) (item : String) : Bool :=
  groups.any fun group => group.2.contains item

def collectDirectGroundArgDecls (arg : SimpleGroundArg) (s : NameSet) : NameSet :=
  match arg with
  | .reference declName => s.insert declName
  | .tagged .. | .rawReference .. => s

def collectDirectGroundArgsDecls (args : Array SimpleGroundArg) (s : NameSet) : NameSet :=
  args.foldl (init := s) fun s arg => collectDirectGroundArgDecls arg s

def collectDirectGroundDecls (ground : SimpleGroundExpr) (s : NameSet) : NameSet :=
  match ground with
  | .ctor (objArgs := objArgs) .. => collectDirectGroundArgsDecls objArgs s
  | .pap func args => collectDirectGroundArgsDecls args (s.insert func)
  | .nameMkStr args => args.foldl (init := s) fun s (ref, _) => s.insert ref
  | .reference declName => s.insert declName
  | .array elems => collectDirectGroundArgsDecls elems s
  | .string .. | .byteArray .. => s

def collectDirectLetValueDecls (value : LetValue .impure) (s : NameSet) : NameSet :=
  match value with
  | .const declName .. | .fap declName .. | .pap declName .. => s.insert declName
  | _ => s

mutual
partial def collectDirectFunDecls (decl : FunDecl .impure) (s : NameSet) : NameSet :=
  collectDirectCodeDecls decl.value s

partial def collectDirectCodeDecls (code : Code .impure) (s : NameSet) : NameSet :=
  match code with
  | .let decl k =>
    collectDirectCodeDecls k <| collectDirectLetValueDecls decl.value s
  | .jp decl k =>
    collectDirectCodeDecls k <| collectDirectFunDecls decl s
  | .cases c =>
    c.alts.foldl (init := s) fun s alt => collectDirectCodeDecls alt.getCode s
  | .oset (k := k) .. | .uset (k := k) .. | .sset (k := k) ..
  | .inc (k := k) .. | .dec (k := k) .. | .del (k := k) .. | .setTag (k := k) .. =>
    collectDirectCodeDecls k s
  | .jmp .. | .return .. | .unreach .. => s
end

def collectDirectDecls (env : Environment) (decl : Decl .impure) (s : NameSet) : NameSet :=
  if let some ground := getSimpleGroundExpr env decl.name then
    collectDirectGroundDecls ground s
  else
    match decl.value with
    | .code code => collectDirectCodeDecls code s
    | .extern .. => s

def collectDirectUsedDecls (env : Environment) (decls : Array (Decl .impure)) : NameSet :=
  decls.foldl (init := {}) fun s decl => collectDirectDecls env decl s

def formatUseGroup (path : String) (items : Array String) : String :=
  let items := items.qsort (· < ·)
  if h : items.size = 0 then
    ""
  else if h : items.size = 1 then
    s!"use {path}::{items[0]};"
  else
    "use " ++ path ++ "::{" ++ String.intercalate ", " items.toList ++ "};"

def emitUseGroups (groups : UseGroups) : EmitM Unit := do
  for group in groups.toList do
    let line := formatUseGroup group.1 group.2
    unless line.isEmpty do
      emitLn line

-- Collect the init function names that a phase's init fn needs to call.
def getInitFnNames (phases : IRPhases) : EmitM (List String) := do
  let env ← getEnv
  let allFns ← env.imports.filterMapM fun imp => do
    if phases != .all && imp.isMeta != (phases == .comptime) then
      return none
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index"
    let pkg? := env.getModulePackageByIdx? idx
    return some (mkModuleInitializationFunctionName
      (phases := if phases == .all then .all else if imp.isMeta then .runtime else phases)
      imp.module pkg?)
  return allFns.toList

def getLegacyInitFnNames : EmitM (List String) := do
  let env ← getEnv
  let allFns ← env.imports.filterMapM fun imp => do
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index"
    let pkg? := env.getModulePackageByIdx? idx
    return some (mkModuleInitializationFunctionName imp.module pkg?)
  return allFns.toList

def ctorScalarSizeExpression (usize : Nat) (ssize : Nat) : String :=
  if usize == 0 then
    s!"{ssize}"
  else if ssize == 0 then
    s!"core::mem::size_of::<usize>()*{usize}"
  else
    s!"core::mem::size_of::<usize>()*{usize} + {ssize}"

structure GroundState where
  auxCounter : Nat := 0

abbrev GroundM := StateRefT GroundState EmitM

partial def emitGroundDecl (decl : Decl .impure) (cppBaseName : String) : EmitM Unit := do
  let some ground := getSimpleGroundExpr (← getEnv) decl.name | unreachable!
  discard <| compileGround ground |>.run {}
where
  mkHeader {α : Type} [ToString α] (csSz : α) (other : Nat) (tag : Nat) : String :=
    s!"{leanh "LeanObject"} \{ rc: 0, cs_size: ({csSz}) as u16, other: {other}, tag: {tag} }"

  mkCtorHeader (numObjs : Nat) (usize : Nat) (ssize : Nat) (tag : Nat) : String :=
    let size := s!"core::mem::size_of::<{leanObjectTy}>() + core::mem::size_of::<{leanObjectPtrTy}>()*{numObjs} + {ctorScalarSizeExpression usize ssize}"
    mkHeader size numObjs tag

  compileGround (e : SimpleGroundExpr) : GroundM Unit := do
    let valueName ← compileGroundToValue e (root := true)
    if isClosedTermName (← getEnv) decl.name then
      emitLn <| s!"static mut {cppBaseName}: {leanObjectPtrTy} = core::ptr::addr_of!({valueName}) as {leanObjectPtrTy};"
    else
      emitLn <| s!"pub static mut {cppBaseName}: {leanObjectPtrTy} = core::ptr::addr_of!({valueName}) as {leanObjectPtrTy};"

  compileGroundToValue (e : SimpleGroundExpr) (root := false) : GroundM String := do
    match e with
    | .ctor cidx objArgs usizeArgs scalarArgs =>
      let (n, val) ← compileCtor cidx objArgs usizeArgs scalarArgs
      mkValueCLit s!"{leanh "LeanCtorObject"}<{n}>" val root
    | .string data =>
      let leanStringTag := 249
      let header := mkHeader 0 0 leanStringTag
      let size := data.utf8ByteSize + 1 -- null byte
      let length := data.length
      let dataBytes := String.intercalate ", " <| (data.toUTF8.data.toList.map (fun b => toString b.toNat))
      let dataWithNull := if dataBytes.isEmpty then "0" else dataBytes ++ ", 0"
      let type := leanh "LeanStringObject" ++ "<" ++ toString size ++ ">"
      let value := (s!"{leanh "LeanStringObject"} \{ m_header: {header}, m_size: {size}, m_capacity: {size}, m_length: {length}, m_data: [") ++ dataWithNull ++ "]" ++ "}"
      mkValueCLit
        type
        value
        root
    | .pap func args =>
      let numFixed := args.size
      let leanClosureTag := 245
      let header := mkHeader s!"core::mem::size_of::<{leanObjectTy}>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<{leanObjectPtrTy}>()*{numFixed}" 0 leanClosureTag
      let funPtr := s!"{← toCName func} as *const core::ffi::c_void"
      let arity := (← getImpureSignature? func).get!.params.size
      let args ← args.mapM groundArgToCLit
      let argArray := String.intercalate "," args.toList
      mkValueCLit
        s!"{leanh "LeanClosureObject"}<{numFixed}>"
        s!"{leanh "LeanClosureObject"} \{ m_header: {header}, m_fun: {funPtr}, m_arity: {arity}, m_num_fixed: {numFixed}, m_objs: [{argArray}] }"
        root
    | .nameMkStr args =>
      let (n, obj) ← groundNameMkStrToCLit args
      mkValueCLit s!"{leanh "LeanCtorObject"}<{n}>" obj root
    | .array elems =>
      let leanArrayTag := 246
      let header := mkHeader s!"core::mem::size_of::<{leanObjectTy}>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<{leanObjectPtrTy}>()*{elems.size}" 0 leanArrayTag
      let elemLits ← elems.mapM groundArgToCLit
      let dataArray := String.intercalate "," elemLits.toList
      mkValueCLit
        s!"{leanh "LeanArrayObject"}<{elems.size}>"
        s!"{leanh "LeanArrayObject"} \{ m_header: {header}, m_size: {elems.size}, m_capacity: {elems.size}, m_data: [{dataArray}] }"
        root
    | .byteArray data =>
      let leanScalarArrayTag := 248
      let elemSize : Nat := 1
      let header := mkHeader s!"core::mem::size_of::<{leanObjectTy}>() + core::mem::size_of::<usize>()*2 + {data.size}" elemSize leanScalarArrayTag
      let dataLits := data.map toString
      let dataArray := String.intercalate "," dataLits.toList
      mkValueCLit
        s!"{leanh "LeanScalarArray"}<{data.size}>"
        s!"{leanh "LeanScalarArray"} \{ m_header: {header}, m_size: {data.size}, m_capacity: {data.size}, m_data: [{dataArray}] }"
        root
    | .reference refDecl => findValueDecl refDecl

  mkValueName (name : String) : String :=
    name ++ "_value"

  mkAuxValueName (name : String) (idx : Nat) : String :=
    mkValueName name ++ s!"_aux_{idx}"

  mkAuxDecl (type value : String) : GroundM String := do
    let idx ← modifyGet fun s => (s.auxCounter, { s with auxCounter := s.auxCounter + 1 })
    let name := mkAuxValueName cppBaseName idx
    emitLn <| s!"static {name}: {type} = {value};"
    return name

  mkValueCLit (type value : String) (root : Bool) : GroundM String := do
    if root then
      let valueName := mkValueName cppBaseName
      emitLn <| s!"pub static {valueName}: {type} = {value};"
      return valueName
    else
      mkAuxDecl type value

  groundNameMkStrToCLit (args : Array (Name × UInt64)) : GroundM (Nat × String) := do
    assert! args.size > 0
    if h : args.size = 1 then
      let (ref, hash) := args[0]
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.tagged 0, .reference ref] #[] hash
    else
      let (ref, hash) := args.back!
      let args := args.pop
      let (auxN, lit) ← groundNameMkStrToCLit args
      let auxName ← mkAuxDecl s!"{leanh "LeanCtorObject"}<{auxN}>" lit
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.rawReference auxName, .reference ref] #[] hash

  groundArgToCLit (a : SimpleGroundArg) : GroundM String := do
    match a with
    | .tagged val => return s!"((( {val} as usize) << 1) | 1) as {leanObjectPtrTy}"
    | .reference decl =>
        return s!"core::ptr::addr_of!({← findValueDecl decl}) as {leanObjectPtrTy}"
    | .rawReference decl => return s!"core::ptr::addr_of!({decl}) as {leanObjectPtrTy}"

  -- Follow reference chains until a decl with its own _value is found.
  -- Decls whose ground expr is `.reference` have no own _value static;
  -- only decls with `.ctor`, `.string`, `.array`, etc. get a _value.
  findValueDecl (n : Name) : GroundM String := do
    let env ← getEnv
    match getSimpleGroundExpr env n with
    | some (.reference refDecl) => findValueDecl refDecl
    | some _ => return mkValueName (← toCName n)
    | none => toCName n

  compileCtor (cidx : Nat) (objArgs : Array SimpleGroundArg) (usizeArgs : Array UInt64) (scalarArgs : Array UInt8) : GroundM (Nat × String) := do
    let numFixed := objArgs.size + usizeArgs.size
    let header := mkCtorHeader numFixed usizeArgs.size scalarArgs.size cidx
    let objArgs ← objArgs.mapM groundArgToCLit
    let usizeArgs : Array String := usizeArgs.map fun val => s!"({val} as {leanObjectPtrTy})"
    let packedScalars ← packScalarArgs scalarArgs
    let totalObjs := numFixed + packedScalars.size
    let argArray := String.intercalate "," (objArgs ++ usizeArgs ++ packedScalars).toList
    return (totalObjs, s!"{leanh "LeanCtorObject"} \{ m_header: {header}, m_objs: [{argArray}] }")

  packScalarArgs (scalarArgs : Array UInt8) : GroundM (Array String) := do
    let numU64s := (scalarArgs.size + 7) / 8
    let mut packed := #[]
    for idx in 0...numU64s do
      let b1 := scalarArgs.getD (idx * 8) 0
      let b2 := scalarArgs.getD (idx * 8 + 1) 0
      let b3 := scalarArgs.getD (idx * 8 + 2) 0
      let b4 := scalarArgs.getD (idx * 8 + 3) 0
      let b5 := scalarArgs.getD (idx * 8 + 4) 0
      let b6 := scalarArgs.getD (idx * 8 + 5) 0
      let b7 := scalarArgs.getD (idx * 8 + 6) 0
      let b8 := scalarArgs.getD (idx * 8 + 7) 0
      let lit := scalarPtrLiteral b1 b2 b3 b4 b5 b6 b7 b8
      packed := packed.push lit
    return packed

def toOnceTokenName (cppBaseName : String) : String :=
  s!"{cppBaseName}_once"

@[inline]
def paramsWithoutVoid (ps : Array (Param .impure)) :=
  ps.filter (!·.type.isVoid)

@[inline]
def paramsWithoutErased (ps : Array (Param .impure)) :=
  ps.filter (!·.type.isErased)

def emitFileHeader (body : String) : EmitM Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn s!"// Module: {modName}"
  emit "// Imports:"
  env.imports.forM fun m => emit (" " ++ toString m.module)
  emitLn ""
  let mut useGroups : UseGroups := #[]
  let mut localDefinedNames : Array String := #[]
  for decl in (← getLocalDecls) do
    match decl.value with
    | .extern .. => pure ()
    | .code .. =>
      if !(hasInitAttr env decl.name || isSimpleGroundDecl env decl.name) then
        localDefinedNames := addImportName localDefinedNames (← toCName decl.name)
  -- 1. Direct imports: imported module initialization functions.
  let neededInitFns ←
    if env.header.isModule then
      pure <| (← getInitFnNames .runtime) ++ (← getInitFnNames .comptime) ++ (← getLegacyInitFnNames)
    else
      getInitFnNames .all
  for imp in env.imports do
    let depMod := imp.module
    let some idx := env.getModuleIdx? depMod
      | throwError "(internal) import without module index"
    let pkg? := env.getModulePackageByIdx? idx
    for fnName in #[
        mkModuleInitializationFunctionName (phases := .runtime) depMod pkg?,
        mkModuleInitializationFunctionName (phases := .comptime) depMod pkg?,
        mkModuleInitializationFunctionName (phases := .all) depMod pkg?
      ] do
      if neededInitFns.contains fnName then
        useGroups := addUseItemFrom useGroups "crate::r#gen" depMod fnName
  -- 2. otherModuleDecls (handles inlined transitive refs).
  let directlyUsedDecls := collectDirectUsedDecls env (← getLocalDecls)
  for sig in (← getOtherModuleDecls) do
    if directlyUsedDecls.contains sig.name && (getExternNameFor env `c sig.name).isNone then
      if let some idx := env.getModuleIdxFor? sig.name then
        if let some depMod := env.header.moduleNames[idx]? then
          let item ← toCName sig.name
          if body.contains item && !useGroupsContainsItem useGroups item then
            useGroups := addUseItemFrom useGroups "crate::r#gen" depMod item
  -- 3. Imports for declarations with runtime symbol names.
  --    `@[extern]` names are imported through the local per-crate ffi module.
  for decl in (← getLocalDecls) do
    if let some externName := getExternNameFor env `c decl.name then
      if !decl.params.isEmpty then
        if body.contains externName && !localDefinedNames.contains externName && !useGroupsContainsItem useGroups externName then
          useGroups := addUseItem useGroups "crate::ffi" externName
  for sig in (← getOtherModuleDecls) do
    if let some externName := getExternNameFor env `c sig.name then
      if let some idx := env.getModuleIdxFor? sig.name then
        if (env.header.moduleNames[idx]?).isSome then
          if !sig.params.isEmpty then
            if body.contains externName && !localDefinedNames.contains externName && !useGroupsContainsItem useGroups externName then
              useGroups := addUseItem useGroups "crate::ffi" externName
  emitUseGroups useGroups

def offsetExpression (i : Nat) (offset : Nat) : String :=
  if i > 0 then
    if offset > 0 then
      s!"(core::mem::size_of::<{leanObjectPtrTy}>()*{i} + {offset}) as u32"
    else
      s!"(core::mem::size_of::<{leanObjectPtrTy}>()*{i}) as u32"
  else
    s!"{offset} as u32"

def isTailCall (code : Code .impure) : EmitM Bool :=
  match code with
  | .let { fvarId := fvarId, value := .fap declName _, .. } (.return fvarId') =>
    return fvarId == fvarId' && (← getCurrFn) == declName
  | _ => return false

def getOrAssignStateId (fvarId : FVarId) : EmitM Nat := do
  let s ← get
  if let some id := s.stateIds.get? fvarId then
    return id
  else
    let id := s.nextStateId
    set { s with stateIds := s.stateIds.insert fvarId id, nextStateId := id + 1 }
    return id

partial def assignStateIds (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp decl k =>
    let _ ← getOrAssignStateId decl.fvarId
    assignStateIds decl.value
    assignStateIds k
  | .let _ k | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => assignStateIds k
  | .cases cs => cs.alts.forM (assignStateIds ·.getCode)
  | .return _ | .jmp _ _ | .unreach _ => return ()

partial def hasControlFlow (code : Code .impure) : EmitM Bool := do
  let rec go (code : Code .impure) : EmitM Bool := do
    match code with
    | .jp .. => return true
    | .let _ k =>
      let isTail ← isTailCall code
      if isTail then
        return true
      else
        go k
    | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
    | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => go k
    | .cases cs => cs.alts.anyM (go ·.getCode)
    | .return _ | .jmp _ _ | .unreach _ => return false
  go code

private def emitVarDecl (binderName : Name) (type : Expr) : EmitM Unit := do
  emit "let mut "; emit binderName; emit s!": {type.toRustType} = {defaultInitializer type}; "

private def emitParamDecls (ps : Array (Param .impure)) : EmitM Unit :=
  ps.forM fun p => emitVarDecl p.binderName p.type

def declareVars (code : Code .impure) : EmitM Bool :=
  go code false
where
  go (code : Code .impure) (didChange : Bool) : EmitM Bool := do
    match code with
    | .let decl k =>
      let isTail ← isTailCall code
      if isTail then
        return didChange
      else
        emitVarDecl decl.binderName decl.type
        go k true
    | .jp decl k =>
      emitParamDecls decl.params
      go k (didChange || !decl.params.isEmpty)
    | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
    | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => go k didChange
    | .cases .. | .return .. | .jmp .. | .unreach .. => return didChange

-- Like declareVars but also recurses into .cases alts and .jp bodies,
-- so ALL variables across all states of a state-machine function are hoisted.
partial def declareAllVars (code : Code .impure) : EmitM Bool :=
  go code false
where
  go (code : Code .impure) (didChange : Bool) : EmitM Bool := do
    match code with
    | .let decl k =>
      let isTail ← isTailCall code
      if isTail then
        return didChange
      else
        emitVarDecl decl.binderName decl.type
        go k true
    | .jp decl k =>
      emitParamDecls decl.params
      let dc1 ← go decl.value (didChange || !decl.params.isEmpty)
      go k dc1
    | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
    | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => go k didChange
    | .cases cs =>
      let mut dc := didChange
      for alt in cs.alts do
        dc ← go alt.getCode dc
      return dc
    | .return .. | .jmp .. | .unreach .. => return didChange

def emitLetDecl (decl : LetDecl .impure) : EmitM Unit := do
  match decl.value with
  | .ctor info args => emitCtor info args
  | .reset n fvarId => emitReset n fvarId
  | .reuse fvarId info update args => emitReuse fvarId info update args
  | .oproj i fvarId => emitOproj i fvarId
  | .uproj i fvarId => emitUproj i fvarId
  | .sproj n offset fvarId => emitSproj n offset fvarId
  | .fap fn args => emitFap fn args
  | .pap fn args => emitPap fn args
  | .fvar fvarId args => emitAp fvarId args
  | .box ty fvarId => emitBox ty fvarId
  | .unbox fvarId => emitUnbox fvarId
  | .isShared fvarId => emitIsShared fvarId
  | .lit v => emitLit v
  | .erased => emitErased
where
  emitAllocCtor (info : CtorInfo) : EmitM Unit :=
    emitCApp3 "lean_alloc_ctor" info.cidx info.size s!"({ctorScalarSizeExpression info.usize info.ssize}) as u32"

  emitCtorSetArgs (targetId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    for h : i in 0...args.size do
      let arg := args[i]
      emitCApp3 "lean_ctor_set" targetId i arg; emitLn ";"

  emitCtor (info : CtorInfo) (args : Array (Arg .impure)) : EmitM Unit := do
    if decl.type == ImpureType.bool && info.size == 0 && info.usize == 0 && info.ssize == 0 then do
      withEmitAssignment do
        emit (if info.cidx == 0 then "false" else "true")
    else if info.size == 0 && info.usize == 0 && info.ssize == 0 then do
      withEmitAssignment do emitCApp1 "lean_box" info.cidx
    else do
      withEmitAssignment do emitAllocCtor info
      emitCtorSetArgs decl.fvarId args

  emitReset (n : Nat) (fvarId : FVarId) : EmitM Unit := do
    emit "if "; emitCApp1 "lean_is_exclusive" fvarId
    withEmitBlock do
      for i in 0...n do
        emitCApp2 "lean_ctor_release" fvarId i; emitLn ";"
      withEmitAssignment do emit fvarId
    emit "else"
    withEmitBlock do
      emitCApp1 "lean_dec_ref" fvarId; emitLn ";"
      withEmitAssignment do
        emit s!"{leanh "lean_box"}(0)"

  emitReuse (fvarId : FVarId) (info : CtorInfo) (update : Bool) (args : Array (Arg .impure)) :
      EmitM Unit := do
    emit "if "; emitCApp1 "lean_is_scalar" fvarId; emit " != 0"
    withEmitBlock do
      withEmitAssignment do emitAllocCtor info
    emit "else"
    withEmitBlock do
      withEmitAssignment do emit fvarId
      if update then
        emitCApp2 "lean_ctor_set_tag" decl.fvarId info.cidx; emitLn ";"
    emitCtorSetArgs decl.fvarId args

  emitOproj (i : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp2 "lean_ctor_get" fvarId i

  emitUproj (i : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp2 "lean_ctor_get_usize" fvarId i

  emitSproj (n : Nat) (offset : Nat) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      if decl.type == ImpureType.bool then
        emit "("
        emitCApp2 decl.type.sprojOpName fvarId (offsetExpression n offset)
        emit " != 0)"
      else
        emitCApp2 decl.type.sprojOpName fvarId (offsetExpression n offset)

  emitLeanFunReference (ty : Expr) (f : Name) : EmitM Unit := do
    let env ← getEnv
    if isSimpleGroundDecl env f then
      emit s!"{← toCName f}"
    else if isClosedTermName env f then
      let cname ← toCName f
      let cnameRef := s!"core::ptr::addr_of_mut!({cname})"
      let tokenRef := s!"core::ptr::addr_of_mut!({toOnceTokenName cname})"
      let initName ← toCInitName f
      emitCApp3 ty.closedTermReadOpName cnameRef tokenRef initName
    else
      emitCName f

  emitFap (fn : Name) (args : Array (Arg .impure)) : EmitM Unit := do
    let some sig ← getImpureSignature? fn | unreachable!
    let ps := sig.params
    withEmitAssignment do
      let castBoolResult := decl.type == ImpureType.bool && sig.type.isConstOf ``Bool
      match getExternAttrData? (← getEnv) fn |>.bind (getExternEntryFor · `c) with
      | some (.standard _ fn) =>
        if castBoolResult then
          emit "("
        let (_, args) :=
          ps.zip args
            |>.filter (fun (p, _) => !(p.type.isVoid || p.type.isErased))
            |>.unzip
        emit fn
        emit "("
        for h : i in 0...args.size do
          if i > 0 then emit ", "
          emit args[i]
        emit ")"
        if castBoolResult then
          emit " != 0)"
      | some (.inline _ pat) =>
        if castBoolResult then
          emit "("
        emit (expandExternPattern pat (← toStringArgs args))
        if castBoolResult then
          emit " != 0)"
      | some .opaque | none =>
        emitLeanFunReference decl.type fn
        if args.size > 0 then
          let (_, args) :=
            ps.zip args
              |>.filter (fun (p, _) => !p.type.isVoid)
              |>.unzip
          emit "("; emitArgs args; emit ")"
      | _ => throwError s!"failed to emit extern application '{fn}'"

  emitPap (fn : Name) (args : Array (Arg .impure)) : EmitM Unit := do
    let some sig ← getImpureSignature? fn | unreachable!
    let arity := sig.params.size
    withEmitAssignment do
      emitCApp3 "lean_alloc_closure" s!"{← toCName fn} as *mut core::ffi::c_void" arity args.size
    for h : i in 0...args.size do
      let arg := args[i]
      emitCApp3 "lean_closure_set" decl.fvarId i arg; emitLn ";"

  emitAp (fvarId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    assert! !args.isEmpty
    if args.size > closureMaxArgs then
      withEmitBlock do
        emit "let mut _aargs = ["; emitArgs args; emitLn "];"
        let fvarIdStr ← EmitToString.toEmitString fvarId
        withEmitAssignment do
          emit s!"{leanh "lean_apply_m"}({fvarIdStr}, {args.size}, _aargs.as_mut_ptr())"
    else
      withEmitAssignment do
        emit s!"{leanh s!"lean_apply_{args.size}"}("; emit fvarId; emit ", "; emitArgs args; emit ")"

  emitBox (ty : Expr) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      if ty == ImpureType.bool || ty == ImpureType.uint8 || ty == ImpureType.uint16 then do
        emit (leanh ty.boxOpName); emit "(("; emit fvarId; emit ") as usize)"
      else
        emitCApp1 ty.boxOpName fvarId

  emitUnbox (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      let ty := decl.type
      if ty == ImpureType.bool then do
        emit "("; emit (leanh ty.unboxOpName); emit "("; emit fvarId; emit ") != 0)"
      else if ty == ImpureType.uint8 || ty == ImpureType.uint16 then do
        emit "("; emit (leanh ty.unboxOpName); emit("("); emit fvarId; emit ") as "; emit ty.toRustType; emit ")"
      else
        emitCApp1 ty.unboxOpName fvarId

  emitIsShared (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emit s!"(!{leanh "lean_is_exclusive"}("; emit fvarId; emit ")) as u8"

  emitLit (v : LitValue) : EmitM Unit := do
    withEmitAssignment do
      match v with
      | .uint8 v | .uint16 v | .uint32 v => emit v
      | .uint64 v => emit v; emit "u64"
      | .usize v => emit v; emit "usize"
      | .nat v =>
        if v < UInt32.size then do
          emit s!"{leanh "lean_unsigned_to_nat"}("; emit v; emit ")"
        else do
          emit s!"{leanh "lean_cstr_to_nat"}(b\""; emit v; emit "\\0\".as_ptr().cast())"
      | .str v =>
        emitCApp3 "lean_mk_string_unchecked" s!"b\"{quoteString v}\\0\".as_ptr().cast()" v.utf8ByteSize v.length

  emitErased : EmitM Unit := do
    withEmitAssignment do
      emit s!"{leanh "lean_box"}(0)"

  emitLhs (binderName : Name) : EmitM Unit := do
    emit binderName; emit " = "

  withEmitAssignment {α : Type} (x : EmitM α) : EmitM α := do
    emitLhs decl.binderName
    let ret ← x
    emitLn ";"
    return ret

def emitTailCall (decl : LetDecl .impure) : EmitM Unit := do
  let .fap _ args := decl.value | unreachable!
  let ps ← getCurrParams
  assert! ps.size == args.size
  let (ps, args) := ps.zip args |>.filter (fun (p, _) => !p.type.isVoid) |>.unzip
  if overwriteParam ps args then
    withEmitBlock do
      for h : i in 0...ps.size do
        let p := ps[i]
        let arg := args[i]!
        unless paramEqArg p arg do
          emit "let _tmp_"; emit i; emit ": "; emit p.type.toRustType; emit " = "; emit arg; emitLn ";"

      for h : i in 0...ps.size do
        let p := ps[i]
        let arg := args[i]!
        unless paramEqArg p arg do
          emit p.binderName; emit " = _tmp_"; emit i; emitLn ";"
  else
    for p in ps, arg in args do
      unless paramEqArg p arg do
        emit p.binderName; emit " = "; emit arg; emitLn ";"
  emitLn "state = 0; continue;"
where
  overwriteParam (ps : Array (Param .impure)) (args : Array (Arg .impure)) : Bool := Id.run do
    for h1 : i in 0...ps.size do
      let p := ps[i]
      for h2 : j in (i+1)...args.size do
        if paramEqArg p args[j] then
          return true
    return false

  paramEqArg (p : Param .impure) (arg : Arg .impure) : Bool :=
    match arg with
    | .fvar fvarId => p.fvarId == fvarId
    | .erased => false

mutual

partial def emitBasicBlock (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp (k := k) .. => emitBasicBlock k
  | .let decl k =>
    let isTail ← isTailCall code
    if isTail then
      emitTailCall decl
    else
      emitLetDecl decl
      emitBasicBlock k
  | .inc fvarId n check persistent k =>
    unless persistent do emitInc fvarId n check
    emitBasicBlock k
  | .dec fvarId n check persistent objs? k =>
    unless persistent do emitDec fvarId n check objs?
    emitBasicBlock k
  | .del fvarId k =>
    emitDel fvarId
    emitBasicBlock k
  | .setTag fvarId cidx k =>
    emitSetTag fvarId cidx
    emitBasicBlock k
  | .oset fvarId i y k =>
    emitOset fvarId i y
    emitBasicBlock k
  | .uset fvarId i y k =>
    emitUset fvarId i y
    emitBasicBlock k
  | .sset fvarId i offset y ty k =>
    emitSset fvarId i offset y ty
    emitBasicBlock k
  | .cases cs => emitCases cs
  | .return fvarId => emitReturn fvarId
  | .jmp fvarId args => emitJmp fvarId args
  | .unreach .. => emitUnreach
where
  emitInc (fvarId : FVarId) (n : Nat) (check : Bool) : EmitM Unit := do
    if n == 1 then
      let incFn := if check then "lean_inc" else "lean_inc_ref"
      emitCApp1 incFn fvarId
    else
      let incFn := if check then "lean_inc_n" else "lean_inc_ref_n"
      emitCApp2 incFn fvarId n
    emitLn ";"

  emitDec (fvarId : FVarId) (n : Nat) (check : Bool) (objs? : Option Nat) : EmitM Unit := do
    assert! n == 1
    match objs? with
    | some objs =>
      emitCApp2 "lean_dec_ref_known" fvarId objs
    | none =>
      let decFn := if check then "lean_dec" else "lean_dec_ref"
      emitCApp1 decFn fvarId
    emitLn ";"

  emitDel (fvarId : FVarId) : EmitM Unit := do
    emitCApp1 "lean_del_object" fvarId
    emitLn ";"

  emitSetTag (fvarId : FVarId) (cidx : Nat) : EmitM Unit := do
    emitCApp2 "lean_ctor_set_tag" fvarId cidx
    emitLn ";"

  emitOset (fvarId : FVarId) (i : Nat) (y : Arg .impure) : EmitM Unit := do
    emitCApp3 "lean_ctor_set" fvarId i y
    emitLn ";"

  emitUset (fvarId : FVarId) (i : Nat) (y : FVarId) : EmitM Unit := do
    emitCApp3 "lean_ctor_set_usize" fvarId i y
    emitLn ";"

  emitSset (fvarId : FVarId) (i : Nat) (offset : Nat) (y : FVarId) (ty : Expr) : EmitM Unit := do
    if ty == ImpureType.bool then
      emitCApp3 ty.ssetOpName fvarId (offsetExpression i offset) s!"({y} as u8)"
    else
      emitCApp3 ty.ssetOpName fvarId (offsetExpression i offset) y
    emitLn ";"

  isIf (cs : Cases .impure) : EmitM (Option (Nat × Code .impure × Code .impure)) := do
    if h : cs.alts.size = 2 then
      match cs.alts[0] with
      | .ctorAlt info k => return some (info.cidx, k, cs.alts[1].getCode)
      | _ => return none
    else
      return none

  emitTag (fvarId : FVarId) : EmitM Unit := do
    let type ← getType fvarId
    if type.isObj then do
      emitCApp1 "lean_obj_tag" fvarId
    else
      emit fvarId

  emitCases (cs : Cases .impure) : EmitM Unit := do
    match ← isIf cs with
    | some (tag, t, e) =>
      emit "if "; emitTag cs.discr; emit " == "; emit tag; emitLn " {"
      emitCode t
      emitLn "} else {"
      emitCode e
      emitLn "}"
    | none =>
      emit "match "; emitTag cs.discr; emitLn ""
      withEmitBlock do
        let alts := ensureHasDefault cs.alts
        alts.forM fun alt => do
          match alt with
          | .ctorAlt info k =>
            emit info.cidx; emitLn " => {"
            emitCode k
            emitLn "}"
          | .default k =>
            emitLn "_ => {"
            emitCode k
            emitLn "}"

  emitReturn (fvarId : FVarId) : EmitM Unit := do
    emit "return "; emit fvarId; emitLn ";"

  emitJmp (fvarId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    let some jpDecl ← findFunDecl? (pu := .impure) fvarId | unreachable!
    let ps := jpDecl.params
    if args.size != ps.size then
      throwError "invalid jump"
    for arg in args, p in ps do
      emit p.binderName; emit " = "; emit arg; emitLn ";"
    let id ← getOrAssignStateId fvarId
    emitLn s!"state = {id}; continue;"

  emitUnreach : EmitM Unit := do
    emitLn "core::hint::unreachable_unchecked();"

partial def emitJoinPoints (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp decl k =>
    let id ← getOrAssignStateId decl.fvarId
    emit id; emitLn " => {"
    emitCode decl.value
    emitLn "}"
    emitJoinPoints k
  | .let (k := k) .. | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => emitJoinPoints k
  | .cases cs => cs.alts.forM (fun alt => emitJoinPoints alt.getCode)
  | .return .. | .jmp .. | .unreach .. => return ()

-- Like emitJoinPoints but uses emitBasicBlock (no var declarations) for state machine.
partial def emitJoinPointsBody (code : Code .impure) : EmitM Unit := do
  match code with
  | .jp decl k =>
    let id ← getOrAssignStateId decl.fvarId
    emit id; emitLn " => {"
    emitBasicBlock decl.value
    emitLn "}"
    -- Also recurse into the jp body: it may contain nested jp definitions.
    emitJoinPointsBody decl.value
    emitJoinPointsBody k
  | .let (k := k) .. | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
  | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => emitJoinPointsBody k
  | .cases cs => cs.alts.forM (fun alt => emitJoinPointsBody alt.getCode)
  | .return .. | .jmp .. | .unreach .. => return ()

partial def emitCode (code : Code .impure) : EmitM Unit := do
  unless (← read).inStateMachineLoop do
    let declared ← declareVars code
    if declared then emitLn ""
  emitBasicBlock code

end

def emitDeclBody (code : Code .impure) : EmitM Unit := do
  let needsLoop ← hasControlFlow code
  if needsLoop then
    -- Hoist ALL variable declarations before the loop so they are visible across all states.
    let declared ← declareAllVars code
    if declared then emitLn ""
    emitLn "let mut state = 0;"
    emitLn "loop {";
    emitLn "match state {"
    emitLn "0 => {"
    withReader (fun ctx => { ctx with inStateMachineLoop := true }) do
      emitBasicBlock code
      emitLn "}"
      emitJoinPointsBody code
    emitLn "_ => {}"
    emitLn "}"
    emitLn "}"
  else
    emitCode code

def emitDecl (decl : Decl .impure) : EmitM Unit := do
  let env ← getEnv
  if hasInitAttr env decl.name || isSimpleGroundDecl env decl.name then
    return ()
  match decl.value with
  | .extern .. => return ()
  | .code code =>
    let baseName ← toCName decl.name
    let ps := decl.params
    emit "pub unsafe fn "

    if ps.isEmpty then
      emitCInitName decl.name
      emit s!"() -> {decl.type.toRustType}"
    else
      emit baseName
      emit "("
      let ps := paramsWithoutVoid ps
      if ps.size > closureMaxArgs && isBoxedName decl.name then
        emit s!"_args: *mut {leanObjectPtrTy}"
      else
        ps.size.forM fun i _ => do
          if i > 0 then emit ", "
          let p := ps[i]
          emit "mut "; emit p.binderName; emit s!": {p.type.toRustType}"
      emit s!") -> {decl.type.toRustType}"

    withEmitBlock do
      if ps.size > closureMaxArgs && isBoxedName decl.name then
        ps.size.forM fun i _ => do
          let p := ps[i]
          emit "let mut "; emit p.binderName; emit s!": {p.type.toRustType} = *_args.add("; emit i; emitLn ");"

      modify fun s => { s with stateIds := {}, nextStateId := 1 }
      assignStateIds code
      withReader (fun ctx => { ctx with currFn := decl.name, currParams := ps }) do
        emitDeclBody code

def emitFns : EmitM Unit := do
  (← getLocalDecls).forM go
where
  go (decl : Decl .impure) : EmitM Unit := do
    let decl ← decl.internalize (uniqueIdents := true)
    try
      emitDecl decl
    catch err =>
      throwError m!"{err.toMessageData}\ncompiling:\n{decl.name}"

def withErrRet (emitIORes : EmitM Unit) : EmitM Unit := do
  emit "res = "; emitIORes; emitLn ";"
  emitLn s!"if {leanh "lean_io_result_is_error"}(res) \{ return res; }"

def emitMarkPersistent (decl : Decl .impure) : EmitM Unit := do
  if decl.type.isObj then
    emitCApp1 "lean_mark_persistent" (← toCName decl.name); emitLn ";"

def emitDeclInit (decl : Decl .impure) (isBuiltin : Bool) : EmitM Unit := do
  let env ← getEnv
  if (isBuiltin && isIOUnitBuiltinInitFn env decl.name) || isIOUnitInitFn env decl.name then
      withErrRet do
        emitCName decl.name; emit "()"
      emitLn s!"{leanh "lean_dec_ref"}(res);"
  else if decl.params.isEmpty then
    if let some initFn := (guard isBuiltin *> getBuiltinInitFnNameFor? env decl.name) <|> getInitFnNameFor? env decl.name then
      withErrRet do
        emitCName initFn; emit "()"
      emit s!"{← toCName decl.name}"
      if decl.type.isScalar then
        if decl.type == ImpureType.bool then
          emitLn <| " = (" ++ leanh decl.type.unboxOpName ++ "(" ++ leanh "lean_io_result_get_value" ++ "(res)) != 0);"
        else if decl.type == ImpureType.uint8 || decl.type == ImpureType.uint16 then
          emitLn <| " = (" ++ leanh decl.type.unboxOpName ++ "(" ++ leanh "lean_io_result_get_value" ++ "(res)) as " ++ decl.type.toRustType ++ ");"
        else
          emitLn <| " = " ++ leanh decl.type.unboxOpName ++ "(" ++ leanh "lean_io_result_get_value" ++ "(res));"
      else
        emitLn s!" = {leanh "lean_io_result_get_value"}(res);"
        emitMarkPersistent decl
      emitLn s!"{leanh "lean_dec_ref"}(res);"
    else if !(isClosedTermName env decl.name || isSimpleGroundDecl env decl.name) then
      emit s!"{← toCName decl.name}"; emit " = "; emitCInitName decl.name; emitLn "();"
      emitMarkPersistent decl

-- Emit a single init function body (externs already emitted by the caller).
def emitInitFn (phases : IRPhases) (impInitFns : List String) : EmitM Unit := do
  let env ← getEnv
  let initialized := s!"_G_{mkModuleInitializationPrefix phases}initialized"
  emitLns [
    s!"static mut {initialized}: bool = false;",
    s!"pub unsafe fn {← getModInitFn (phases := phases)}(builtin: bool) -> {leanObjectPtrTy} \{",
    s!"let mut res: {leanObjectPtrTy} = core::ptr::null_mut();",
    s!"if {initialized} \{ return {leanh "lean_io_result_mk_ok"}({leanh "lean_box"}(0)); }",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn s!"{leanh "lean_dec_ref"}(res);"
  for decl in (← getLocalDecls) do
    if phases == .all || (phases == .comptime) == isMarkedMeta env decl.name then
      emitDeclInit decl (isBuiltin := phases != .comptime)
  emitLn s!"return {leanh "lean_io_result_mk_ok"}({leanh "lean_box"}(0));"
  emitLn "}"

def emitLegacyInitFn (impInitFns : List String) : EmitM Unit := do
  let initialized := s!"_G_initialized"
  emitLns [
    s!"static mut {initialized}: bool = false;",
    s!"pub unsafe fn {← getModInitFn (phases := .all)}(builtin: bool) -> {leanObjectPtrTy} \{",
    s!"let mut res: {leanObjectPtrTy} = core::ptr::null_mut();",
    s!"if {initialized} \{ return {leanh "lean_io_result_mk_ok"}({leanh "lean_box"}(0)); }",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn s!"{leanh "lean_dec_ref"}(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .runtime)}(builtin)"
  emitLn s!"{leanh "lean_dec_ref"}(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .comptime)}(builtin)"
  emitLn s!"{leanh "lean_dec_ref"}(res);"
  emitLn s!"return {← getModInitFn (phases := .all)}(builtin);"
  emitLn "}"

def emitFnDecls : EmitM Unit := do
  for decl in (← getLocalDecls) do
    let decl ← decl.internalize (uniqueIdents := true)
    let env ← getEnv
    let cppBaseName ← toCName decl.name
    if isSimpleGroundDecl env decl.name then
      emitGroundDecl decl cppBaseName
    else if isClosedTermName env decl.name then
      emitLn s!"static mut {toOnceTokenName cppBaseName}: {leanh "LeanOnceCell"} = {leanh "LeanOnceCell"} \{ state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };"
      emitLn s!"static mut {cppBaseName}: {decl.type.toRustType} = {defaultInitializer decl.type};"
    else if decl.params.isEmpty && hasInitAttr env decl.name && !(isIOUnitBuiltinInitFn env decl.name || isIOUnitInitFn env decl.name) then
      emitLn s!"pub static mut {cppBaseName}: {decl.type.toRustType} = {defaultInitializer decl.type};"
    else if decl.params.isEmpty && !hasInitAttr env decl.name then
      emitLn s!"pub static mut {cppBaseName}: {decl.type.toRustType} = {defaultInitializer decl.type};"

def emitMainFnIfNeeded : EmitM Unit := do
  if let some mainFn ← hasMainFn then
    emitMainFn mainFn
where
  hasMainFn : EmitM (Option (Decl .impure)) := do
    return (← getLocalDecls).find? (·.name == `main)

  emitMainFn (decl : Decl .impure) : EmitM Unit := do
    let .code .. := decl.value | throwError "Expected Lean function declaration as `main`"
    let ps := decl.params
    if ps.size != 1 && ps.size != 2 then
      throwError "invalid main function, incorrect arity when generating code"
    let env ← getEnv
    let usesLeanAPI := usesModuleFrom env `Lean

    -- Determine exit code type
    let retTy := env.find? `main |>.get! |>.type |>.getForallBody
    let retTy := retTy.appArg!
    let hasExitCode := retTy.isConstOf ``UInt32

    emitLns [
      s!"unsafe fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> {leanObjectPtrTy} \{",
      if ps.size == 2 then
        s!"    let mut args_list = {leanh "lean_box"}(0);
            let mut i = argc;
            while i > 1 \{
                i -= 1;
                let arg_str = {leanh "lean_mk_string"}(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = {leanh "lean_alloc_ctor"}(1, 2, 0);
                {leanh "lean_ctor_set"}(args_list, 0, arg_str);
                {leanh "lean_ctor_set"}(args_list, 1, fields[1]);
            }
            return {leanMainFn}(args_list);"
      else
        s!"    return {leanMainFn}();"
      ,
      "}"
    ]

    emitLns [
      "unsafe fn lean_rust_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {",
      if usesLeanAPI then s!"  {leanh "lean_initialize"}();" else s!"  {leanh "lean_initialize_runtime_module"}();",
      s!"  let res = {← getModInitFn (phases := if env.header.isModule then .runtime else .all)}(true /* builtin */);",
      s!"  {leanh "lean_io_mark_end_initialization"}();",
      "  let mut ret_val = 1;",
      s!"  if {leanh "lean_io_result_is_ok"}(res) \{",
      s!"    {leanh "lean_dec"}(res);",
      s!"    {leanh "lean_init_task_manager"}();",
      "    let main_res = run_main(argc, argv);",
      s!"    {leanh "lean_finalize_task_manager"}();",
      s!"    if {leanh "lean_io_result_is_ok"}(main_res) \{",
      if hasExitCode then
        s!"      ret_val = {leanh "lean_unbox_uint32"}({leanh "lean_io_result_get_value"}(main_res)) as i32;"
      else
        "      ret_val = 0;"
      ,
      s!"      {leanh "lean_dec"}(main_res);",
      "    } else {",
      s!"      {leanh "lean_io_result_show_error"}(main_res);",
      s!"      {leanh "lean_dec"}(main_res);",
      "    }",
      "  } else {",
      s!"    {leanh "lean_io_result_show_error"}(res);",
      s!"    {leanh "lean_dec"}(res);",
      "  }",
      "  return ret_val;",
      "}",
      "",
      "pub fn main() {",
      "  let c_args: Vec<std::ffi::CString> = std::env::args().map(|arg| std::ffi::CString::new(arg).expect(\"process argument contains NUL byte\")).collect();",
      "  let mut raw_args: Vec<*mut core::ffi::c_char> = c_args.iter().map(|arg| arg.as_ptr() as *mut core::ffi::c_char).collect();",
      "  let argc = raw_args.len() as core::ffi::c_int;",
      "  let code = unsafe { lean_rust_main(argc, raw_args.as_mut_ptr()) };",
      "  std::process::exit(code);",
      "}"
    ]

def emitFileFooter : EmitM Unit := return ()

def emitFileBody : EmitM Unit := do
  emitFnDecls
  emitFns
  if (← getEnv).header.isModule then
    let runtimeFns ← getInitFnNames .runtime
    let comptimeFns ← getInitFnNames .comptime
    let legacyFns ← getLegacyInitFnNames
    emitInitFn .runtime runtimeFns
    emitInitFn .comptime comptimeFns
    emitLegacyInitFn legacyFns
  else
    let allFns ← getInitFnNames .all
    emitInitFn .all allFns
  emitMainFnIfNeeded
  emitFileFooter

def main (body : String) : EmitM Unit := do
  emitFileHeader body
  emit body

public def emitRustForDecls (modName : Name) (decls : Array Name) : CoreM String := do
  let (localDecls, otherModuleDecls) ← collectUsedDecls decls
  let env ← getEnv
  let indexMap := getImpureDeclIndices env decls
  let localDecls := localDecls.qsort fun l r => indexMap[l.name]! < indexMap[r.name]!
  let ctx := { localDecls, otherModuleDecls, modName }
  let (_, { buf := body, .. }) ←
    emitFileBody
      |>.run ctx
      |>.run {}
      |>.run (phase := .impure)
  let (_, { buf, .. }) ←
    main body
      |>.run ctx
      |>.run {}
      |>.run (phase := .impure)
  return buf

public def emitRust (modName : Name) : CoreM String := do
  emitRustForDecls modName (← getLocalImpureDecls)

end Lean.Compiler.LCNF

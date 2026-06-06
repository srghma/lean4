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

namespace ImpureType

def Lean.Expr.toRustType : Expr → String
  | float => "f64"
  | float32 => "f32"
  | uint8 => "u8"
  | uint16 => "u16"
  | uint32 => "u32"
  | uint64 => "u64"
  | usize => "usize"
  | object => "*mut lean_object"
  | tagged => "*mut lean_object"
  | tobject => "*mut lean_object"
  | erased => "*mut lean_object"
  | void => "*mut lean_object"
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
  | uint8 => "lean_ctor_get_uint8"
  | uint16 => "lean_ctor_get_uint16"
  | uint32 => "lean_ctor_get_uint32"
  | uint64 => "lean_ctor_get_uint64"
  | _ => unreachable!

def Lean.Expr.ssetOpName (t : Expr) : String :=
  match t with
  | float => "lean_ctor_set_float"
  | float32 => "lean_ctor_set_float32"
  | uint8 => "lean_ctor_set_uint8"
  | uint16 => "lean_ctor_set_uint16"
  | uint32 => "lean_ctor_set_uint32"
  | uint64 => "lean_ctor_set_uint64"
  | _ => unreachable!

def Lean.Expr.closedTermReadOpName (t : Expr) : String :=
  match t with
  | float => "lean_float_once"
  | float32 => "lean_float32_once"
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
  | uint8 | uint16 | uint32 | uint64 | usize => "0"
  | _ => "core::ptr::null_mut()"

private def scalarPtrLiteral (b1 b2 b3 b4 b5 b6 b7 b8 : UInt8) : String :=
  let pack (b : UInt8) (shift : UInt64) : UInt64 := b.toUInt64 <<< shift
  let v := pack b1 0 ||| pack b2 8 ||| pack b3 16 ||| pack b4 24 |||
           pack b5 32 ||| pack b6 40 ||| pack b7 48 ||| pack b8 56
  s!"{v} as *mut lean_object"

structure Context where
  localDecls : Array (Decl .impure)
  otherModuleDecls : Array (Signature .impure)
  modName : Name
  currFn : Name := default
  currParams : Array (Param .impure) := #[]

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

def Arg.toRustString (a : Arg .impure) : EmitM String := do
  match a with
  | .fvar fvarId => EmitToString.toEmitString fvarId
  | .erased => return "lean_box(0)"

instance : EmitToString (Arg .impure) where
  toEmitString a := a.toRustString

@[inline] def emit [EmitToString α] (a : α) : EmitM Unit := do
  let str ← EmitToString.toEmitString a
  modify fun out => { out with buf := out.buf ++ str }

@[inline] def emitLn [EmitToString α] (a : α) : EmitM Unit := do
  emit a; emit "\n"

@[inline]
def emitCApp1 {α : Type} [EmitToString α] (fn : String) (arg : α) : EmitM Unit := do
  emit fn; emit "("; emit arg; emit ")"

@[inline]
def emitCApp2 {α β : Type} [EmitToString α] [EmitToString β] (fn : String) (arg1 : α) (arg2 : β) :
    EmitM Unit := do
  emit fn; emit "("; emit arg1; emit ", "; emit arg2; emit ")"

@[inline]
def emitCApp3 {α β γ : Type} [EmitToString α] [EmitToString β] [EmitToString γ] (fn : String)
    (arg1 : α) (arg2 : β) (arg3 : γ) : EmitM Unit := do
  emit fn; emit "("; emit arg1; emit ", "; emit arg2; emit ", "; emit arg3; emit ")"

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

def emitFileHeader : EmitM Unit := do
  let env ← getEnv
  let modName ← getModName
  emitLn "// Lean compiler output"
  emitLn s!"// Module: {modName}"
  emit "// Imports:"
  env.imports.forM fun m => emit (" " ++ toString m)
  emitLn ""
  emitLns [
    "#[repr(C)]",
    "pub struct lean_object { _private: [u8; 0] }",
    "#[repr(C)]",
    "pub struct lean_once_cell {",
    "  pub m_value: *mut lean_object,",
    "  pub m_initialized: u8,",
    "}",
    "extern \"C\" {",
    "  fn lean_box(n: usize) -> *mut lean_object;",
    "  fn lean_unbox(o: *mut lean_object) -> usize;",
    "  fn lean_dec(o: *mut lean_object);",
    "  fn lean_inc(o: *mut lean_object);",
    "  fn lean_alloc_ctor(tag: core::ffi::c_uint, num_objs: core::ffi::c_uint, scalar_size: core::ffi::c_uint) -> *mut lean_object;",
    "  fn lean_ctor_set(obj: *mut lean_object, index: core::ffi::c_uint, value: *mut lean_object);",
    "  fn lean_ctor_get(obj: *mut lean_object, index: core::ffi::c_uint) -> *mut lean_object;",
    "  fn lean_ctor_release(obj: *mut lean_object, index: core::ffi::c_uint);",
    "  fn lean_ctor_set_tag(obj: *mut lean_object, tag: core::ffi::c_uint);",
    "  fn lean_is_exclusive(o: *mut lean_object) -> bool;",
    "  fn lean_is_scalar(obj: *const lean_object) -> bool;",
    "  fn lean_alloc_closure(fun_ptr: *mut core::ffi::c_void, arity: core::ffi::c_uint, num_fixed: core::ffi::c_uint) -> *mut lean_object;",
    "  fn lean_closure_set(obj: *mut lean_object, index: core::ffi::c_uint, value: *mut lean_object);",
    "  fn lean_apply_m(obj: *mut lean_object, nargs: usize, args: *mut *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_1(obj: *mut lean_object, a1: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_2(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_3(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_4(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_5(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_6(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_7(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_8(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_9(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_10(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_11(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_12(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object, a12: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_13(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object, a12: *mut lean_object, a13: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_14(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object, a12: *mut lean_object, a13: *mut lean_object, a14: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_15(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object, a12: *mut lean_object, a13: *mut lean_object, a14: *mut lean_object, a15: *mut lean_object) -> *mut lean_object;",
    "  fn lean_apply_16(obj: *mut lean_object, a1: *mut lean_object, a2: *mut lean_object, a3: *mut lean_object, a4: *mut lean_object, a5: *mut lean_object, a6: *mut lean_object, a7: *mut lean_object, a8: *mut lean_object, a9: *mut lean_object, a10: *mut lean_object, a11: *mut lean_object, a12: *mut lean_object, a13: *mut lean_object, a14: *mut lean_object, a15: *mut lean_object, a16: *mut lean_object) -> *mut lean_object;",
    "  fn lean_ctor_set_usize(obj: *mut lean_object, index: core::ffi::c_uint, value: usize);",
    "  fn lean_ctor_get_usize(obj: *mut lean_object, index: core::ffi::c_uint) -> usize;",
    "  fn lean_ctor_set_float(obj: *mut lean_object, offset: core::ffi::c_uint, value: f64);",
    "  fn lean_ctor_set_float32(obj: *mut lean_object, offset: core::ffi::c_uint, value: f32);",
    "  fn lean_ctor_set_uint8(obj: *mut lean_object, offset: core::ffi::c_uint, value: u8);",
    "  fn lean_ctor_set_uint16(obj: *mut lean_object, offset: core::ffi::c_uint, value: u16);",
    "  fn lean_ctor_set_uint32(obj: *mut lean_object, offset: core::ffi::c_uint, value: u32);",
    "  fn lean_ctor_set_uint64(obj: *mut lean_object, offset: core::ffi::c_uint, value: u64);",
    "  fn lean_ctor_get_float(obj: *mut lean_object, offset: core::ffi::c_uint) -> f64;",
    "  fn lean_ctor_get_float32(obj: *mut lean_object, offset: core::ffi::c_uint) -> f32;",
    "  fn lean_ctor_get_uint8(obj: *mut lean_object, offset: core::ffi::c_uint) -> u8;",
    "  fn lean_ctor_get_uint16(obj: *mut lean_object, offset: core::ffi::c_uint) -> u16;",
    "  fn lean_ctor_get_uint32(obj: *mut lean_object, offset: core::ffi::c_uint) -> u32;",
    "  fn lean_ctor_get_uint64(obj: *mut lean_object, offset: core::ffi::c_uint) -> u64;",
    "  fn lean_mk_string_unchecked(s: *const core::ffi::c_char, sz: usize, len: usize) -> *mut lean_object;",
    "  fn lean_mk_string(s: *const core::ffi::c_char) -> *mut lean_object;",
    "  fn lean_unsigned_to_nat(v: core::ffi::c_uint) -> *mut lean_object;",
    "  fn lean_cstr_to_nat(s: *const core::ffi::c_char) -> *mut lean_object;",
    "  fn lean_unbox_uint32(o: *mut lean_object) -> u32;",
    "  fn lean_unbox_uint64(o: *mut lean_object) -> u64;",
    "  fn lean_unbox_usize(o: *mut lean_object) -> usize;",
    "  fn lean_unbox_float(o: *mut lean_object) -> f64;",
    "  fn lean_unbox_float32(o: *mut lean_object) -> f32;",
    "  fn lean_box_uint32(v: u32) -> *mut lean_object;",
    "  fn lean_box_uint64(v: u64) -> *mut lean_object;",
    "  fn lean_box_usize(v: usize) -> *mut lean_object;",
    "  fn lean_box_float(v: f64) -> *mut lean_object;",
    "  fn lean_box_float32(v: f32) -> *mut lean_object;",
    "  fn lean_mark_persistent(o: *mut lean_object);",
    "  fn lean_io_result_mk_ok(o: *mut lean_object) -> *mut lean_object;",
    "  fn lean_obj_tag(o: *mut lean_object) -> core::ffi::c_uint;",
    "  fn lean_del_object(o: *mut lean_object);",
    "  fn lean_dec_ref(o: *mut lean_object);",
    "  fn lean_dec_ref_known(o: *mut lean_object, n: usize);",
    "  fn lean_float_once(v: *mut f64, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> f64;",
    "  fn lean_float32_once(v: *mut f32, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> f32;",
    "  fn lean_uint8_once(v: *mut u8, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> u8;",
    "  fn lean_uint16_once(v: *mut u16, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> u16;",
    "  fn lean_uint32_once(v: *mut u32, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> u32;",
    "  fn lean_uint64_once(v: *mut u64, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> u64;",
    "  fn lean_usize_once(v: *mut usize, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> usize;",
    "  fn lean_obj_once(v: *mut *mut lean_object, t: *mut lean_once_cell, f: unsafe extern \"C\" fn() -> *mut lean_object) -> *mut lean_object;",
    "  fn lean_setup_args(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut *mut core::ffi::c_char;",
    "  fn lean_initialize();",
    "  fn lean_initialize_runtime_module();",
    "  fn lean_init_task_manager();",
    "  fn lean_finalize_task_manager();",
    "  fn lean_run_main(f: unsafe extern \"C\" fn(core::ffi::c_int, *mut *mut core::ffi::c_char) -> *mut lean_object, argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object;",
    "  fn lean_io_mark_end_initialization();",
    "  fn lean_io_result_is_error(res: *mut lean_object) -> bool;",
    "  fn lean_io_result_is_ok(res: *mut lean_object) -> bool;",
    "  fn lean_io_result_get_value(res: *mut lean_object) -> *mut lean_object;",
    "  fn lean_io_result_get_error(res: *mut lean_object) -> *mut lean_object;",
    "  fn lean_io_result_show_error(res: *mut lean_object);",
    "}",
    "#[repr(C)]",
    "struct lean_ctor_object<const N: usize> {",
    "  m_header: lean_object,",
    "  m_objs: [*mut lean_object; N],",
    "}",
    "#[repr(C)]",
    "struct lean_closure_object<const N: usize> {",
    "  m_header: lean_object,",
    "  m_fun: *const core::ffi::c_void,",
    "  m_arity: u16,",
    "  m_num_fixed: u16,",
    "  m_objs: [*mut lean_object; N],",
    "}",
    "#[repr(C)]",
    "struct lean_array_object<const N: usize> {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_data: [*mut lean_object; N],",
    "}",
    "#[repr(C)]",
    "struct lean_sarray_object<const N: usize> {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_data: [u8; N],",
    "}",
    "#[repr(C)]",
    "struct lean_string_object<const N: usize> {",
    "  m_header: lean_object,",
    "  m_size: usize,",
    "  m_capacity: usize,",
    "  m_length: usize,",
    "  m_data: [u8; N],",
    "}"
  ]

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
    s!"lean_object \{ m_rc: 0, m_cs_sz: {csSz} as u16, m_other: {other}, m_tag: {tag} }"

  mkCtorHeader (numObjs : Nat) (usize : Nat) (ssize : Nat) (tag : Nat) : String :=
    let size := s!"core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*{numObjs} + {ctorScalarSizeExpression usize ssize}"
    mkHeader size numObjs tag

  compileGround (e : SimpleGroundExpr) : GroundM Unit := do
    let valueName ← compileGroundToValue e
    let declPrefix := if isClosedTermName (← getEnv) decl.name then "static mut" else "#[no_mangle] pub static mut"
    emitLn <| s!"{declPrefix} {cppBaseName}: *mut lean_object = core::ptr::addr_of!({valueName}) as *mut lean_object;"

  compileGroundToValue (e : SimpleGroundExpr) : GroundM String := do
    match e with
    | .ctor cidx objArgs usizeArgs scalarArgs =>
      let val ← compileCtor cidx objArgs usizeArgs scalarArgs
      mkValueCLit "lean_ctor_object" val
    | .string data =>
      let leanStringTag := 249
      let header := mkHeader 0 0 leanStringTag
      let size := data.utf8ByteSize + 1 -- null byte
      let length := data.length
      let dataBytes := String.intercalate ", " <| (data.toUTF8.data.toList.map (fun b => toString b.toNat))
      let type := "lean_string_object<" ++ toString size ++ ">"
      let value := (s!"lean_string_object \{ m_header: {header}, m_size: {size}, m_capacity: {size}, m_length: {length}, m_data: [") ++ dataBytes ++ ", 0]" ++ "}"
      mkValueCLit
        type
        value
    | .pap func args =>
      let numFixed := args.size
      let leanClosureTag := 245
      let header := mkHeader s!"core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*{numFixed}" 0 leanClosureTag
      let funPtr := s!"{← toCName func} as *const core::ffi::c_void"
      let arity := (← getImpureSignature? func).get!.params.size
      let args ← args.mapM groundArgToCLit
      let argArray := String.intercalate "," args.toList
      mkValueCLit
        s!"lean_closure_object<{numFixed}>"
        s!"lean_closure_object \{ m_header: {header}, m_fun: {funPtr}, m_arity: {arity}, m_num_fixed: {numFixed}, m_objs: [{argArray}] }"
    | .nameMkStr args =>
      let obj ← groundNameMkStrToCLit args
      mkValueCLit "lean_ctor_object" obj
    | .array elems =>
      let leanArrayTag := 246
      let header := mkHeader s!"core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*{elems.size}" 0 leanArrayTag
      let elemLits ← elems.mapM groundArgToCLit
      let dataArray := String.intercalate "," elemLits.toList
      mkValueCLit
        s!"lean_array_object<{elems.size}>"
        s!"lean_array_object \{ m_header: {header}, m_size: {elems.size}, m_capacity: {elems.size}, m_data: [{dataArray}] }"
    | .byteArray data =>
      let leanScalarArrayTag := 248
      let elemSize : Nat := 1
      let header := mkHeader s!"core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + {data.size}" elemSize leanScalarArrayTag
      let dataLits := data.map toString
      let dataArray := String.intercalate "," dataLits.toList
      mkValueCLit
        s!"lean_sarray_object<{data.size}>"
        s!"lean_sarray_object \{ m_header: {header}, m_size: {data.size}, m_capacity: {data.size}, m_data: [{dataArray}] }"
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

  mkValueCLit (type value : String) : GroundM String := do
    let valueName := mkValueName cppBaseName
    emitLn <| s!"static {valueName}: {type} = {value};"
    return valueName

  groundNameMkStrToCLit (args : Array (Name × UInt64)) : GroundM String := do
    assert! args.size > 0
    if h : args.size = 1 then
      let (ref, hash) := args[0]
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.tagged 0, .reference ref] #[] hash
    else
      let (ref, hash) := args.back!
      let args := args.pop
      let lit ← groundNameMkStrToCLit args
      let auxName ← mkAuxDecl "lean_ctor_object" lit
      let hash := uint64ToByteArrayLE hash
      compileCtor 1 #[.rawReference auxName, .reference ref] #[] hash

  groundArgToCLit (a : SimpleGroundArg) : GroundM String := do
    match a with
    | .tagged val => return s!"((( {val} as usize) << 1) | 1) as *mut lean_object"
    | .reference decl =>  return s!"core::ptr::addr_of!({← findValueDecl decl}) as *mut lean_object"
    | .rawReference decl => return s!"core::ptr::addr_of!({decl}) as *mut lean_object"

  findValueDecl (n : Name) : GroundM String := do
    let env ← getEnv
    if let some ground := getSimpleGroundExpr env n then
      discard <| compileGroundToValue ground
      return mkValueName (← toCName n)
    else
      toCName n

  compileCtor (cidx : Nat) (objArgs : Array SimpleGroundArg) (usizeArgs : Array UInt64) (scalarArgs : Array UInt8) : GroundM String := do
    let numObjs := objArgs.size + usizeArgs.size
    let header := mkCtorHeader numObjs usizeArgs.size scalarArgs.size cidx
    let objArgs ← objArgs.mapM groundArgToCLit
    let usizeArgs : Array String := usizeArgs.map fun val => s!"({val} as *mut lean_object)"
    let scalarArgs ← packScalarArgs scalarArgs
    let argArray := String.intercalate "," (objArgs ++ usizeArgs ++ scalarArgs).toList
    return s!"lean_ctor_object \{ m_header: {header}, m_objs: [{argArray}] }"

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

def emitFnDecls : EmitM Unit := do
  emitLn "extern \"C\" {"
  (← getOtherModuleDecls).forM fun sig => do
    match getExternNameFor (← getEnv) `c sig.name with
    | some externName => emitFnDeclAux sig externName true
    | none => emitFnDeclStandard sig true
  emitLn "}"
  
  (← getLocalDecls).forM fun decl => do
    match getExternNameFor (← getEnv) `c decl.name with
    | some externName => emitFnDeclAux decl.toSignature externName false
    | none => emitFnDecl decl false
where
  emitExternDecl (sig : Signature .impure) (externName : String) : EmitM Unit := do
    emitFnDeclAux sig externName true

  emitFnDecl (decl : Decl .impure) (isExternal : Bool) : EmitM Unit := do
    let env ← getEnv
    let cppBaseName ← toCName decl.name
    if isSimpleGroundDecl env decl.name then
      emitGroundDecl decl cppBaseName
    else if isClosedTermName env decl.name then
      emitFnDeclClosed decl cppBaseName
    else
      emitFnDeclStandard decl.toSignature isExternal

  emitFnDeclClosed (decl : Decl .impure) (cppBaseName : String) : EmitM Unit := do
    emitLn s!"static mut {toOnceTokenName cppBaseName}: lean_once_cell = lean_once_cell \{ m_value: core::ptr::null_mut(), m_initialized: 0 };"
    emitLn s!"static mut {cppBaseName}: {decl.type.toRustType} = {defaultInitializer decl.type};"

  emitFnDeclStandard (sig : Signature .impure) (isExternal : Bool) : EmitM Unit := do
    let cppBaseName ← toCName sig.name
    emitFnDeclAux sig cppBaseName isExternal

  emitFnDeclAux (sig : Signature .impure) (cppBaseName : String) (isExternal : Bool) :
      EmitM Unit := do
    let ps := sig.params
    let env ← getEnv

    if ps.isEmpty then
      if isExternal then
        emitLn s!"    static mut {cppBaseName}: {sig.type.toRustType};"
      else
        let declPrefix := if isClosedTermName env sig.name then "static mut" else "#[no_mangle] pub static mut"
        emitLn s!"{declPrefix} {cppBaseName}: {sig.type.toRustType} = {defaultInitializer sig.type};"
    else
      if isExternal then
        emit s!"    fn {cppBaseName}"
        unless ps.isEmpty do
          emit "("
          let ps := paramsWithoutVoid ps
          let ps := if isExternC env sig.name then paramsWithoutErased ps else ps
          if ps.size > closureMaxArgs && isBoxedName sig.name then
            emit "_: *mut *mut lean_object"
          else
            ps.size.forM fun i _ => do
              if i > 0 then emit ", "
              emit s!"_: {ps[i].type.toRustType}"
          emit ")"
        emit s!" -> {sig.type.toRustType};"
        emitLn ""

def offsetExpression (i : Nat) (offset : Nat) : String :=
  if i > 0 then
    if offset > 0 then
      s!"core::mem::size_of::<*mut lean_object>()*{i} + {offset}"
    else
      s!"core::mem::size_of::<*mut lean_object>()*{i}"
  else
    s!"{offset}"

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
        declareVar decl.binderName decl.type
        go k true
    | .jp decl k =>
      declareParams decl.params
      go k (didChange || !decl.params.isEmpty)
    | .del (k := k) .. | .dec (k := k) .. | .inc (k := k) .. | .setTag (k := k) ..
    | .sset (k := k) .. | .uset (k := k) .. | .oset (k := k) .. => go k didChange
    | .cases .. | .return .. | .jmp .. | .unreach .. => return didChange

  declareVar (binderName : Name) (type : Expr) : EmitM Unit := do
    emit "let mut "; emit binderName; emit s!": {type.toRustType} = {defaultInitializer type}; "

  declareParams (ps : Array (Param .impure)) : EmitM Unit := do
    ps.forM fun p => declareVar p.binderName p.type

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
    emitCApp3 "lean_alloc_ctor" info.cidx info.size (ctorScalarSizeExpression info.usize info.ssize)

  emitCtorSetArgs (targetId : FVarId) (args : Array (Arg .impure)) : EmitM Unit := do
    for h : i in 0...args.size do
      let arg := args[i]
      emitCApp3 "lean_ctor_set" targetId i arg; emitLn ";"

  emitCtor (info : CtorInfo) (args : Array (Arg .impure)) : EmitM Unit := do
    if info.size == 0 && info.usize == 0 && info.ssize == 0 then do
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
      withEmitAssignment do emit "lean_box(0)"

  emitReuse (fvarId : FVarId) (info : CtorInfo) (update : Bool) (args : Array (Arg .impure)) :
      EmitM Unit := do
    emit "if "; emitCApp1 "lean_is_scalar" fvarId
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
      match getExternAttrData? (← getEnv) fn |>.bind (getExternEntryFor · `c) with
      | some (.standard _ fn) =>
        let (_, args) :=
          ps.zip args
            |>.filter (fun (p, _) => !(p.type.isVoid || p.type.isErased))
            |>.unzip
        emit fn; emit "("
        for h : i in 0...args.size do
          if i > 0 then emit ", "
          emit args[i]
        emit ")"
      | some (.inline _ pat) =>
        emit (expandExternPattern pat (← toStringArgs args))
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
          emit s!"lean_apply_m({fvarIdStr}, {args.size}, _aargs.as_mut_ptr())"
    else
      withEmitAssignment do
        emit s!"lean_apply_{args.size}("; emit fvarId; emit ", "; emitArgs args; emit ")"

  emitBox (ty : Expr) (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp1 ty.boxOpName fvarId

  emitUnbox (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emitCApp1 decl.type.unboxOpName fvarId

  emitIsShared (fvarId : FVarId) : EmitM Unit := do
    withEmitAssignment do
      emit "!lean_is_exclusive("; emit fvarId; emit ")"

  emitLit (v : LitValue) : EmitM Unit := do
    withEmitAssignment do
      match v with
      | .uint8 v | .uint16 v | .uint32 v => emit v
      | .uint64 v => emit v; emit "u64"
      | .usize v => emit v; emit "usize"
      | .nat v =>
        if v < UInt32.size then
          emit "lean_unsigned_to_nat("; emit v; emit ")"
        else
          emit "lean_cstr_to_nat(b\""; emit v; emit "\\0\".as_ptr().cast())"
      | .str v =>
        emitCApp3 "lean_mk_string_unchecked" s!"b\"{quoteString v}\\0\".as_ptr().cast()" v.utf8ByteSize v.length

  emitErased : EmitM Unit := do
    withEmitAssignment do
      emit "lean_box(0)"

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
          emit p.type.toRustType; emit " _tmp_"; emit i; emit " = "; emit arg; emitLn ";"

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
      emit "if "; emitTag cs.discr; emit " == "; emit tag; emitLn ""
      emitCode t
      emitLn "else"
      emitCode e
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
    emitLn "panic!(\"unreachable\");"

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

partial def emitCode (code : Code .impure) : EmitM Unit := do
  let declared ← declareVars code
  if declared then emitLn ""
  emitBasicBlock code

end

def emitDeclBody (code : Code .impure) : EmitM Unit := do
  let needsLoop ← hasControlFlow code
  if needsLoop then
    emitLn "let mut state = 0;"
    emitLn "loop {";
    emitLn "match state {"
    emitLn "0 => {"
    emitCode code
    emitLn "}"
    emitJoinPoints code
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
    if ps.isEmpty then
      emit "#[no_mangle] pub unsafe extern \"C\" fn "
    else
      emit "#[no_mangle] pub unsafe extern \"C\" fn "

    if ps.isEmpty then
      emitCInitName decl.name
      emit "() -> *mut lean_object"
    else
      emit baseName
      emit "("
      let ps := paramsWithoutVoid ps
      if ps.size > closureMaxArgs && isBoxedName decl.name then
        emit "_args: *mut *mut lean_object"
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
  emitLn "if lean_io_result_is_error(res) { return res; }"

def emitMarkPersistent (decl : Decl .impure) : EmitM Unit := do
  if decl.type.isObj then
    emitCApp1 "lean_mark_persistent" (← toCName decl.name); emitLn ";"

def emitDeclInit (decl : Decl .impure) (isBuiltin : Bool) : EmitM Unit := do
  let env ← getEnv
  if (isBuiltin && isIOUnitBuiltinInitFn env decl.name) || isIOUnitInitFn env decl.name then
    withErrRet do
      emitCName decl.name; emit "()"
    emitLn "lean_dec_ref(res);"
  else if decl.params.isEmpty then
    if let some initFn := (guard isBuiltin *> getBuiltinInitFnNameFor? env decl.name) <|> getInitFnNameFor? env decl.name then
      withErrRet do
        emitCName initFn; emit "()"
      emit s!"{← toCName decl.name}"
      if decl.type.isScalar then
        emitLn <| " = " ++ decl.type.unboxOpName ++ "(lean_io_result_get_value(res));"
      else
        emitLn " = lean_io_result_get_value(res);"
        emitMarkPersistent decl
      emitLn "lean_dec_ref(res);"
    else if !(isClosedTermName env decl.name || isSimpleGroundDecl env decl.name) then
      emit s!"{← toCName decl.name}"; emit " = "; emitCInitName decl.name; emitLn "();"
      emitMarkPersistent decl

def emitInitFn (phases : IRPhases) : EmitM Unit := do
  let env ← getEnv
  -- Collect all init function names first, then deduplicate to avoid duplicate
  -- extern declarations when the same module appears as both regular and meta import.
  let allImpInitFns ← env.imports.filterMapM fun imp => do
    if phases != .all && imp.isMeta != (phases == .comptime) then
      return none
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index"
    let pkg? := env.getModulePackageByIdx? idx
    let fn := mkModuleInitializationFunctionName (phases := if phases == .all then .all else if imp.isMeta then .runtime else phases) imp.module pkg?
    return some fn
  let impInitFns := allImpInitFns.toList.eraseDups
  impInitFns.forM fun fn =>
    emitLn s!"extern \"C\" \{ fn {fn}(builtin: u8) -> *mut lean_object; }"
  let initialized := s!"_G_{mkModuleInitializationPrefix phases}initialized"
  emitLns [
    s!"static mut {initialized}: bool = false;",
    s!"#[no_mangle]",
    s!"pub unsafe extern \"C\" fn {← getModInitFn (phases := phases)}(builtin: u8) -> *mut lean_object \{",
    "let mut res;",
    s!"if {initialized} \{ return lean_io_result_mk_ok(lean_box(0)); }",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn "lean_dec_ref(res);"
  for decl in (← getLocalDecls) do
    if phases == .all || (phases == .comptime) == isMarkedMeta env decl.name then
      emitDeclInit decl (isBuiltin := phases != .comptime)
  emitLn "return lean_io_result_mk_ok(lean_box(0));"
  emitLn "}"

def emitLegacyInitFn : EmitM Unit := do
  let env ← getEnv
  let allImpInitFns ← env.imports.filterMapM fun imp => do
    let some idx := env.getModuleIdx? imp.module
      | throwError "(internal) import without module index"
    let pkg? := env.getModulePackageByIdx? idx
    return some (mkModuleInitializationFunctionName imp.module pkg?)
  let impInitFns := allImpInitFns.toList.eraseDups
  impInitFns.forM fun fn =>
    emitLn s!"extern \"C\" \{ fn {fn}(builtin: u8) -> *mut lean_object; }"
  let initialized := s!"_G_initialized"
  emitLns [
    s!"static mut {initialized}: bool = false;",
    s!"#[no_mangle]",
    s!"pub unsafe extern \"C\" fn {← getModInitFn (phases := .all)}(builtin: u8) -> *mut lean_object \{",
    "let mut res;",
    s!"if {initialized} \{ return lean_io_result_mk_ok(lean_box(0)); }",
    s!"{initialized} = true;"
  ]
  impInitFns.forM fun fn => do
    withErrRet do
      emit s!"{fn}(builtin)"
    emitLn "lean_dec_ref(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .runtime)}(builtin)"
  emitLn "lean_dec_ref(res);"
  withErrRet do
    emit s!"{← getModInitFn (phases := .comptime)}(builtin)"
  emitLn "lean_dec_ref(res);"
  emitLn s!"return {← getModInitFn (phases := .all)}(builtin);"
  emitLn "}"

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
      "unsafe extern \"C\" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {",
      if ps.size == 2 then
        s!"    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 \{
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return {leanMainFn}(args_list);"
      else
        s!"    return {leanMainFn}();"
      ,
      "}"
    ]

    emitLns [
      "#[no_mangle]",
      "pub unsafe extern \"C\" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {",
      "  argv = lean_setup_args(argc, argv);",
      if usesLeanAPI then "  lean_initialize();" else "  lean_initialize_runtime_module();",
      s!"  let res = {← getModInitFn (phases := if env.header.isModule then .runtime else .all)}(1 /* builtin */);",
      "  lean_io_mark_end_initialization();",
      "  let mut ret_val = 1;",
      "  if lean_io_result_is_ok(res) {",
      "    lean_dec(res);",
      "    lean_init_task_manager();",
      "    let main_res = lean_run_main(run_main, argc, argv);",
      "    lean_finalize_task_manager();",
      "    if lean_io_result_is_ok(main_res) {",
      if hasExitCode then
        "      ret_val = lean_unbox_uint32(lean_io_result_get_value(main_res)) as i32;"
      else
        "      ret_val = 0;"
      ,
      "      lean_dec(main_res);",
      "    } else {",
      "      lean_io_result_show_error(main_res);",
      "      lean_dec(main_res);",
      "    }",
      "  } else {",
      "    lean_io_result_show_error(res);",
      "    lean_dec(res);",
      "  }",
      "  return ret_val;",
      "}"
    ]

def emitFileFooter : EmitM Unit := return ()

def main : EmitM Unit := do
  emitFileHeader
  emitFnDecls
  emitFns
  if (← getEnv).header.isModule then
    emitInitFn (phases := .runtime)
    emitInitFn (phases := .comptime)
    emitLegacyInitFn
  else
    emitInitFn (phases := .all)
  emitMainFnIfNeeded
  emitFileFooter

public def emitRustForDecls (modName : Name) (decls : Array Name) : CoreM String := do
  let (localDecls, otherModuleDecls) ← collectUsedDecls decls
  let env ← getEnv
  let indexMap := getImpureDeclIndices env decls
  let localDecls := localDecls.qsort fun l r => indexMap[l.name]! < indexMap[r.name]!
  let (_, { buf, .. }) ←
    main
      |>.run { localDecls, otherModuleDecls, modName }
      |>.run {}
      |>.run (phase := .impure)
  return buf

public def emitRust (modName : Name) : CoreM String := do
  emitRustForDecls modName (← getLocalImpureDecls)

end Lean.Compiler.LCNF

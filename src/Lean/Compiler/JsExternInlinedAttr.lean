/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Coe
public import Init.Data.Repr
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Init.Data.ToString.Name

public section

namespace Lean.Compiler.JS

inductive JSBinOp where
  | and | bitAnd | bitOr | bitXor | divide | eq | ge | gt | in_ | instanceOf | le | lsh | lt | minus | mod | neq | of | or | plus | rsh | strictEq | strictNeq | times | ursh
  deriving Repr, BEq

inductive JSUnaryOp where
  | decr | delete | incr | minus | not | plus | tilde | typeof | void
  deriving Repr, BEq

inductive JsInlineExpr where
  | funArg (idx : Nat) -- like De Bruijn indices, everything else is copied from https://hackage.haskell.org/package/language-javascript
  | identifier (name : String)
  | decimal (val : Nat)
  | hex (val : Nat) -- 0xFF for example, should be rendered as 0xFF too
  | stringLiteral (val : String)
  | arrayLiteral (elems : Array JsInlineExpr)
  | callExpression (fn : JsInlineExpr) (args : Array JsInlineExpr)
  | memberDot (obj : JsInlineExpr) (name : String)
  | memberSquare (obj : JsInlineExpr) (idx : JsInlineExpr)
  | unaryExpression (op : JSUnaryOp) (arg : JsInlineExpr)
  | expressionBinary (op : JSBinOp) (lhs : JsInlineExpr) (rhs : JsInlineExpr)
  | expressionTernary (cond : JsInlineExpr) (thenExpr : JsInlineExpr) (elseExpr : JsInlineExpr)
  | memberNew (expr : JsInlineExpr) (args : Array JsInlineExpr)
  | throw (expr : JsInlineExpr)
  deriving Repr, BEq

def throwNewError (msg : String) : JsInlineExpr := .throw (.memberNew (.identifier "Error") #[.stringLiteral msg])
def plus a b := JsInlineExpr.expressionBinary .plus a b
def minus a b := JsInlineExpr.expressionBinary .minus a b
def times a b := JsInlineExpr.expressionBinary .times a b
def divide a b := JsInlineExpr.expressionBinary .divide a b
def mod a b := JsInlineExpr.expressionBinary .mod a b
def pow a b := JsInlineExpr.callExpression (.memberDot (.identifier "Math") "pow") #[a, b]
def eq a b := JsInlineExpr.expressionBinary .eq a b
def le a b := JsInlineExpr.expressionBinary .le a b
def lt a b := JsInlineExpr.expressionBinary .lt a b
def gt a b := JsInlineExpr.expressionBinary .gt a b
def bitAnd a b := JsInlineExpr.expressionBinary .bitAnd a b
def rsh a b := JsInlineExpr.expressionBinary .rsh a b


private unsafe def evalJsInlineExprUnsafe (e : Expr) : MetaM JsInlineExpr :=
  Meta.evalExpr' JsInlineExpr ``Lean.Compiler.JS.JsInlineExpr e

@[implemented_by evalJsInlineExprUnsafe]
opaque evalJsInlineExpr (e : Expr) : MetaM JsInlineExpr

end Lean.Compiler.JS

open Lean.Compiler.JS

/-- Arithmetic operator instances on JsInlineExpr so `#0 + #1`, `#0 * #1` etc. work directly. -/
instance : Add Lean.Compiler.JS.JsInlineExpr where add := Lean.Compiler.JS.plus
instance : Sub Lean.Compiler.JS.JsInlineExpr where sub := Lean.Compiler.JS.minus
instance : Mul Lean.Compiler.JS.JsInlineExpr where mul := Lean.Compiler.JS.times
instance : Div Lean.Compiler.JS.JsInlineExpr where div := Lean.Compiler.JS.divide
instance : Mod Lean.Compiler.JS.JsInlineExpr where mod := Lean.Compiler.JS.mod
instance : Pow Lean.Compiler.JS.JsInlineExpr Lean.Compiler.JS.JsInlineExpr where pow := Lean.Compiler.JS.pow

namespace Lean.Compiler.JS

-- 1. Declare the syntax category for our JS subset
declare_syntax_cat js_expr

-- 2. Define the grammar for the category
syntax "#" num : js_expr                        -- Arguments: #0, #1
syntax "#" num "." ident : js_expr              -- Arg + property: #0.length (avoids decimal-point ambiguity)
syntax num : js_expr                            -- Literals: 64, 0xFF
syntax str : js_expr                            -- String literals
syntax ident : js_expr                          -- Identifiers: Error, Uint8Array
syntax "(" js_expr ")" : js_expr                -- Parentheses
syntax "[]" : js_expr                           -- Empty array
syntax js_expr "[" js_expr "]" : js_expr        -- Bracket access
syntax js_expr "." ident : js_expr              -- Member dot access
syntax js_expr "(" (js_expr,*)? ")" : js_expr   -- Function calls
syntax "new " ident "(" (js_expr,*)? ")" : js_expr   -- New expression: new Foo(args)
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" : js_expr  -- Chained: new Foo().method(args)
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" "." ident : js_expr  -- Chained + prop: new Foo().method(args).prop
syntax "throw " js_expr : js_expr               -- Throw statements

-- Binary and Ternary operators with precedence
syntax:60 js_expr " + " js_expr : js_expr
syntax:60 js_expr " - " js_expr : js_expr
syntax:70 js_expr " * " js_expr : js_expr
syntax:70 js_expr " / " js_expr : js_expr
syntax:70 js_expr " % " js_expr : js_expr
syntax:70 js_expr " ^ " js_expr : js_expr
syntax:40 js_expr " == " js_expr : js_expr
syntax:40 js_expr " <= " js_expr : js_expr
syntax:40 js_expr " < " js_expr : js_expr
syntax:40 js_expr " > " js_expr : js_expr
syntax:50 js_expr " & " js_expr : js_expr
syntax:50 js_expr " >> " js_expr : js_expr
syntax:20 js_expr " ? " js_expr " : " js_expr : js_expr

-- 3. Define the top-level bracket syntax
syntax "⟪" js_expr "⟫" : term

-- 4. Macro rules to translate JS syntax to JsInlineExpr
macro_rules
  | `(⟪ #$n:num .$p:ident ⟫) => `(JsInlineExpr.memberDot (JsInlineExpr.funArg $n) $(Lean.quote p.getId.toString))
  | `(⟪ #$n:num ⟫) => `(JsInlineExpr.funArg $n)
  | `(⟪ $n:num ⟫) => `(JsInlineExpr.decimal $n)
  | `(⟪ $s:str ⟫) => `(JsInlineExpr.stringLiteral $s)
  | `(⟪ $id:ident ⟫) => `(JsInlineExpr.identifier $(quote id.getId.toString))
  | `(⟪ ($e) ⟫) => `(⟪ $e ⟫)
  | `(⟪ [] ⟫) => `(JsInlineExpr.arrayLiteral #[])
  | `(⟪ $obj[$idx] ⟫) => `(JsInlineExpr.memberSquare ⟪$obj⟫ ⟪$idx⟫)
  | `(⟪ $obj.$id:ident ⟫) => `(JsInlineExpr.memberDot ⟪$obj⟫ $(quote id.getId.toString))
  | `(⟪ $fn($[$args],*) ⟫) => `(JsInlineExpr.callExpression ⟪$fn⟫ #[$[⟪$args⟫],*])
  -- new Ctor(args)
  | `(⟪ new $cls:ident ($[$args],*) ⟫) =>
    `(JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[$[⟪$args⟫],*])
  -- new Ctor().method(args)
  | `(⟪ new $cls:ident () . $m:ident ($[$args],*) ⟫) =>
    `(JsInlineExpr.callExpression
        (JsInlineExpr.memberDot
          (JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[])
          $(Lean.quote m.getId.toString))
        #[$[⟪$args⟫],*])
  -- new Ctor().method(args).prop
  | `(⟪ new $cls:ident () . $m:ident ($[$args],*) . $prop:ident ⟫) =>
    `(JsInlineExpr.memberDot
        (JsInlineExpr.callExpression
          (JsInlineExpr.memberDot
            (JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[])
            $(Lean.quote m.getId.toString))
          #[$[⟪$args⟫],*])
        $(Lean.quote prop.getId.toString))
  | `(⟪ throw $e ⟫) => `(JsInlineExpr.throw ⟪$e⟫)

  -- Binary Operators
  | `(⟪ $a + $b ⟫)  => `(JsInlineExpr.expressionBinary .plus ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a - $b ⟫)  => `(JsInlineExpr.expressionBinary .minus ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a * $b ⟫)  => `(JsInlineExpr.expressionBinary .times ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a / $b ⟫)  => `(JsInlineExpr.expressionBinary .divide ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a % $b ⟫)  => `(JsInlineExpr.expressionBinary .mod ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a ^ $b ⟫)  => `(Lean.Compiler.JS.pow ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a == $b ⟫) => `(JsInlineExpr.expressionBinary .eq ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a <= $b ⟫) => `(JsInlineExpr.expressionBinary .le ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a < $b ⟫)  => `(JsInlineExpr.expressionBinary .lt ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a > $b ⟫)  => `(JsInlineExpr.expressionBinary .gt ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a & $b ⟫)  => `(JsInlineExpr.expressionBinary .bitAnd ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a >> $b ⟫) => `(JsInlineExpr.expressionBinary .rsh ⟪$a⟫ ⟪$b⟫)

  -- Ternary
  | `(⟪ $c ? $t : $e ⟫) => `(JsInlineExpr.expressionTernary ⟪$c⟫ ⟪$t⟫ ⟪$e⟫)

end Lean.Compiler.JS

namespace Lean.Compiler.JS.Impl

def isScalarObj := ⟪throw new Error("lean_is_scalar is not and should not be implemented")⟫
def sorryAx := ⟪throw new Error("lean_sorry is not and should not be implemented")⟫
def natAdd := ⟪#0 + #1⟫
def natMul := ⟪#0 * #1⟫
def natPow := ⟪#0 ^ #1⟫
def natDecEq := ⟪#0 == #1⟫
def natPred := ⟪(#0 > 0) ? (#0 - 1) : 0⟫
def natDecLe := ⟪#0 <= #1⟫
def natDecLt := ⟪#0 < #1⟫
def natSub := ⟪(#0 > #1) ? (#0 - #1) : 0⟫
def natDiv := ⟪(#1 > 0) ? (#0 / #1) : 0⟫
def natMod := ⟪(#1 > 0) ? (#0 % #1) : 0⟫
def systemPlatformGetNumBits := ⟪64⟫
def uint8OfNat := ⟪#0 & 0xFF⟫
def uint8DecEq := ⟪#0 == #1⟫
def uint8DecLt := ⟪#0 < #1⟫
def uint8DecLe := ⟪#0 <= #1⟫
def uint16OfNat := ⟪#0 & 0xFFFF⟫
def uint16DecEq := ⟪#0 == #1⟫
def uint32OfNat := ⟪#0 >> 0⟫
def uint32DecEq := ⟪#0 == #1⟫
def uint32DecLt := ⟪#0 < #1⟫
def uint32DecLe := ⟪#0 <= #1⟫
def uint64DecEq := ⟪#0 == #1⟫
def usizeDecEq := ⟪#0 == #1⟫
def mkEmptyArrayWithCapacity := ⟪[]⟫
def arrayGetSize := ⟪(#0).length⟫
def arrayGet := ⟪#0[#1]⟫
def mkEmptyByteArray := ⟪new Uint8Array(0)⟫
def byteArraySize := ⟪(#0).length⟫
def stringToUtf8 := ⟪new TextEncoder().encode(#0)⟫
def stringFromUtf8Unchecked := ⟪new TextDecoder().decode(#0)⟫
def stringMk := ⟪throw new Error("lean_string_mk should not be implemented")⟫
def stringDecEq := ⟪#0 == #1⟫
def floatOfScientific := ⟪throw new Error("lean_float_of_scientific is not and should not be implemented (we should just render floats?)")⟫
def stringUtf8ByteSize := ⟪new TextEncoder().encode(#0).length⟫

end Lean.Compiler.JS.Impl

namespace Lean.Compiler

structure JsExternInlinedEntry where
  decl : Name
  stx  : Syntax

builtin_initialize jsExternInlinedExt : SimplePersistentEnvExtension JsExternInlinedEntry (NameMap Syntax) ←
  registerSimplePersistentEnvExtension {
    name          := `js_extern_inlined_ext
    addImportedFn := fun as => as.foldl (init := {}) fun m as => as.foldl (init := m) fun m e => m.insert e.decl e.stx
    addEntryFn    := fun m e => m.insert e.decl e.stx
  }

private def getJsExternInlinedStx (stx : Syntax) : AttrM Syntax := do
  if stx.getKind == `Lean.Parser.Attr.js_extern_inlined then
    return stx[1]
  else if let some arg ← Attribute.Builtin.getIdent? stx then
    return arg
  else
    throwErrorAt stx "Unexpected attribute argument: expected a term"

builtin_initialize
  registerBuiltinAttribute {
    name := `js_extern_inlined
    descr := "inlined JS implementation for an external function"
    add := fun decl stx _ => do
      let arg ← getJsExternInlinedStx stx
      modifyEnv fun env => jsExternInlinedExt.addEntry env { decl, stx := arg }
  }

def getJsExternInlined? (env : Environment) (n : Name) : Option Syntax :=
  jsExternInlinedExt.getState env |>.find? n

def resolveBuiltinJsExternInlined? : Name → Option JS.JsInlineExpr
  | ``Lean.Compiler.JS.Impl.isScalarObj => some JS.Impl.isScalarObj
  | ``Lean.Compiler.JS.Impl.sorryAx => some JS.Impl.sorryAx
  | ``Lean.Compiler.JS.Impl.natAdd => some JS.Impl.natAdd
  | ``Lean.Compiler.JS.Impl.natMul => some JS.Impl.natMul
  | ``Lean.Compiler.JS.Impl.natPow => some JS.Impl.natPow
  | ``Lean.Compiler.JS.Impl.natDecEq => some JS.Impl.natDecEq
  | ``Lean.Compiler.JS.Impl.natPred => some JS.Impl.natPred
  | ``Lean.Compiler.JS.Impl.natDecLe => some JS.Impl.natDecLe
  | ``Lean.Compiler.JS.Impl.natDecLt => some JS.Impl.natDecLt
  | ``Lean.Compiler.JS.Impl.natSub => some JS.Impl.natSub
  | ``Lean.Compiler.JS.Impl.natDiv => some JS.Impl.natDiv
  | ``Lean.Compiler.JS.Impl.natMod => some JS.Impl.natMod
  | ``Lean.Compiler.JS.Impl.systemPlatformGetNumBits => some JS.Impl.systemPlatformGetNumBits
  | ``Lean.Compiler.JS.Impl.uint8OfNat => some JS.Impl.uint8OfNat
  | ``Lean.Compiler.JS.Impl.uint8DecEq => some JS.Impl.uint8DecEq
  | ``Lean.Compiler.JS.Impl.uint8DecLt => some JS.Impl.uint8DecLt
  | ``Lean.Compiler.JS.Impl.uint8DecLe => some JS.Impl.uint8DecLe
  | ``Lean.Compiler.JS.Impl.uint16OfNat => some JS.Impl.uint16OfNat
  | ``Lean.Compiler.JS.Impl.uint16DecEq => some JS.Impl.uint16DecEq
  | ``Lean.Compiler.JS.Impl.uint32OfNat => some JS.Impl.uint32OfNat
  | ``Lean.Compiler.JS.Impl.uint32DecEq => some JS.Impl.uint32DecEq
  | ``Lean.Compiler.JS.Impl.uint32DecLt => some JS.Impl.uint32DecLt
  | ``Lean.Compiler.JS.Impl.uint32DecLe => some JS.Impl.uint32DecLe
  | ``Lean.Compiler.JS.Impl.uint64DecEq => some JS.Impl.uint64DecEq
  | ``Lean.Compiler.JS.Impl.usizeDecEq => some JS.Impl.usizeDecEq
  | ``Lean.Compiler.JS.Impl.mkEmptyArrayWithCapacity => some JS.Impl.mkEmptyArrayWithCapacity
  | ``Lean.Compiler.JS.Impl.arrayGetSize => some JS.Impl.arrayGetSize
  | ``Lean.Compiler.JS.Impl.arrayGet => some JS.Impl.arrayGet
  | ``Lean.Compiler.JS.Impl.mkEmptyByteArray => some JS.Impl.mkEmptyByteArray
  | ``Lean.Compiler.JS.Impl.byteArraySize => some JS.Impl.byteArraySize
  | ``Lean.Compiler.JS.Impl.stringToUtf8 => some JS.Impl.stringToUtf8
  | ``Lean.Compiler.JS.Impl.stringFromUtf8Unchecked => some JS.Impl.stringFromUtf8Unchecked
  | ``Lean.Compiler.JS.Impl.stringMk => some JS.Impl.stringMk
  | ``Lean.Compiler.JS.Impl.stringDecEq => some JS.Impl.stringDecEq
  | ``Lean.Compiler.JS.Impl.floatOfScientific => some JS.Impl.floatOfScientific
  | ``Lean.Compiler.JS.Impl.stringUtf8ByteSize => some JS.Impl.stringUtf8ByteSize
  | _ => none

end Lean.Compiler

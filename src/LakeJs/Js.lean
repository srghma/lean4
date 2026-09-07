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
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section

namespace Lean.Compiler.JS

inductive JSBinOp where
  | and | bitAnd | bitOr | bitXor | divide | eq | ge | gt | in_ | instanceOf | le | lsh | lt | minus | mod | neq | of | or | plus | rsh | strictEq | strictNeq | times | ursh
  deriving Repr, BEq, Inhabited

inductive JSUnaryOp where
  | decr | delete | incr | minus | not | plus | tilde | typeof | void
  deriving Repr, BEq, Inhabited

mutual
  inductive JsInlineExpr where
    | funArg (idx : Nat) -- like De Bruijn indices, everything else is copied from https://hackage.haskell.org/package/language-javascript
    | identifier (name : String)
    | decimal (val : Nat)
    | hex (val : Nat) -- 0xFF for example, should be rendered as 0xFF too
    | stringLiteral (val : String)
    | boolLiteral (val : Bool)
    | arrayLiteral (elems : Array JsInlineExpr)
    | objectLiteral (fields : Array (String × JsInlineExpr))
    | callExpression (fn : JsInlineExpr) (args : Array JsInlineExpr)
    | memberDot (obj : JsInlineExpr) (name : String)
    | memberSquare (obj : JsInlineExpr) (idx : JsInlineExpr)
    | unaryExpression (op : JSUnaryOp) (arg : JsInlineExpr)
    | expressionBinary (op : JSBinOp) (lhs : JsInlineExpr) (rhs : JsInlineExpr)
    | expressionTernary (cond : JsInlineExpr) (thenExpr : JsInlineExpr) (elseExpr : JsInlineExpr)
    | memberNew (expr : JsInlineExpr) (args : Array JsInlineExpr)
    | throw (expr : JsInlineExpr)
    | arrowFunction (params : Array String) (body : JsInlineExpr)
    | arrowFunctionBlock (params : Array String) (body : Array JsInlineStmt)
    | isTag (obj : JsInlineExpr) (tag : Name)
    | getField (obj : JsInlineExpr) (idx : Nat)
    | mkObject (tag : Name) (fields : Array JsInlineExpr)
    deriving Repr, BEq, Inhabited

  inductive JsInlineStmt where
    | const (name : String) (val : JsInlineExpr)
    | letVar (name : String) (val : JsInlineExpr)
    | assign (lhs : JsInlineExpr) (rhs : JsInlineExpr)
    | expr (e : JsInlineExpr)
    | return (e : JsInlineExpr)
    | while (cond : JsInlineExpr) (body : Array JsInlineStmt)
    deriving Repr, BEq, Inhabited
end

public def mangleString (s : String) : String :=
  s.foldl (fun res c =>
    if c.isAlphanum then
      res.push c
    else if c == '.' then
      res.push '$'
    else if c == '_' then
      res ++ "__"
    else
      res ++ s!"_u{c.toNat.toUInt32.toNat}_"
  ) ""

public def mangleName (n : Name) : String :=
  mangleString n.toString

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

-- 1. Declare the syntax categories for our JS subset
declare_syntax_cat js_stmt
declare_syntax_cat js_expr

-- 2. Define the grammar for the category
syntax "#" num : js_expr                        -- Arguments: #0, #1
syntax "#" num "." ident : js_expr              -- Arg + property: #0.length (avoids decimal-point ambiguity)
syntax num : js_expr                            -- Literals: 64, 0xFF
syntax str : js_expr                            -- String literals
syntax ident : js_expr                          -- Identifiers: Error, Uint8Array
syntax "(" js_expr ")" : js_expr                -- Parentheses
syntax "[" (js_expr,*)? "]" : js_expr            -- Array literal: [], [a, b]
syntax js_expr "[" js_expr "]" : js_expr        -- Bracket access
syntax js_expr "." ident : js_expr              -- Member dot access
syntax js_expr "(" (js_expr,*)? ")" : js_expr   -- Function calls
syntax "new " ident "(" (js_expr,*)? ")" : js_expr   -- New expression: new Foo(args)
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" : js_expr  -- Chained: new Foo().method(args)
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" "." ident : js_expr  -- Chained + prop: new Foo().method(args).prop
syntax "throw " js_expr : js_expr               -- Throw statements

-- Unary operators
syntax "!" js_expr : js_expr
syntax "-" js_expr : js_expr
syntax "~" js_expr : js_expr

-- Binary and Ternary operators with precedence
syntax:30 js_expr " || " js_expr : js_expr
syntax:35 js_expr " && " js_expr : js_expr
syntax:40 js_expr " == " js_expr : js_expr
syntax:40 js_expr " === " js_expr : js_expr
syntax:40 js_expr " != " js_expr : js_expr
syntax:40 js_expr " !== " js_expr : js_expr
syntax:45 js_expr " <= " js_expr : js_expr
syntax:45 js_expr " < " js_expr : js_expr
syntax:45 js_expr " > " js_expr : js_expr
syntax:45 js_expr " >= " js_expr : js_expr
syntax:50 js_expr " | " js_expr : js_expr
syntax:55 js_expr " ^ " js_expr : js_expr
syntax:60 js_expr " & " js_expr : js_expr
syntax:65 js_expr " << " js_expr : js_expr
syntax:65 js_expr " >> " js_expr : js_expr
syntax:65 js_expr " >>> " js_expr : js_expr
syntax:70 js_expr " + " js_expr : js_expr
syntax:70 js_expr " - " js_expr : js_expr
syntax:80 js_expr " * " js_expr : js_expr
syntax:80 js_expr " / " js_expr : js_expr
syntax:80 js_expr " % " js_expr : js_expr
syntax:20 js_expr " ? " js_expr " : " js_expr : js_expr
syntax "({" (ident ":" js_expr),* "})" : js_expr
syntax "({})" : js_expr

-- Arrow function expressions
syntax "(" (ident,*)? ")" " => " js_expr : js_expr
syntax ident " => " js_expr : js_expr

-- Arrow function (block body)
syntax "(" (ident,*)? ")" " => " "{" js_stmt* "}" : js_expr

-- Statements
syntax "const " ident " = " js_expr (";")? : js_stmt
syntax "let " ident " = " js_expr (";")? : js_stmt
syntax js_expr " = " js_expr (";")? : js_stmt
syntax "return " js_expr (";")? : js_stmt
syntax "while " "(" js_expr ")" "{" js_stmt* "}" : js_stmt
syntax js_expr (";")? : js_stmt

-- Helper constructs requested by user
syntax "isTag" "(" js_expr "," Lean.Parser.nameLit ")" : js_expr
syntax "isTag" "(" js_expr "," ident ")" : js_expr
syntax "getField" "(" js_expr "," num ")" : js_expr
syntax "mkObject" "(" Lean.Parser.nameLit ("," js_expr)* ")" : js_expr
syntax "mkObject" "(" ident ("," js_expr)* ")" : js_expr

-- 3. Define top-level bracket syntax
syntax "[JS|" js_expr "]" : term
syntax "[JS_STMT|" js_stmt "]" : term

public meta def toJsIdent (n : Name) : MacroM (TSyntax `term) := do
  if n == `true then
    `(JsInlineExpr.boolLiteral true)
  else if n == `false then
    `(JsInlineExpr.boolLiteral false)
  else match n with
    | .str p member =>
      if p != .anonymous then
        let parent ← toJsIdent p
        `(JsInlineExpr.memberDot $parent $(quote member))
      else
        `(JsInlineExpr.identifier $(quote member))
    | _ => `(JsInlineExpr.identifier $(quote n.toString))

-- 4. Macro rules to translate JS syntax to JsInlineExpr
macro_rules
  | `([JS| #$n:num .$p:ident ]) => `(JsInlineExpr.memberDot (JsInlineExpr.funArg $n) $(Lean.quote p.getId.toString))
  | `([JS| #$n:num ]) => `(JsInlineExpr.funArg $n)
  | `([JS| $n:num ]) => `(JsInlineExpr.decimal $n)
  | `([JS| $s:str ]) => `(JsInlineExpr.stringLiteral $s)
  | `([JS| $id:ident ]) => toJsIdent id.getId
  | `([JS| ($e) ]) => `([JS| $e ])
  | `([JS| [ $[$elems],* ] ]) => `(JsInlineExpr.arrayLiteral #[$[[JS| $elems ]],*])
  | `([JS| $obj[$idx] ]) => `(JsInlineExpr.memberSquare [JS| $obj ] [JS| $idx ])
  | `([JS| $obj.$id:ident ]) => `(JsInlineExpr.memberDot [JS| $obj ] $(quote id.getId.toString))
  | `([JS| $fn($[$args],*) ]) => `(JsInlineExpr.callExpression [JS| $fn ] #[$[[JS| $args ]],*])
  -- new Ctor(args)
  | `([JS| new $cls:ident ($[$args],*) ]) =>
    `(JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[$[[JS| $args ]],*])
  -- new Ctor().method(args)
  | `([JS| new $cls:ident () . $m:ident ($[$args],*) ]) =>
    `(JsInlineExpr.callExpression
        (JsInlineExpr.memberDot
          (JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[])
          $(Lean.quote m.getId.toString))
        #[$[[JS| $args ]],*])
  -- new Ctor().method(args).prop
  | `([JS| new $cls:ident () . $m:ident ($[$args],*) . $prop:ident ]) =>
    `(JsInlineExpr.memberDot
        (JsInlineExpr.callExpression
          (JsInlineExpr.memberDot
            (JsInlineExpr.memberNew (JsInlineExpr.identifier $(Lean.quote cls.getId.toString)) #[])
            $(Lean.quote m.getId.toString))
          #[$[[JS| $args ]],*])
        $(Lean.quote prop.getId.toString))
  | `([JS| throw $e ]) => `(JsInlineExpr.throw [JS| $e ])

  -- Binary Operators
  -- Unary operators
  | `([JS| ! $a ])      => `(JsInlineExpr.unaryExpression .not [JS| $a ])
  | `([JS| - $a ])      => `(JsInlineExpr.unaryExpression .minus [JS| $a ])
  | `([JS| ~ $a ])      => `(JsInlineExpr.unaryExpression .tilde [JS| $a ])

  -- Binary operators
  | `([JS| $a || $b ])  => `(JsInlineExpr.expressionBinary .or [JS| $a ] [JS| $b ])
  | `([JS| $a && $b ])  => `(JsInlineExpr.expressionBinary .and [JS| $a ] [JS| $b ])
  | `([JS| $a != $b ])  => `(JsInlineExpr.expressionBinary .neq [JS| $a ] [JS| $b ])
  | `([JS| $a !== $b ]) => `(JsInlineExpr.expressionBinary .strictNeq [JS| $a ] [JS| $b ])
  | `([JS| $a >= $b ])  => `(JsInlineExpr.expressionBinary .ge [JS| $a ] [JS| $b ])
  | `([JS| $a | $b ])   => `(JsInlineExpr.expressionBinary .bitOr [JS| $a ] [JS| $b ])
  | `([JS| $a << $b ])  => `(JsInlineExpr.expressionBinary .lsh [JS| $a ] [JS| $b ])
  | `([JS| $a + $b ])   => `(JsInlineExpr.expressionBinary .plus [JS| $a ] [JS| $b ])
  | `([JS| $a - $b ])   => `(JsInlineExpr.expressionBinary .minus [JS| $a ] [JS| $b ])
  | `([JS| $a * $b ])   => `(JsInlineExpr.expressionBinary .times [JS| $a ] [JS| $b ])
  | `([JS| $a / $b ])   => `(JsInlineExpr.expressionBinary .divide [JS| $a ] [JS| $b ])
  | `([JS| $a % $b ])   => `(JsInlineExpr.expressionBinary .mod [JS| $a ] [JS| $b ])
  | `([JS| $a ^ $b ])   => `(Lean.Compiler.JS.pow [JS| $a ] [JS| $b ])
  | `([JS| $a == $b ])  => `(JsInlineExpr.expressionBinary .eq [JS| $a ] [JS| $b ])
  | `([JS| $a === $b ]) => `(JsInlineExpr.expressionBinary .strictEq [JS| $a ] [JS| $b ])
  | `([JS| $a <= $b ])  => `(JsInlineExpr.expressionBinary .le [JS| $a ] [JS| $b ])
  | `([JS| $a < $b ])   => `(JsInlineExpr.expressionBinary .lt [JS| $a ] [JS| $b ])
  | `([JS| $a > $b ])   => `(JsInlineExpr.expressionBinary .gt [JS| $a ] [JS| $b ])
  | `([JS| $a & $b ])   => `(JsInlineExpr.expressionBinary .bitAnd [JS| $a ] [JS| $b ])
  | `([JS| $a >> $b ])  => `(JsInlineExpr.expressionBinary .rsh [JS| $a ] [JS| $b ])
  | `([JS| $a >>> $b ]) => `(JsInlineExpr.expressionBinary .ursh [JS| $a ] [JS| $b ])

  -- Object literals
  | `([JS| ({}) ])      => `(JsInlineExpr.objectLiteral #[])
  | `([JS| ({ $[$keys:ident : $vals:js_expr],* }) ]) =>
    `(JsInlineExpr.objectLiteral #[ $[ ($(quote keys.getId.toString), [JS| $vals ]) ],* ])

  -- Ternary
  | `([JS| $c ? $t : $e ]) => `(JsInlineExpr.expressionTernary [JS| $c ] [JS| $t ] [JS| $e ])

  -- Arrow function expressions
  | `([JS| ($[$params],*) => $body:js_expr ]) =>
    let ps := quote (params.map fun p => p.getId.toString)
    `(JsInlineExpr.arrowFunction $ps [JS| $body ])
  | `([JS| $p:ident => $body:js_expr ]) =>
    `(JsInlineExpr.arrowFunction #[$(quote p.getId.toString)] [JS| $body ])

  -- Arrow function with block body
  | `([JS| ($[$params],*) => { $[$stmts:js_stmt]* } ]) =>
    let ps := quote (params.map fun p => p.getId.toString)
    `(JsInlineExpr.arrowFunctionBlock $ps #[$[[JS_STMT| $stmts ]],*])

  -- isTag
  | `([JS| isTag($obj, $tag:name) ]) =>
    `(JsInlineExpr.isTag [JS| $obj ] $(quote tag.getName))
  | `([JS| isTag($obj, $tag:ident) ]) =>
    `(JsInlineExpr.isTag [JS| $obj ] $(quote tag.getId))

  -- getField
  | `([JS| getField($obj, $idx:num) ]) =>
    `(JsInlineExpr.getField [JS| $obj ] $(quote idx.getNat))

  -- mkObject
  | `([JS| mkObject($tag:name $[, $fields:js_expr]* ) ]) =>
    `(JsInlineExpr.mkObject $(quote tag.getName) #[$[[JS| $fields ]],*])
  | `([JS| mkObject($tag:ident $[, $fields:js_expr]* ) ]) =>
    `(JsInlineExpr.mkObject $(quote tag.getId) #[$[[JS| $fields ]],*])

macro_rules
  | `([JS_STMT| const $x = $val:js_expr $[;]? ]) =>
    `(JsInlineStmt.const $(quote x.getId.toString) [JS| $val ])
  | `([JS_STMT| let $x = $val:js_expr $[;]? ]) =>
    `(JsInlineStmt.letVar $(quote x.getId.toString) [JS| $val ])
  | `([JS_STMT| $lhs:js_expr = $rhs:js_expr $[;]? ]) =>
    `(JsInlineStmt.assign [JS| $lhs ] [JS| $rhs ])
  | `([JS_STMT| return $val:js_expr $[;]? ]) =>
    `(JsInlineStmt.return [JS| $val ])
  | `([JS_STMT| while ($c:js_expr) { $[$body]* } ]) =>
    `(JsInlineStmt.while [JS| $c ] #[$[[JS_STMT| $body ]],*])
  | `([JS_STMT| $e:js_expr $[;]? ]) =>
    `(JsInlineStmt.expr [JS| $e ])

end Lean.Compiler.JS

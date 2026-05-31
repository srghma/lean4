import Init

inductive JSBinOp where | plus
inductive JSUnaryOp where | not
inductive JsInlineExpr where
  | funArg (idx : Nat)
  | memberDot (obj : JsInlineExpr) (name : String)
  | memberSquare (obj : JsInlineExpr) (idx : JsInlineExpr)
  | stringLiteral (val : String)
  | expressionBinary (op : JSBinOp) (lhs : JsInlineExpr) (rhs : JsInlineExpr)

declare_syntax_cat js_expr
syntax "#" num : js_expr
syntax "#" num "." ident : js_expr
syntax "(" js_expr ")" : js_expr
syntax str : js_expr
syntax js_expr "[" js_expr "]" : js_expr
syntax js_expr "." ident : js_expr

syntax "⟪" js_expr "⟫" : term

macro_rules
  | `(⟪ #$n:num .$p:ident ⟫) => `(JsInlineExpr.memberDot (JsInlineExpr.funArg $n) $(Lean.quote p.getId.toString))
  | `(⟪ #$n:num ⟫) => `(JsInlineExpr.funArg $n)
  | `(⟪ $s:str ⟫) => `(JsInlineExpr.stringLiteral $s)
  | `(⟪ ($e) ⟫) => `(⟪ $e ⟫)
  | `(⟪ $obj[$idx] ⟫) => `(JsInlineExpr.memberSquare ⟪$obj⟫ ⟪$idx⟫)
  | `(⟪ $obj.$id:ident ⟫) => `(JsInlineExpr.memberDot ⟪$obj⟫ $(Lean.quote id.getId.toString))

-- def test1 := ⟪#0.length⟫
def test2 := ⟪(#0).length⟫
def test3 := ⟪#0["length"]⟫
def test4 := ⟪#0 .length⟫

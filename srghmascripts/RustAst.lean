/-- Rust primitive scalar types. -/
inductive PrimitiveType
  | u8 | i8 | u16 | i16 | u32 | i32 | u64 | i64
  | u128 | i128 | isize | usize | f32 | f64
  | bool_ | str_ | char_
  deriving Repr, DecidableEq
 
def PrimitiveType.toString : PrimitiveType → String
  | .u8    => "u8"   | .i8    => "i8"
  | .u16   => "u16"  | .i16   => "i16"
  | .u32   => "u32"  | .i32   => "i32"
  | .u64   => "u64"  | .i64   => "i64"
  | .u128  => "u128" | .i128  => "i128"
  | .isize => "isize"| .usize => "usize"
  | .f32   => "f32"  | .f64   => "f64"
  | .bool_ => "bool" | .str_  => "str"  | .char_ => "char"
 
/-- An identifier (possibly raw `r#foo`). -/
structure Ident where
  name : String
  deriving Repr, DecidableEq, Inhabited
 
instance : ToString Ident := ⟨(·.name)⟩
 
/-- A lifetime `'a`. -/
structure Lifetime where
  name : String   -- without the leading `'`
  deriving Repr, DecidableEq
 
def Lifetime.toString (l : Lifetime) : String := "'" ++ l.name
 
/-- A label `'outer`. -/
structure Label where
  name : String
  deriving Repr, DecidableEq
 
def Label.toString (l : Label) : String := "'" ++ l.name
 
/-- Fragment specifiers inside macro_rules patterns. -/
inductive FragmentSpecifier
  | block | expr | expr2021 | ident | item | lifetime | literal
  | meta | pat | patParam | path | stmt | tt | ty | vis
  deriving Repr
 
def FragmentSpecifier.toString : FragmentSpecifier → String
  | .block    => "block" | .expr     => "expr"
  | .expr2021 => "expr_2021" | .ident => "ident"
  | .item     => "item"  | .lifetime => "lifetime"
  | .literal  => "literal" | .meta  => "meta"
  | .pat      => "pat"   | .patParam => "pat_param"
  | .path     => "path"  | .stmt    => "stmt"
  | .tt       => "tt"    | .ty      => "ty"
  | .vis      => "vis"
 
/-- Visibility modifier. -/
inductive Visibility
  | pub                  -- `pub`
  | pubCrate             -- `pub(crate)`
  | pubSelf              -- `pub(self)`
  | pubSuper             -- `pub(super)`
  | pubIn (path : String) -- `pub(in path)`
  | crateKw              -- bare `crate` (old-style)
  deriving Repr
 
def Visibility.toDoc : Visibility → Doc
  | .pub            => Doc.text "pub"
  | .pubCrate       => Doc.text "pub(crate)"
  | .pubSelf        => Doc.text "pub(self)"
  | .pubSuper       => Doc.text "pub(super)"
  | .pubIn p        => Doc.text s!"pub(in {p})"
  | .crateKw        => Doc.text "crate"
 
/-- Binary operators. -/
inductive BinOp
  | and | or | bitAnd | bitOr | bitXor
  | eq | ne | lt | le | gt | ge
  | shl | shr | add | sub | mul | div | rem
  deriving Repr
 
def BinOp.toString : BinOp → String
  | .and => "&&" | .or => "||"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
  | .gt => ">" | .ge => ">="
  | .shl => "<<" | .shr => ">>"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .rem => "%"
 
/-- Compound-assignment operators. -/
inductive CompoundOp
  | addEq | subEq | mulEq | divEq | remEq
  | andEq | orEq  | xorEq | shlEq | shrEq
  deriving Repr
 
def CompoundOp.toString : CompoundOp → String
  | .addEq => "+=" | .subEq => "-=" | .mulEq => "*="
  | .divEq => "/=" | .remEq => "%=" | .andEq => "&="
  | .orEq  => "|=" | .xorEq => "^=" | .shlEq => "<<=" | .shrEq => ">>="
 
/-- Unary operators. -/
inductive UnaryOp | neg | deref | not deriving Repr
 
def UnaryOp.toString : UnaryOp → String
  | .neg => "-" | .deref => "*" | .not => "!"
 
/-- Range operators. -/
inductive RangeOp | exclusive | inclusive | dotDotDot deriving Repr
 
def RangeOp.toString : RangeOp → String
  | .exclusive => ".." | .inclusive => "..=" | .dotDotDot => "..."
 
 
/-! ──────────────────────────────────────────────────────────────
    § 3  Mutually recursive AST  (Types, Expressions, Patterns,
         Statements, Items)
──────────────────────────────────────────────────────────────── -/
 
-- Forward declarations via `mutual`
mutual
 
  /-- A Rust type. -/
  inductive Ty
    | primitive  (p : PrimitiveType)
    | named      (id : Ident)
    | scoped     (path : Option ScopedPath) (name : Ident)
    | generic    (ty : Ty) (args : TypeArgs)
    | reference  (lt : Option Lifetime) (mut_ : Bool) (inner : Ty)
    | pointer    (const_ : Bool) (inner : Ty)     -- *const / *mut
    | array      (elem : Ty) (len : Option Expr)
    | slice      (elem : Ty)
    | tuple      (elems : List Ty)
    | unit
    | never
    | fn_        (mods : FnModifiers) (params : List Ty) (ret : Option Ty)
    | implTrait  (bound : TraitBound)
    | dynTrait   (bound : TraitBound)
    | bounded    (lhs rhs : Ty)
    | metavar    (name : String)
    | macro_     (inv : MacroInvocation)
    deriving Repr
 
  /-- A trait bound:  `: Trait + 'a + …` -/
  inductive TraitBound
    | bounds (items : List TraitBoundItem)
    deriving Repr
 
  inductive TraitBoundItem
    | ty       (t : Ty)
    | lifetime (l : Lifetime)
    | higherRanked (forLifetimes : List Lifetime) (t : Ty)
    deriving Repr
 
  /-- Type arguments `<A, B, 'a, …>`. -/
  inductive TypeArgs
    | args (items : List TypeArgItem)
    deriving Repr
 
  inductive TypeArgItem
    | ty       (t : Ty)
    | lifetime (l : Lifetime)
    | binding  (name : Ident) (t : Ty)
    | literal  (lit : Literal)
    | block    (b : Block)
    deriving Repr
 
  /-- A path for scoped resolution, e.g. `std::collections`. -/
  inductive ScopedPath
    | self_
    | super_
    | crate_
    | ident (id : Ident)
    | scoped (head : ScopedPath) (seg : Ident)
    | generic (head : ScopedPath) (args : TypeArgs)
    | bracketed (inner : Ty)
    deriving Repr
 
  /-- Literal values. -/
  inductive Literal
    | int_    (raw : String)
    | float_  (raw : String)
    | str_    (raw : String)
    | rawStr  (raw : String)
    | char_   (raw : String)
    | bool_   (b : Bool)
    deriving Repr
 
  /-- A block `{ stmts… expr? }`. -/
  inductive Block
    | mk (label : Option Label) (stmts : List Stmt) (tail : Option Expr)
    deriving Repr
 
  /-- A function modifier list. -/
  inductive FnModifiers
    | mods (async_ const_ unsafe_ default_ : Bool) (extern_ : Option (Option String))
    deriving Repr
 
  def FnModifiers.none : FnModifiers :=
    .mods false false false false none
 
  /-- A where-clause predicate. -/
  inductive WherePred
    | mk (lhs : Ty) (bounds : TraitBound)
    deriving Repr
 
  /-- Generic type parameters `<T : Trait, 'a, const N : usize>`. -/
  inductive TypeParams
    | params (items : List TypeParamItem)
    deriving Repr
 
  inductive TypeParamItem
    | ty        (name : Ident) (bounds : Option TraitBound) (default_ : Option Ty)
    | lifetime  (lt : Lifetime) (bounds : Option TraitBound)
    | const_    (name : Ident) (ty : Ty) (default_ : Option ConstParamDefault)
    | metavar   (name : String)
    deriving Repr
 
  inductive ConstParamDefault
    | block (b : Block) | ident (id : Ident) | literal (l : Literal)
    deriving Repr
 
  /-- A function parameter. -/
  inductive Param
    | named    (mut_ : Bool) (pat : Pat) (ty : Ty)
    | self_    (ref_ : Bool) (lt : Option Lifetime) (mut_ : Bool)
    | variadic (pat : Option Pat)
    | anon     (ty : Ty)
    deriving Repr
 
  /-- Patterns. -/
  inductive Pat
    | literal    (lit : Literal)
    | ident      (id : Ident)
    | primitive  (p : PrimitiveType)
    | scoped     (path : ScopedPath)
    | tuple      (pats : List Pat)
    | tupleStruct (ty : ScopedPath) (pats : List Pat)
    | struct_    (ty : Ident) (fields : List FieldPat)
    | slice      (pats : List Pat)
    | ref_       (inner : Pat)
    | mut_       (inner : Pat)
    | captured   (name : Ident) (inner : Pat)
    | reference  (mut_ : Bool) (inner : Pat)
    | range      (lo : Option RangePat) (op : RangeOp) (hi : Option RangePat)
    | or         (alts : List Pat)
    | rest                            -- `..`
    | wildcard                        -- `_`
    | constBlock (b : Block)
    | macro_     (inv : MacroInvocation)
    deriving Repr
 
  inductive RangePat | literal (l : Literal) | path (p : ScopedPath) deriving Repr
 
  inductive FieldPat
    | shorthand (ref_ mut_ : Bool) (name : Ident)
    | full      (ref_ mut_ : Bool) (name : Ident) (pat : Pat)
    | remaining
    deriving Repr
 
  /-- Expressions. -/
  inductive Expr
    -- literals & paths
    | literal    (l : Literal)
    | ident      (id : Ident)
    | primitive  (p : PrimitiveType)
    | self_
    | scoped     (path : ScopedPath)
    | metavar    (name : String)
    -- operators
    | unary      (op : UnaryOp) (e : Expr)
    | binary     (op : BinOp) (l r : Expr)
    | assign     (l r : Expr)
    | compoundAssign (op : CompoundOp) (l r : Expr)
    | cast       (e : Expr) (ty : Ty)
    | try_       (e : Expr)
    | range      (lo : Option Expr) (op : RangeOp) (hi : Option Expr)
    | range_     -- bare `..`
    -- calls
    | call       (fn : Expr) (args : List Expr)
    | methodCall (recv : Expr) (method : Ident) (turbofish : Option TypeArgs) (args : List Expr)
    | field      (recv : Expr) (field : Ident)
    | index      (recv : Expr) (idx : Expr)
    | await      (e : Expr)
    -- closures & blocks
    | closure    (static_ async_ move_ : Bool) (params : List ClosureParam) (ret : Option Ty) (body : ClosureBody)
    | block      (b : Block)
    | unsafeBlock (b : Block)
    | asyncBlock  (move_ : Bool) (b : Block)
    | genBlock    (move_ : Bool) (b : Block)
    | tryBlock    (b : Block)
    | constBlock  (b : Block)
    -- control flow
    | if_        (cond : Condition) (then_ : Block) (else_ : Option ElseClause)
    | match_     (val : Expr) (arms : List MatchArm)
    | while_     (label : Option Label) (cond : Condition) (body : Block)
    | loop_      (label : Option Label) (body : Block)
    | for_       (label : Option Label) (pat : Pat) (iter : Expr) (body : Block)
    | return_    (val : Option Expr)
    | yield_     (val : Option Expr)
    | break_     (label : Option Label) (val : Option Expr)
    | continue_  (label : Option Label)
    -- constructors
    | array      (elems : ArrayExprKind)
    | tuple      (elems : List Expr)
    | unit
    | struct_    (name : StructExprName) (fields : List FieldInit)
    -- generics
    | genericFn  (fn : Expr) (args : TypeArgs)
    -- macros
    | macro_     (inv : MacroInvocation)
    | reference  (raw : Bool) (const_ : Bool) (mut_ : Bool) (e : Expr)
    deriving Repr
 
  inductive ArrayExprKind
    | list   (elems : List Expr)
    | repeat (elem : Expr) (len : Expr)
    deriving Repr
 
  inductive ClosureParam
    | pat   (p : Pat)
    | typed (p : Pat) (ty : Ty)
    deriving Repr
 
  inductive ClosureBody
    | expr  (e : Expr)
    | block (b : Block)
    | hole         -- `_`
    deriving Repr
 
  inductive Condition
    | expr    (e : Expr)
    | let_    (pat : Pat) (val : Expr)
    | letChain (items : List LetChainItem)
    deriving Repr
 
  inductive LetChainItem
    | expr (e : Expr)
    | let_ (pat : Pat) (val : Expr)
    deriving Repr
 
  inductive ElseClause
    | block  (b : Block)
    | elseIf (e : Expr)   -- the if_expression
    deriving Repr
 
  inductive MatchArm
    | mk (pat : Pat) (guard : Option Condition) (val : Expr)
    deriving Repr
 
  inductive StructExprName
    | named  (id : Ident)
    | scoped (sp : ScopedPath) (name : Ident)
    | turbofish (id : Ident) (args : TypeArgs)
    deriving Repr
 
  inductive FieldInit
    | shorthand (id : Ident)
    | full      (field : Ident) (val : Expr)
    | base      (e : Expr)             -- `..expr`
    deriving Repr
 
  /-- A statement. -/
  inductive Stmt
    | expr     (e : Expr) (semi : Bool)  -- semi=true → has trailing `;`
    | let_     (mut_ : Bool) (pat : Pat) (ty : Option Ty)
               (val : Option Expr) (else_ : Option Block)
    | item     (it : Item)
    | empty
    deriving Repr
 
  /-- A macro invocation `foo!(…)`. -/
  inductive MacroInvocation
    | mk (path : ScopedPath) (tokens : TokenTree)
    deriving Repr
 
  /-- A token tree (opaque interior). -/
  inductive TokenTree
    | parens   (content : String)
    | brackets (content : String)
    | braces   (content : String)
    deriving Repr
 
  /-- A macro_rules rule:  `pattern => body`. -/
  inductive MacroRule
    | mk (pattern : TokenTree) (body : TokenTree)
    deriving Repr
 
  /-- Top-level items. -/
  inductive Item
    -- modules
    | mod       (vis : Option Visibility) (name : Ident) (body : Option (List Item))
    | foreignMod (unsafe_ : Bool) (abi : Option String) (items : List Item)
    -- types
    | struct_   (vis : Option Visibility) (name : Ident) (typeParams : Option TypeParams)
                (where_ : Option (List WherePred)) (body : StructBody)
    | union_    (vis : Option Visibility) (name : Ident) (typeParams : Option TypeParams)
                (where_ : Option (List WherePred)) (fields : List FieldDecl)
    | enum_     (vis : Option Visibility) (name : Ident) (typeParams : Option TypeParams)
                (where_ : Option (List WherePred)) (variants : List EnumVariant)
    | typeAlias (vis : Option Visibility) (name : Ident) (typeParams : Option TypeParams)
                (where_ : Option (List WherePred)) (ty : Ty)
    -- functions
    | fn_       (vis : Option Visibility) (mods : FnModifiers) (name : Ident)
                (typeParams : Option TypeParams) (params : List Param)
                (ret : Option Ty) (where_ : Option (List WherePred)) (body : Block)
    | fnSig     (vis : Option Visibility) (mods : FnModifiers) (name : Ident)
                (typeParams : Option TypeParams) (params : List Param)
                (ret : Option Ty) (where_ : Option (List WherePred))
    -- traits & impls
    | trait_    (vis : Option Visibility) (unsafe_ : Bool) (name : Ident)
                (typeParams : Option TypeParams) (bounds : Option TraitBound)
                (where_ : Option (List WherePred)) (items : List Item)
    | impl_     (unsafe_ : Bool) (typeParams : Option TypeParams)
                (traitRef : Option ImplTrait) (ty : Ty)
                (where_ : Option (List WherePred)) (items : List Item)
    | assocType (name : Ident) (typeParams : Option TypeParams)
                (bounds : Option TraitBound) (where_ : Option (List WherePred))
    -- misc
    | const_    (vis : Option Visibility) (name : Ident) (ty : Ty) (val : Option Expr)
    | static_   (vis : Option Visibility) (ref_ mut_ : Bool) (name : Ident)
                (ty : Ty) (val : Option Expr)
    | use_      (vis : Option Visibility) (tree : UseTree)
    | externCrate (vis : Option Visibility) (name : Ident) (alias : Option Ident)
    | attribute  (inner : Bool) (attr : Attribute)
    | macro_     (inv : MacroInvocation)
    | macroDef   (name : Ident) (rules : List MacroRule)
    deriving Repr
 
  inductive ImplTrait
    | positive (ty : Ty)
    | negative (ty : Ty)
    deriving Repr
 
  inductive StructBody
    | unit
    | tuple  (fields : List TupleField)
    | record (fields : List FieldDecl)
    deriving Repr
 
  inductive TupleField
    | mk (vis : Option Visibility) (ty : Ty)
    deriving Repr
 
  inductive FieldDecl
    | mk (vis : Option Visibility) (name : Ident) (ty : Ty)
    deriving Repr
 
  inductive EnumVariant
    | mk (vis : Option Visibility) (name : Ident) (body : StructBody) (disc : Option Expr)
    deriving Repr
 
  inductive UseTree
    | path     (seg : Ident) (child : UseTree)
    | name     (id : Ident)
    | alias    (id : Ident) (alias : Ident)
    | glob
    | list     (trees : List UseTree)
    | self_
    deriving Repr
 
  inductive Attribute
    | mk (path : ScopedPath) (value : Option AttrValue)
    deriving Repr
 
  inductive AttrValue
    | eq    (e : Expr)
    | args  (tt : TokenTree)
    deriving Repr
 
end  -- mutual
 
 
/-- A Rust source file. -/
structure SourceFile where
  shebang : Option String
  items   : List Item
  deriving Repr

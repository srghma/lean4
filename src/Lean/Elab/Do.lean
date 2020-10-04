/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.Quotation
import Lean.Elab.Match

namespace Lean
namespace Elab
namespace Term
open Meta

@[builtinTermElab liftMethod] def elabLiftMethod : TermElab :=
fun stx _ =>
  throwErrorAt stx "invalid use of `(<- ...)`, must be nested inside a 'do' expression"

private partial def hasLiftMethod : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.do then false
  else if k == `Lean.Parser.Term.doSeqIndent then false
  else if k == `Lean.Parser.Term.doSeqBracketed then false
  else if k == `Lean.Parser.Term.quot then false
  else if k == `Lean.Parser.Term.liftMethod then true
  else args.any hasLiftMethod
| _ => false

structure ExtractMonadResult :=
(m           : Expr)
(α           : Expr)
(hasBindInst : Expr)

private def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
u ← getLevel type;
let id        := Lean.mkConst `Id [u];
let idBindVal := Lean.mkConst `Id.hasBind [u];
pure { m := id, hasBindInst := idBindVal, α := type }

private def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
match expectedType? with
| none => throwError "invalid do notation, expected type is not available"
| some expectedType => do
  type ← withReducible $ whnf expectedType;
  when type.getAppFn.isMVar $ throwError "invalid do notation, expected type is not available";
  match type with
  | Expr.app m α _ =>
    catch
      (do
        bindInstType ← mkAppM `HasBind #[m];
        bindInstVal  ← synthesizeInst bindInstType;
        pure { m := m, hasBindInst := bindInstVal, α := α })
      (fun ex => mkIdBindFor type)
  | _ => mkIdBindFor type

namespace Do

/- A `doMatch` alternative. `vars` is the array of variables declared by `patterns`. -/
structure Alt (σ : Type) :=
(ref : Syntax) (vars : Array Name) (patterns : Array Syntax) (rhs : σ)

/-
  Auxiliary datastructure for representing a `do` code block, and compiling "reassignments" (e.g., `x := x + 1`).
  We convert `Code` into a `Syntax` term representing the:
  - `do`-block, or
  - the visitor argument for the `forIn` combinator.

  We say the following constructors are terminals:
  - `break`:    for interrupting a `for x in s`
  - `continue`: for interrupting the current iteration of a `for x in s`
  - `return`:   returning the result of the computation.
  - `ite`:      if-then-else
  - `match`:    pattern matching
  - `jmp`       a goto to a join-point

  We say the terminals `break`, `continue` and `return` are "exit points"

  The terminal `return` also contains the name of the variable containing the result of the computation.
  We ignore this value when inside a `for x in s`.

  - `decl` represents all declaration-like `doElem`s (e.g., `let`, `have`, `let rec`). The field `stx` is the actual `doElem`,
     `vars` is the array of variables declared by it, and `cont` is the next instruction in the `do` code block.
     `vars` is an array since we have declarations such as `let (a, b) := s`.

  - `reassign` is an reassignment-like `doElem` (e.g., `x := x + 1`).

  - `joinpoint` is a join point declaration: an auxiliary `let`-declaration used to represent the control-flow.

  - `action` is an action-like `doElem` (e.g., `IO.println "hello"`, `dbgTrace! "foo"`).

  A code block `C` is well-formed if
  - For every `jmp ref j as` in `C`, there is a `joinpoint j ps b k` and `jmp ref j as` is in `k`, and
    `ps.size == as.size` -/
inductive Code
| decl       (xs : Array Name) (stx : Syntax) (cont : Code)
| reassign   (xs : Array Name) (stx : Syntax) (cont : Code)
/- The Boolean value in `params` indicates whether we should use `(x : typeof! x)` when generating term Syntax or not -/
| joinpoint  (name : Name) (params : Array (Name × Bool)) (body : Code) (cont : Code)
| action     (stx : Syntax) (cond : Code)
| «break»    (ref : Syntax)
| «continue» (ref : Syntax)
| «return»   (ref : Syntax) (x? : Option Name)
/- Recall that an if-then-else may declare a variable using `optIdent` for the branches `thenBranch` and `elseBranch`. We store the variable name at `var?`. -/
| ite        (ref : Syntax) (h? : Option Name) (optIdent : Syntax) (cond : Syntax) (thenBranch : Code) (elseBranch : Code)
| «match»    (ref : Syntax) (discrs : Array Syntax) (type? : Option Syntax) (alts : Array (Alt Code))
| jmp        (ref : Syntax) (jpName : Name) (args : Array Name)

instance Code.inhabited : Inhabited Code :=
⟨Code.«break» (arbitrary _)⟩

instance Alt.inhabited : Inhabited (Alt Code) :=
⟨{ ref := arbitrary _, vars := #[], patterns := #[], rhs := arbitrary _ }⟩

/- A code block, and the collection of variables updated by it. -/
structure CodeBlock :=
(code  : Code)
(uvars : NameSet := {}) -- set of variables updated by `code`

private def varsToMessageData (vars : Array Name) : MessageData :=
MessageData.joinSep (vars.toList.map fun n => MessageData.ofName (n.simpMacroScopes)) " "

partial def toMessageDataAux (updateVars : MessageData) : Code → MessageData
| Code.decl xs _ k            => "let " ++ varsToMessageData xs ++ " := ... " ++ Format.line ++ toMessageDataAux k
| Code.reassign xs _ k        => varsToMessageData xs ++ " := ... " ++ Format.line ++ toMessageDataAux k
| Code.joinpoint n ps body k  =>
  "let " ++ n.simpMacroScopes ++ " " ++ varsToMessageData (ps.map Prod.fst) ++ " := " ++ indentD (toMessageDataAux body)
  ++ Format.line ++ toMessageDataAux k
| Code.action e k           => e ++ Format.line ++ toMessageDataAux k
| Code.ite _ _ _ c t e      => "if " ++ c ++ " then " ++ indentD (toMessageDataAux t) ++ Format.line ++ "else " ++ indentD (toMessageDataAux e)
| Code.jmp _ j xs           => "jmp " ++ j.simpMacroScopes ++ " " ++ toString xs.toList
| Code.«break» _            => "break " ++ updateVars
| Code.«continue» _         => "continue " ++ updateVars
| Code.«return» _ none      => "return " ++ updateVars
| Code.«return» _ (some x)  => "return " ++ x.simpMacroScopes ++ " " ++ updateVars
| Code.«match» _ ds t alts  =>
  "match " ++ MessageData.joinSep (ds.toList.map MessageData.ofSyntax) ", " ++ " with " ++
    alts.foldl
      (fun (acc : MessageData) (alt : Alt Code) =>
        acc ++ Format.line ++ "| "
        ++ MessageData.joinSep (alt.patterns.toList.map MessageData.ofSyntax) ", "
        ++ " => " ++ toMessageDataAux alt.rhs)
      Format.nil

private def nameSetToArray (s : NameSet) : Array Name :=
s.fold (fun (xs : Array Name) x => xs.push x) #[]

def CodeBlock.toMessageData (c : CodeBlock) : MessageData :=
let us := (nameSetToArray c.uvars).toList.map MessageData.ofName;
toMessageDataAux (MessageData.ofList us) c.code

partial def hasExitPoint : Code → Bool
| Code.decl _ _ k         => hasExitPoint k
| Code.reassign _ _ k     => hasExitPoint k
| Code.joinpoint _ _ b k  => hasExitPoint b || hasExitPoint k
| Code.action _ k         => hasExitPoint k
| Code.ite _ _ _ _ t e    => hasExitPoint t || hasExitPoint e
| Code.jmp _ _ _          => false
| Code.«break» _          => true
| Code.«continue» _       => true
| Code.«return» _ _       => true
| Code.«match» _ _ _ alts => alts.any fun alt => hasExitPoint alt.rhs

partial def hasContinueBreak : Code → Bool
| Code.decl _ _ k         => hasContinueBreak k
| Code.reassign _ _ k     => hasContinueBreak k
| Code.joinpoint _ _ b k  => hasContinueBreak b || hasContinueBreak k
| Code.action _ k         => hasContinueBreak k
| Code.ite _ _ _ _ t e    => hasContinueBreak t || hasContinueBreak e
| Code.jmp _ _ _          => false
| Code.«break» _          => true
| Code.«continue» _       => true
| Code.«return» _ _       => false
| Code.«match» _ _ _ alts => alts.any fun alt => hasContinueBreak alt.rhs

partial def convertReturnIntoJmpAux (jp : Name) (xs : Array Name) : Code → Code
| Code.decl xs stx k         => Code.decl xs stx $ convertReturnIntoJmpAux k
| Code.reassign xs stx k     => Code.reassign xs stx $ convertReturnIntoJmpAux k
| Code.joinpoint n ps b k    => Code.joinpoint n ps (convertReturnIntoJmpAux b) (convertReturnIntoJmpAux k)
| Code.action e k            => Code.action e $ convertReturnIntoJmpAux k
| Code.ite ref x? h c t e    => Code.ite ref x? h c (convertReturnIntoJmpAux t) (convertReturnIntoJmpAux e)
| Code.«match» ref ds t alts => Code.«match» ref ds t $ alts.map fun alt => { alt with rhs := convertReturnIntoJmpAux alt.rhs }
| Code.«return» ref _        => Code.jmp ref jp xs
| c                          => c

/- Convert `return _ x` instructions in `c` into `jmp _ jp xs`. -/
def convertReturnIntoJmp (c : Code) (jp : Name) (xs : Array Name) : Code :=
convertReturnIntoJmpAux jp xs c

structure JPDecl :=
(name : Name) (params : Array (Name × Bool)) (body : Code)

def attachJP (jpDecl : JPDecl) (k : Code) : Code :=
Code.joinpoint jpDecl.name jpDecl.params jpDecl.body k

def attachJPs (jpDecls : Array JPDecl) (k : Code) : Code :=
jpDecls.foldr attachJP k

def mkFreshJP (ps : Array (Name × Bool)) (body : Code) : TermElabM JPDecl := do
name ← mkFreshUserName `jp;
pure { name := name, params := ps, body := body }

def mkFreshJP' (xs : Array Name) (body : Code) : TermElabM JPDecl :=
mkFreshJP (xs.map fun x => (x, true)) body

def addFreshJP (ps : Array (Name × Bool)) (body : Code) : StateRefT (Array JPDecl) TermElabM Name := do
jp ← liftM $ mkFreshJP ps body;
modify fun (jps : Array JPDecl) => jps.push jp;
pure jp.name

def addFreshJP' (xs : Array Name) (body : Code) : StateRefT (Array JPDecl) TermElabM Name :=
addFreshJP (xs.map fun x => (x, true)) body

def insertVars (rs : NameSet) (xs : Array Name) : NameSet :=
xs.foldl (fun (rs : NameSet) x => rs.insert x) rs

def eraseVars (rs : NameSet) (xs : Array Name) : NameSet :=
xs.foldl (fun (rs : NameSet) x => rs.erase x) rs

def eraseOptVar (rs : NameSet) (x? : Option Name) : NameSet :=
match x? with
| none   => rs
| some x => rs.insert x

/- `pullExitPointsAux rs c` auxiliary method for `pullExitPoints`, `rs` is the set of update variable in the current path.  -/
partial def pullExitPointsAux : NameSet → Code → StateRefT (Array JPDecl) TermElabM Code
| rs, Code.decl xs stx k         => Code.decl xs stx <$> pullExitPointsAux (eraseVars rs xs) k
| rs, Code.reassign xs stx k     => Code.reassign xs stx <$> pullExitPointsAux (insertVars rs xs) k
| rs, Code.joinpoint j ps b k    => Code.joinpoint j ps <$> pullExitPointsAux rs b <*> pullExitPointsAux rs k
| rs, Code.action e k            => Code.action e <$> pullExitPointsAux rs k
| rs, Code.ite ref x? o c t e    => Code.ite ref x? o c <$> pullExitPointsAux (eraseOptVar rs x?) t <*> pullExitPointsAux (eraseOptVar rs x?) e
| rs, Code.«match» ref ds t alts => Code.«match» ref ds t <$> alts.mapM fun alt => do
  rhs ← pullExitPointsAux (eraseVars rs alt.vars) alt.rhs; pure { alt with rhs := rhs }
| rs, c@(Code.jmp _ _ _)     => pure c
| rs, Code.«break» ref           => do let xs := nameSetToArray rs; jp ← addFreshJP' xs (Code.«break» ref); pure $ Code.jmp ref jp xs
| rs, Code.«continue» ref        => do let xs := nameSetToArray rs; jp ← addFreshJP' xs (Code.«continue» ref); pure $ Code.jmp ref jp xs
| rs, Code.«return» ref y?       => do
  let xs := nameSetToArray rs;
  let ps := xs.map fun x => (x, true);
  (ps, xs, y?) ← match y? with
    | none   => pure (ps, xs, none)
    | some y =>
      if rs.contains y then pure (ps, xs, some y)
      else do {
        yFresh ← mkFreshUserName y;
        pure (ps.push (yFresh, false), xs.push y, some yFresh)
      };
  jp ← addFreshJP ps (Code.«return» ref y?);
  pure $ Code.jmp ref jp xs

/-
Auxiliary operation for adding new variables to `c.uvars` (updated variables).
When a new variable is not already in `c.uvars`, but is shadowed by some declaration in `c.code`,
we create auxiliary join points to make sure we preserve the semantics of the code block.
Example: suppose we have the code block `print x; let x := 10; return x`. And we want to extend it
with the reassignment `x := x + 1`. We first use `pullExitPoints` to create
```
let jp (x!1) :=  return x!1;
print x;
let x := 10;
jmp jp x
```
and then we add the reassignment
```
x := x + 1
let jp (x!1) := return x!1;
print x;
let x := 10;
jmp jp x
```
Note that we created a fresh variable `x!1` to avoid accidental name capture.

```
print x;
let x := 10
y := y + 1;
return x;
```
We transform it into
```
let jp (y x!1) := return x!1;
print x;
let x := 10
y := y + 1;
jmp jp y x
```
and then we add the reassignment as in the previous example.
We need to include `y` in the jump, because each exit point is implicitly returning the set of
update variables.

We implement the method as follows. Let `us` be `c.uvars`, then
1- for each `return _ y` in `c`, we create a join point
  `let j (us y!1) := return y!1`
   and replace the `return _ y` with `jmp us y`
2- for each `break`, we create a join point
  `let j (us) := break`
   and replace the `break` with `jmp us`.
3- Same as 2 for `continue`.
-/
def pullExitPoints (c : Code) : TermElabM Code :=
if hasExitPoint c then do
  (c, jpDecls) ← (pullExitPointsAux {} c).run #[];
  pure $ attachJPs jpDecls c
else
  pure c

partial def extendUpdatedVarsAux (ws : NameSet) : Code → TermElabM Code
| Code.joinpoint j ps b k        => Code.joinpoint j ps <$> extendUpdatedVarsAux b <*> extendUpdatedVarsAux k
| Code.action e k                => Code.action e <$> extendUpdatedVarsAux k
| c@(Code.«match» ref ds t alts) =>
  if alts.any fun alt => alt.vars.any fun x => ws.contains x then
    -- If a pattern variable is shadowing a variable in ws, we `pullExitPoints`
    pullExitPoints c
  else
    Code.«match» ref ds t <$> alts.mapM fun alt => do rhs ← extendUpdatedVarsAux alt.rhs; pure { alt with rhs := rhs }
| Code.ite ref none o c t e =>
  Code.ite ref none o c <$> extendUpdatedVarsAux t <*> extendUpdatedVarsAux e
| c@(Code.ite ref (some h) o cond t e) =>
  if ws.contains h then
    -- if the `h` at `if h:c then t else e` shadows a variable in `ws`, we `pullExitPoints`
    pullExitPoints c
  else
    Code.ite ref (some h) o cond <$> extendUpdatedVarsAux t <*> extendUpdatedVarsAux e
| Code.reassign xs stx k => Code.reassign xs stx <$> extendUpdatedVarsAux k
| c@(Code.decl xs stx k) =>
  if xs.any fun x => ws.contains x then
    -- One the declared variables is shadowing a variable in `ws`
    pullExitPoints c
  else
    Code.decl xs stx <$> extendUpdatedVarsAux k
| c => pure c

/-
Extend the set of updated variables. It assumes `ws` is a super set of `c.uvars`.
We **cannot** simply update the field `c.uvars`, because `c` may have shadowed some variable in `ws`.
See discussion at `pullExitPoints`.
-/
def extendUpdatedVars (c : CodeBlock) (ws : NameSet) : TermElabM CodeBlock :=
if ws.any fun x => !c.uvars.contains x then do
  -- `ws` contains a variable that is not in `c.uvars`, but in `c.dvars` (i.e., it has been shadowed)
  code ← extendUpdatedVarsAux ws c.code;
  pure { code := code, uvars := ws }
else
  pure { c with uvars := ws }

private def union (s₁ s₂ : NameSet) : NameSet :=
s₁.fold (fun (s : NameSet) x => s.insert x) s₂

/-
Given two code blocks `c₁` and `c₂`, make sure they have the same set of updated variables.
Let `ws` the union of the updated variables in `c₁‵ and ‵c₂`.
We use `extendUpdatedVars c₁ ws` and `extendUpdatedVars c₂ ws`
-/
def homogenize (c₁ c₂ : CodeBlock) : TermElabM (CodeBlock × CodeBlock) := do
let ws := union c₁.uvars c₂.uvars;
c₁ ← extendUpdatedVars c₁ ws;
c₂ ← extendUpdatedVars c₂ ws;
pure (c₁, c₂)

/-
Extending code blocks with variable declarations: `let x : t := v` and `let x : t ← v`.
We remove `x` from the collection of updated varibles.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `let (x, y) := t`
-/
def mkVarDeclCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : CodeBlock :=
{ code := Code.decl xs stx c.code, uvars := eraseVars c.uvars xs }

/-
Extending code blocks with reassignments: `x : t := v` and `x : t ← v`.
Remark: `stx` is the syntax for the declaration (e.g., `letDecl`), and `xs` are the variables
declared by it. It is an array because we have let-declarations that declare multiple variables.
Example: `(x, y) ← t`
-/
def mkReassignCore (xs : Array Name) (stx : Syntax) (c : CodeBlock) : TermElabM CodeBlock := do
let us := c.uvars;
let ws := insertVars us xs;
-- If `xs` contains a new updated variable, then we must use `extendUpdatedVars`.
-- See discussion at `pullExitPoints`
code ← if xs.any fun x => !us.contains x then extendUpdatedVarsAux ws c.code else pure c.code;
pure { code := Code.reassign xs stx code, uvars := ws }

def mkAction (action : Syntax) (c : CodeBlock) : CodeBlock :=
{ c with code := Code.action action c.code }

def mkReturn (ref : Syntax) (x? : Option Name := none) : CodeBlock :=
{ code := Code.«return» ref x? }

def mkBreak (ref : Syntax) : CodeBlock :=
{ code := Code.«break» ref }

def mkContinue (ref : Syntax) : CodeBlock :=
{ code := Code.«continue» ref }

def mkIte (ref : Syntax) (optIdent : Syntax) (cond : Syntax) (thenBranch : CodeBlock) (elseBranch : CodeBlock) : TermElabM CodeBlock := do
let x? := if optIdent.isNone then none else some (optIdent.getArg 0).getId;
(thenBranch, elseBranch) ← homogenize thenBranch elseBranch;
pure {
  code  := Code.ite ref x? optIdent cond thenBranch.code elseBranch.code,
  uvars := thenBranch.uvars,
}

/- Return a code block that executes `terminal` and then `k`.
   This method assumes `terminal` is a terminal -/
def concat (terminal : CodeBlock) (k : CodeBlock) : TermElabM CodeBlock := do
(terminal, k) ← homogenize terminal k;
let xs := nameSetToArray k.uvars;
jpDecl ← mkFreshJP' xs k.code;
let jp := jpDecl.name;
pure {
  code  := attachJP jpDecl (convertReturnIntoJmp terminal.code jp xs),
  uvars := terminal.uvars,
}

def mkWhen (ref : Syntax) (cond : Syntax) (c : CodeBlock) : CodeBlock :=
{ c with code := Code.ite ref none mkNullNode cond c.code (Code.«return» ref none) }

def mkUnless (ref : Syntax) (cond : Syntax) (c : CodeBlock) : CodeBlock :=
{ c with code := Code.ite ref none mkNullNode cond (Code.«return» ref none) c.code }

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
if doSeq.getKind == `Lean.Parser.Term.doSeqBracketed then
  (doSeq.getArg 1).getArgs.getSepElems.toList
else if doSeq.getKind == `Lean.Parser.Term.doSeqIndent then
  (doSeq.getArg 0).getArgs.getSepElems.toList
else
  []

private def getDoSeq (doStx : Syntax) : Syntax :=
doStx.getArg 1

def getLetIdDeclVar (letIdDecl : Syntax) : Name :=
(letIdDecl.getArg 0).getId

def getLetPatDeclVars (letPatDecl : Syntax) : TermElabM (Array Name) := do
let pattern := letPatDecl.getArg 0;
patternVars ← getPatternVars pattern;
pure $ patternVars.filterMap fun patternVar => match patternVar with
  | PatternVar.localVar x => some x
  | _ => none

def getLetEqnsDeclVar (letEqnsDecl : Syntax) : Name :=
(letEqnsDecl.getArg 0).getId

def getLetDeclVars (letDecl : Syntax) : TermElabM (Array Name) := do
let arg := letDecl.getArg 0;
if arg.getKind == `Lean.Parser.Term.letIdDecl then
  pure #[getLetIdDeclVar arg]
else if arg.getKind == `Lean.Parser.Term.letPatDecl then
  getLetPatDeclVars arg
else if arg.getKind == `Lean.Parser.Term.letEqnsDecl then
  pure #[getLetEqnsDeclVar arg]
else
  throwError "unexpected kind of let declaration"

def getDoLetVars (doLet : Syntax) : TermElabM (Array Name) :=
getLetDeclVars (doLet.getArg 1)

-- ident >> optType >> leftArrow >> termParser
def getDoIdDeclVar (doIdDecl : Syntax) : Name :=
(doIdDecl.getArg 0).getId

-- termParser >> leftArrow >> termParser >> optional (" | " >> termParser)
def getDoPatDeclVars (doPatDecl : Syntax) : TermElabM (Array Name) := do
let pattern := doPatDecl.getArg 0;
patternVars ← getPatternVars pattern;
pure $ patternVars.filterMap fun patternVar => match patternVar with
  | PatternVar.localVar x => some x
  | _ => none

-- parser! "let " >> (doIdDecl <|> doPatDecl)
def getDoLetArrowVars (doLetArrow : Syntax) : TermElabM (Array Name) := do
let decl := doLetArrow.getArg 1;
if decl.getKind == `Lean.Parser.Term.doIdDecl then
  pure #[getDoIdDeclVar decl]
else if decl.getKind == `Lean.Parser.Term.doPatDecl then
  getDoPatDeclVars decl
else
  throwError "unexpected kind of 'do' declaration"

def getDoReassignVars (doReassign : Syntax) : TermElabM (Array Name) := do
let arg := doReassign.getArg 0;
if arg.getKind == `Lean.Parser.Term.letIdDecl then
  pure #[getLetIdDeclVar arg]
else if arg.getKind == `Lean.Parser.Term.letPatDecl then
  getLetPatDeclVars arg
else
  throwError "unexpected kind of reassignment"

def toDoSeq (doElem : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.doSeqIndent #[mkNullNode #[doElem, mkNullNode]]

/-
  Recall that the `doIf` syntax is of the form
  ```
  "if " >> optIdent >> termParser >> " then " >> doSeq
  >> many (group (" else " >> " if ") >> optIdent >> termParser >> " then " >> doSeq)
  >> optional (" else " >> doSeq)
  ```

  Given a `doIf`, return an equivalente `doIf` that has no `else if`s and the `else` is not none.  -/
private def expandDoIf (doIf : Syntax) : Syntax :=
let ref       := doIf;
let doElseIfs := (doIf.getArg 5).getArgs;
let doElse    := doIf.getArg 6;
if doElseIfs.isEmpty && !doElse.isNone then
  doIf
else
  let doElse    :=
    if doElse.isNone then
      mkNullNode #[
        mkAtomFrom ref "else",
        toDoSeq (mkNode `Lean.Parser.Term.doReturn #[mkAtomFrom ref "return", mkNullNode])
      ]
    else
      doElse;
  let doElse := doElseIfs.foldr
    (fun doElseIf doElse =>
      let ifAtom := (doElseIf.getArg 0).getArg 1;
      let doIfArgs := (doElseIf.getArgs).set! 0 ifAtom;
      let doIfArgs := doIfArgs.push mkNullNode;
      let doIfArgs := doIfArgs.push doElse;
      mkNullNode #[mkAtomFrom doElseIf "else",
                   toDoSeq $ mkNode `Lean.Parser.Term.doIf doIfArgs])
    doElse;
  let doIf := doIf.setArg 6 doElse;
  doIf.setArg 5 mkNullNode -- remove else-ifs

structure DoIfView :=
(ref        : Syntax)
(optIdent   : Syntax)
(cond       : Syntax)
(thenBranch : Syntax)
(elseBranch : Syntax)

private def mkDoIfView (doIf : Syntax) : DoIfView :=
let doIf     := expandDoIf doIf;
{ ref        := doIf,
  optIdent   := doIf.getArg 1,
  cond       := doIf.getArg 2,
  thenBranch := doIf.getArg 4,
  elseBranch := (doIf.getArg 6).getArg 1 }

private def mkUnit (ref : Syntax) : MacroM Syntax := do
unit ← `(PUnit.unit);
pure $ unit.copyInfo ref

private def mkTuple (ref : Syntax) (elems : Array Syntax) : MacroM Syntax :=
if elems.size == 0 then do
  mkUnit ref
else if elems.size == 1 then
  pure (elems.get! 0)
else
  (elems.extract 0 (elems.size - 1)).foldrM
    (fun elem tuple => do
      tuple ← `(($elem, $tuple));
      pure $ tuple.copyInfo ref)
    (elems.back)

-- Code block to syntax term
namespace ToTerm

inductive Kind
| regular | forInNestedTerm | forIn | forInMap

structure Context :=
(m     : Syntax) -- Syntax to reference the monad associated with the do notation.
(uvars : Array Name)
(kind  : Kind)

abbrev M := ReaderT Context MacroM

def mkUVarTuple (ref : Syntax) : M Syntax := do
ctx ← read;
let uvarIdents := ctx.uvars.map fun x => mkIdentFrom ref x;
liftM $ mkTuple ref uvarIdents

/- Note that, in the current design, we can only reassign variables that were declared in the do-block.
   Thus, if `ctx.kind == Kind.regular`, then `ctx.uvars` must be empty.
   Therefore, the following method should never create a tuple.
   We keep it as-is because we may change the design decision in the future. -/
def mkResultUVarTuple (ref : Syntax) (x? : Option Name) : M Syntax := do
ctx ← read;
match x?, ctx.uvars.isEmpty with
| none,   true  => liftM $ mkUnit ref
| none,   false => do unit ← liftM $ mkUnit ref; uvars ← mkUVarTuple ref; liftM $ mkTuple ref #[unit, uvars]
| some x, true  => pure $ mkIdentFrom ref x
| some x, false => do uvars ← mkUVarTuple ref; liftM $ mkTuple ref #[mkIdentFrom ref x, uvars]

def returnToTermCore (ref : Syntax) (x? : Option Name) : M Syntax := do
ctx ← read;
match ctx.kind with
| Kind.forInNestedTerm => do u ← mkUVarTuple ref; `(HasPure.pure (DoResult.«return» $u))
| Kind.regular         => do r ← mkResultUVarTuple ref x?; `(HasPure.pure $r)
| _                    => do u ← mkUVarTuple ref; `(HasPure.pure (ForInStep.yield $u))

def returnToTerm (ref : Syntax) (x? : Option Name) : M Syntax := do
r ← returnToTermCore ref x?;
pure $ r.copyInfo ref

def continueToTermCore (ref : Syntax) : M Syntax := do
ctx ← read;
match ctx.kind with
| Kind.regular         => unreachable!
| Kind.forInNestedTerm => do u ← mkUVarTuple ref; `(HasPure.pure (DoResult.«continue» $u))
| _                    => do u ← mkUVarTuple ref; `(HasPure.pure (ForInStep.yield $u))

def continueToTerm (ref : Syntax) : M Syntax := do
r ← continueToTermCore ref;
pure $ r.copyInfo ref

def breakToTermCore (ref : Syntax) : M Syntax := do
ctx ← read;
match ctx.kind with
| Kind.regular         => unreachable!
| Kind.forInNestedTerm => do u ← mkUVarTuple ref; `(HasPure.pure (DoResult.«break» $u))
| _                    => do u ← mkUVarTuple ref; `(HasPure.pure (ForInStep.done $u))

def breakToTerm (ref : Syntax) : M Syntax := do
r ← breakToTermCore ref;
pure $ r.copyInfo ref

def actionToTermCore (action : Syntax) (k : Syntax) : MacroM Syntax := withFreshMacroScope do
if action.getKind == `Lean.Parser.Term.doDbgTrace then
  let msg := action.getArg 1;
  `(dbgTrace! $msg; $k)
else if action.getKind == `Lean.Parser.Term.doAssert then
  let cond := action.getArg 1;
  `(assert! $cond; $k)
else do
  `(HasBind.bind $action (fun _ => $k))

def actionToTerm (action : Syntax) (k : Syntax) : MacroM Syntax := do
r ← actionToTermCore action k;
pure $ r.copyInfo action

def declToTermCore (decl : Syntax) (k : Syntax) : M Syntax := withFreshMacroScope do
let kind := decl.getKind;
if kind == `Lean.Parser.Term.doLet then
  let letDecl := decl.getArg 1;
  `(let $letDecl:letDecl; $k)
else if kind == `Lean.Parser.Term.doLetRec then
  liftM $ Macro.throwError decl "WIP"
else if kind == `Lean.Parser.Term.doLetArrow then
  let arg := decl.getArg 1;
  let ref := arg;
  if arg.getKind == `Lean.Parser.Term.doIdDecl then
    let id    := arg.getArg 0;
    let type  := expandOptType ref (arg.getArg 1);
    let val   := arg.getArg 3;
    `(HasBind.bind $val (fun ($id:ident : $type) => $k))
  else if arg.getKind == `Lean.Parser.Term.doPatDecl then do
    -- termParser >> leftArrow >> termParser >> optional (" | " >> termParser)
    let pat      := arg.getArg 0;
    let discr    := arg.getArg 2;
    let optElse  := arg.getArg 3;
    if optElse.isNone then
      `(HasBind.bind $discr (fun x => match x with | $pat => $k))
    else do
      let elseBody := optElse.getArg 1;
      y ← `(y);
      ret ← returnToTerm ref y.getId;
      elseBody ← `(HasBind.bind $elseBody (fun y => $ret));
      `(HasBind.bind $discr (fun x => match x with | $pat => $k | _ => $elseBody))
  else
    liftM $ Macro.throwError decl "unexpected kind of 'do' declaration"
else if kind == `Lean.Parser.Term.doHave then
  liftM $ Macro.throwError decl ("WIP " ++ toString decl)
else
  liftM $ Macro.throwError decl "unexpected kind of 'do' declaration"

def declToTerm (decl : Syntax) (k : Syntax) : M Syntax := do
r ← declToTermCore decl k;
pure $ r.copyInfo decl

def reassignToTermCore (reassign : Syntax) (k : Syntax) : MacroM Syntax := withFreshMacroScope do
let kind := reassign.getKind;
if kind == `Lean.Parser.Term.doReassign then
  let letDecl := mkNode `Lean.Parser.Term.letDecl #[reassign.getArg 0];
  `(let $letDecl:letDecl; $k)
else if kind == `Lean.Parser.Term.doReassignArrow then
  Macro.throwError reassign ("WIP " ++ toString reassign)
else
  Macro.throwError reassign "unexpected kind of 'do' reassignment"

def reassignToTerm (reassign : Syntax) (k : Syntax) : MacroM Syntax := do
r ← reassignToTermCore reassign k;
pure $ r.copyInfo reassign

def mkIte (ref : Syntax) (optIdent : Syntax) (cond : Syntax) (thenBranch : Syntax) (elseBranch : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.«if» #[mkAtomFrom ref "if", optIdent, cond, mkAtomFrom ref "then", thenBranch, mkAtomFrom ref "else", elseBranch]

def mkJoinPointCore (j : Name) (ps : Array (Name × Bool)) (body : Syntax) (k : Syntax) : M Syntax := withFreshMacroScope do
let ref := body;
binders ← ps.mapM fun ⟨id, useTypeOf⟩ => do {
  type ← if useTypeOf then `(typeOf! $(mkIdentFrom ref id)) else `(_);
  let binderType := mkNullNode #[mkAtomFrom ref ":", type];
  pure $ mkNode `Lean.Parser.Term.explicitBinder #[mkAtomFrom ref "(", mkNullNode #[mkIdentFrom ref id], binderType, mkNullNode, mkAtomFrom ref ")"]
};
ctx ← read;
let m := ctx.m;
type ← `($m _);
`(let $(mkIdentFrom ref j):ident $binders:explicitBinder* : $type := $body; $k)

def mkJoinPoint (j : Name) (ps : Array (Name × Bool)) (body : Syntax) (k : Syntax) : M Syntax := do
r ← mkJoinPointCore j ps body k;
pure $ r.copyInfo body

def mkJmp (ref : Syntax) (j : Name) (args : Array Name) : Syntax :=
mkAppStx (mkIdentFrom ref j) (args.map $ mkIdentFrom ref)

partial def toTerm : Code → M Syntax
| Code.«return» ref x?    => returnToTerm ref x?
| Code.«continue» ref     => continueToTerm ref
| Code.«break» ref        => breakToTerm ref
| Code.joinpoint j ps b k => do b ← toTerm b; k ← toTerm k; mkJoinPoint j ps b k
| Code.jmp ref j args     => pure $ mkJmp ref j args
| Code.decl _ stx k       => do k ← toTerm k; declToTerm stx k
| Code.reassign _ stx k   => do k ← toTerm k; liftM $ reassignToTerm stx k
| Code.action stx k       => do k ← toTerm k; liftM $ actionToTerm stx k
| Code.ite ref _ o c t e  => do t ← toTerm t; e ← toTerm e; pure $ mkIte ref o c t e
| _ => liftM $ Macro.throwError Syntax.missing "WIP"

private def getKindUVars (c : CodeBlock) (forInVar? : Option Name) : Kind × Array Name :=
match forInVar? with
| none          =>
  if hasContinueBreak c.code then
    (Kind.forInNestedTerm, nameSetToArray c.uvars)
  else
    (Kind.regular, nameSetToArray c.uvars)
| some forInVar =>
  if c.uvars.contains forInVar then
    let uvars := #[forInVar] ++ nameSetToArray (c.uvars.erase forInVar);
    (Kind.forInMap, uvars)
  else
    (Kind.forIn, nameSetToArray c.uvars)

def run (c : CodeBlock) (m : Syntax) (forInVar? : Option Name := none) : MacroM (Array Name × Syntax) := do
let code := c.code;
let (kind, uvars) := getKindUVars c forInVar?;
term ← toTerm code { m := m, kind := kind, uvars := uvars };
pure (uvars, term)

end ToTerm

namespace ToCodeBlock

structure Context :=
(ref       : Syntax)
(m         : Syntax) -- Syntax representing the monad associated with the do notation.
(varSet    : NameSet := {})
(insideFor : Bool := false)

abbrev M := ReaderT Context TermElabM

@[inline] def withNewVars {α} (newVars : Array Name) (x : M α) : M α :=
adaptReader (fun (ctx : Context) => { ctx with varSet := insertVars ctx.varSet newVars }) x

def ensureInsideFor : M Unit := do
ctx ← read;
unless ctx.insideFor $
  throwError "invalid statement, can only be used inside 'for ... in ... do ...'"

def ensureEOS (doElems : List Syntax) : M Unit :=
unless doElems.isEmpty $
  throwError "must be last element in a 'do' sequence"

def isDoVar? (stx : Syntax) : M (Option Name) := do
if stx.isIdent then do
  ctx ← read;
  let x := stx.getId;
  if ctx.varSet.contains x then pure (some x) else pure none
else
  pure none

def checkReassignable (xs : Array Name) : M Unit := do
ctx ← read;
xs.forM fun x =>
  unless (ctx.varSet.contains x) do
    throwError ("'" ++ x.simpMacroScopes ++ "' cannot be reassigned, only variables declared in the do-block can be reassigned")

private partial def expandLiftMethodAux : Syntax → StateT (List Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.do then pure stx
  else if k == `Lean.Parser.Term.doSeqIndent then pure stx
  else if k == `Lean.Parser.Term.doSeqBracketed then pure stx
  else if k == `Lean.Parser.Term.quot then pure stx
  else if k == `Lean.Parser.Term.liftMethod then withFreshMacroScope $ do
    let term := args.get! 1;
    term ← expandLiftMethodAux term;
    auxDo ← `(do let a ← $term);
    let auxDoElems := getDoSeqElems (getDoSeq auxDo);
    modify fun s => s ++ auxDoElems;
    `(a)
  else do
    args ← args.mapM expandLiftMethodAux;
    pure $ Syntax.node k args
| stx => pure stx

def expandLiftMethod (doElem : Syntax) : MacroM (List Syntax × Syntax) :=
if !hasLiftMethod doElem then pure ([], doElem)
else do
  (doElem, doElemsNew) ← (expandLiftMethodAux doElem).run [];
  pure (doElemsNew, doElem)

instance auususus : HasToString SourceInfo :=
{ toString := fun info => toString info.pos }

partial def doSeqToCode : List Syntax → M CodeBlock
| [] => do ctx ← read; pure $ mkReturn ctx.ref
| doElem::doElems => withRef doElem do
  (liftedDoElems, doElem) ← liftM (liftMacroM $ expandLiftMethod doElem : TermElabM _);
  if !liftedDoElems.isEmpty then
    doSeqToCode (liftedDoElems ++ [doElem] ++ doElems)
  else do
    let ref := doElem;
    let concatWithRest (c : CodeBlock) : M CodeBlock :=
      match doElems with
      | [] => pure c
      | _  => do {
        k ← doSeqToCode doElems;
        liftM $ concat c k
      };
    let auxDoToCode (auxDo : Syntax) : M CodeBlock := do {
      let auxDoElems := getDoSeqElems (getDoSeq auxDo);
      let auxDoElems := auxDoElems.map fun auxDoElem => auxDoElem.copyInfo doElem;
      doSeqToCode auxDoElems
    };
    let k := doElem.getKind;
    if k == `Lean.Parser.Term.doLet then do
      vars ← liftM $ getDoLetVars doElem;
      mkVarDeclCore vars doElem <$> withNewVars vars (doSeqToCode doElems)
    else if k == `Lean.Parser.Term.doLetRec then do
      throwError "WIP"
    else if k == `Lean.Parser.Term.doLetArrow then do
      vars ← liftM $ getDoLetArrowVars doElem;
      mkVarDeclCore vars doElem <$> withNewVars vars (doSeqToCode doElems)
    else if k == `Lean.Parser.Term.doReassign then do
      vars ← liftM $ getDoReassignVars doElem;
      checkReassignable vars;
      k ← doSeqToCode doElems;
      liftM $ mkReassignCore vars doElem k
    else if k == `Lean.Parser.Term.doReassignArrow then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doHave then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doIf then do
      let view := mkDoIfView doElem;
      thenBranch ← doSeqToCode (getDoSeqElems view.thenBranch);
      elseBranch ← doSeqToCode (getDoSeqElems view.elseBranch);
      ite ← liftM $ mkIte view.ref view.optIdent view.cond thenBranch elseBranch;
      concatWithRest ite
    else if k == `Lean.Parser.Term.doUnless then do
      let cond  := doElem.getArg 1;
      let doSeq := doElem.getArg 3;
      body ← doSeqToCode (getDoSeqElems doSeq);
      concatWithRest (mkUnless ref cond body)
    else if k == `Lean.Parser.Term.doFor then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doMatch then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doTry then
      throwError "WIP"
    else if k == `Lean.Parser.Term.doBreak then do
      ensureInsideFor;
      ensureEOS doElems;
      pure $ mkBreak ref
    else if k == `Lean.Parser.Term.doContinue then do
      ensureInsideFor;
      ensureEOS doElems;
      pure $ mkContinue ref
    else if k == `Lean.Parser.Term.doReturn then do
      ensureEOS doElems;
      let argOpt := doElem.getArg 1;
      if argOpt.isNone then
        pure $ mkReturn ref
      else do
        let arg := argOpt.getArg 0;
        x? ← isDoVar? arg;
        match x? with
        | some x => pure $ mkReturn ref x
        | none => withFreshMacroScope do
          auxDo ← `(do let x := $arg; return x);
          auxDoToCode auxDo
    else if k == `Lean.Parser.Term.doDbgTrace then
      mkAction doElem <$> doSeqToCode doElems
    else if k == `Lean.Parser.Term.doAssert then
      mkAction doElem <$> doSeqToCode doElems
    else if k == `Lean.Parser.Term.doExpr then
      let term := doElem.getArg 0;
      if doElems.isEmpty then withFreshMacroScope do
        auxDo ← `(do let x ← $term; return x);
        auxDoToCode auxDo
      else
        mkAction term <$> doSeqToCode doElems
    else
      throwError ("unexpected do-element" ++ Format.line ++ toString doElem)

def run (doStx : Syntax) (m : Syntax) : TermElabM CodeBlock :=
(doSeqToCode $ getDoSeqElems $ getDoSeq doStx).run { ref := doStx, m := m }

end ToCodeBlock

/- Create a synthetic metavariable `?m` and assign `m` to it.
   We use `?m` to refer to `m` when expanding the `do` notation. -/
private def mkMonadAlias (m : Expr) : TermElabM Syntax := do
result ← `(?m);
mType ← inferType m;
mvar ← elabTerm result mType;
assignExprMVar mvar.mvarId! m;
pure result

-- @[builtinTermElab «do»]
def elabDo : TermElab :=
fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?;
  bindInfo ← extractBind expectedType?;
  m ← mkMonadAlias bindInfo.m;
  codeBlock ← ToCodeBlock.run stx m;
  (_, stxNew) ← liftMacroM $ ToTerm.run codeBlock m;
  trace! `Elab.do stxNew;
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?

end Do

----- OLD IMPLEMENTATION -----

private def getDoElems (stx : Syntax) : Array Syntax :=
let arg := stx.getArg 1;
let args := if arg.getKind == `Lean.Parser.Term.doSeqBracketed then
  (arg.getArg 1).getArgs
else
  (arg.getArg 0).getArgs;
if args.back.isToken ";" || args.back.isNone || (args.back.getArg 0).isToken ";" then -- temporary hack
  args.pop
else
  args

private partial def expandLiftMethodAux : Syntax → StateT (Array Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.do then pure stx
  else if k == `Lean.Parser.Term.quot then pure stx
  else if k == `Lean.Parser.Term.liftMethod then withFreshMacroScope $ do
    let term := args.get! 1;
    term ← expandLiftMethodAux term;
    auxDo ← `(do { let a ← $term; $(Syntax.missing) });
    let auxDoElems := (getDoElems auxDo).pop;
    modify $ fun s => s ++ auxDoElems;
    `(a)
  else do
    args ← args.mapM expandLiftMethodAux;
    pure $ Syntax.node k args
| stx => pure stx

private def expandLiftMethod (stx : Syntax) : MacroM (Option (Array Syntax)) :=
if hasLiftMethod stx then do
  (stx, doElems) ← (expandLiftMethodAux stx).run #[];
  let doElems := doElems.push stx;
  pure doElems
else
  pure none

/- Expand `doLet`, `doPatDecl`, nonterminal `doExpr`s, and `liftMethod` -/
private partial def expandDoElems : Bool → Array Syntax → Nat → MacroM Syntax
| modified, doElems, i =>
  let mkRest : Unit → MacroM Syntax := fun _ => do {
    let restElems := doElems.extract (i+2) doElems.size;
    if restElems.size == 1 then
      pure $ (restElems.get! 0).getArg 0
    else
      `(do { $restElems* })
  };
  let addPrefix (rest : Syntax) : MacroM Syntax := do {
    if i == 0 then
      pure rest
    else
      let newElems := doElems.extract 0 i;
      let newElems := newElems.push $ Syntax.node `Lean.Parser.Term.doExpr #[rest];
      `(do { $newElems* })
  };
  if h : i < doElems.size then do
    let doElem := doElems.get ⟨i, h⟩;
    doElemsNew? ← expandLiftMethod doElem;
    match doElemsNew? with
    | some doElemsNew => do
      let post    := doElems.extract (i+1) doElems.size;
      let pre     := doElems.extract 0 i;
      let doElems := pre ++ doElemsNew ++ post;
      tmp ← `(do { $doElems* });
      expandDoElems true doElems i
    | none =>
      if doElem.getKind == `Lean.Parser.Term.doLet then do
        let letDecl := doElem.getArg 1;
        rest ← mkRest ();
        newBody ← `(let $letDecl:letDecl; $rest);
        addPrefix newBody
      -- cleanup the following code
      else if doElem.getKind == `Lean.Parser.Term.doLetArrow && (doElem.getArg 1).getKind == `Lean.Parser.Term.doPatDecl then withFreshMacroScope $ do
        let doElem  := doElem.getArg 1;
        -- (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
        let pat      := doElem.getArg 0;
        let discr    := doElem.getArg 2;
        let optElse  := doElem.getArg 3;
        rest ← mkRest ();
        newBody ←
          if optElse.isNone then do
            `(do { let x ← $discr; (match x with | $pat => $rest) })
          else
            let elseBody := optElse.getArg 1;
            `(do { let x ← $discr; (match x with | $pat => $rest | _ => $elseBody) });
        addPrefix newBody
      else if i < doElems.size - 1 && doElem.getKind == `Lean.Parser.Term.doExpr then do
        -- def doExpr := parser! termParser
        let term := doElem.getArg 0;
        auxDo ← `(do { let x ← $term; $(Syntax.missing) });
        let doElemNew := (getDoElems auxDo).get! 0;
        let doElems := doElems.set! i doElemNew;
        expandDoElems true doElems (i+2)
      else
        expandDoElems modified doElems (i+2)
  else if modified then
    `(do { $doElems* })
  else
    Macro.throwUnsupported

structure ProcessedDoElem :=
(action : Expr)
(var    : Expr)

instance ProcessedDoElem.inhabited : Inhabited ProcessedDoElem := ⟨⟨arbitrary _, arbitrary _⟩⟩

private def extractTypeFormerAppArg (type : Expr) : TermElabM Expr := do
type ← withReducible $ whnf type;
match type with
| Expr.app _ a _ => pure a
| _              => throwError ("type former application expected" ++ indentExpr type)

/-
HasBind.bind : ∀ {m : Type u_1 → Type u_2} [self : HasBind m] {α β : Type u_1}, m α → (α → m β) → m β
-/
private def mkBind (m bindInstVal : Expr) (elems : Array ProcessedDoElem) (body : Expr) : TermElabM Expr :=
if elems.isEmpty then
  pure body
else do
  let x := elems.back.var; -- any variable would work since they must be in the same universe
  xType ← inferType x;
  u_1 ← getDecLevel xType;
  bodyType ← inferType body;
  u_2 ← getDecLevel bodyType;
  let bindAndInst := mkApp2 (Lean.mkConst `HasBind.bind [u_1, u_2]) m bindInstVal;
  elems.foldrM
    (fun elem body => do
      -- dbgTrace (">>> " ++ toString body);
      let var    := elem.var;
      let action := elem.action;
      α  ← inferType var;
      mβ ← inferType body;
      β  ← extractTypeFormerAppArg mβ;
      f  ← mkLambdaFVars #[var] body;
      -- dbgTrace (">>> f: " ++ toString f);
      let body := mkAppN bindAndInst #[α, β, action, f];
      pure body)
    body

private partial def processDoElemsAux (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : Nat → Array ProcessedDoElem → TermElabM Expr
| i, elems =>
  let doElem := doElems.get! i;
  let k      := doElem.getKind;
  withRef doElem $
  if k == `Lean.Parser.Term.doLetArrow then do
    when (i == doElems.size - 1) $
      throwError "the last statement in a 'do' block must be an expression";
    let doElem := doElem.getArg 1;
    -- try (ident >> optType >> leftArrow) >> termParser
    let id        := doElem.getIdAt 0;
    let typeStx   := expandOptType doElem (doElem.getArg 1);
    let actionStx := doElem.getArg 3;
    type ← elabType typeStx;
    let actionExpectedType := mkApp m type;
    action ← elabTermEnsuringType actionStx actionExpectedType;
    withLocalDecl id BinderInfo.default type $ fun x =>
      processDoElemsAux (i+1) (elems.push { action := action, var := x })
  else if doElem.getKind == `Lean.Parser.Term.doExpr then do
    when (i != doElems.size - 1) $
      throwError ("unexpected 'do' expression element" ++ Format.line ++ doElem);
    let bodyStx := doElem.getArg 0;
    body ← elabTermEnsuringType bodyStx expectedType;
    mkBind m bindInstVal elems body
  else
    throwError ("unexpected 'do' expression element" ++ Format.line ++ doElem)

private def processDoElems (doElems : Array Syntax) (m bindInstVal : Expr) (expectedType : Expr) : TermElabM Expr :=
processDoElemsAux doElems m bindInstVal expectedType 0 #[]

def expandDo? (stx : Syntax) : MacroM (Option Syntax) :=
let doElems := getDoElems stx;
catch
  (do stx ← expandDoElems false doElems 0; pure $ some stx)
  (fun _ => pure none)

@[builtinTermElab «do»]
def elabDo : TermElab :=
fun stx expectedType? => do
  stxNew? ← liftMacroM $ expandDo? stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none => do
    tryPostponeIfNoneOrMVar expectedType?;
    let doElems := getDoElems stx;
    trace `Elab.do $ fun _ => stx;
    let doElems := doElems.getSepElems;
    trace `Elab.do $ fun _ => "doElems: " ++ toString doElems;
    { m := m, hasBindInst := bindInstVal, .. } ← extractBind expectedType?;
    processDoElems doElems m bindInstVal expectedType?.get!

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.do;
pure ()

end Term
end Elab
end Lean

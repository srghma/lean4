import Lean
import Std.Data.HashSet
import Std.Data.HashMap

open Lean Meta

-- Retrieve the pretty-printed tactic string stored in an autoParam tactic declaration.
unsafe def formatAutoParamTacticStr (env : Environment) (tacticDecl : Name) : MetaM String := do
  match env.evalConstCheck Syntax {} ``Syntax tacticDecl with
  | .ok stx =>
    let fmt ← PrettyPrinter.ppCategory `tacticSeq stx
    return fmt.pretty
  | .error _ => return tacticDecl.toString

-- Format a Prop expression using infix notation (e.g. `a < b` instead of
-- `instLTNat.lt a b`).  Falls back to `ppExpr` for unknown shapes.
partial def formatPropExprStr (e : Expr) : MetaM String := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Helper: format the last two arguments with an infix operator symbol.
  let infix2 (sym : String) : MetaM String := do
    if args.size >= 2 then
      let a ← ppExpr args[args.size - 2]!
      let b ← ppExpr args[args.size - 1]!
      return s!"{a} {sym} {b}"
    else
      return (← ppExpr e).pretty
  match fn with
  | .const `LT.lt _   => infix2 "<"
  | .const `LE.le _   => infix2 "≤"
  | .const `GT.gt _   => infix2 ">"
  | .const `GE.ge _   => infix2 "≥"
  | .const `Eq _      => infix2 "="
  | .const `Ne _      => infix2 "≠"
  | .const `Dvd.dvd _ => infix2 "∣"
  | .const `Not _ =>
    if args.size >= 1 then
      let inner ← formatPropExprStr args[0]!
      return s!"¬{inner}"
    else
      return (← ppExpr e).pretty
  | _ => return (← ppExpr e).pretty

structure ScriptConfig where
  outDir   : String := "."
  noWrite  : Bool   := false
  print    : Bool   := false
  pkg      : String := "Init"
  showHelp : Bool   := false

def parseArgs (args : List String) : ScriptConfig :=
  let rec loop (args : List String) (cfg : ScriptConfig) : ScriptConfig :=
    match args with
    | [] => cfg
    | "-h" :: rest | "--help" :: rest =>
      loop rest { cfg with showHelp := true }
    | "-p" :: rest | "--print" :: rest =>
      loop rest { cfg with print := true }
    | "--no-write" :: rest =>
      loop rest { cfg with noWrite := true }
    | "--out-dir" :: dir :: rest =>
      loop rest { cfg with outDir := dir }
    | arg :: rest =>
      if arg.startsWith "-" then
        loop rest cfg
      else
        loop rest { cfg with pkg := arg }
  loop args {}

def isImpureType (type : Expr) : MetaM Bool := do
  forallTelescope type fun _ body => do
    let fn := body.consumeMData.getAppFn
    if let .const name _ := fn then
      let s := name.toString
      return s == "IO" || s == "BaseIO" || s == "EIO" || s == "ST" || s == "EST" || s == "Void"
        || s.endsWith ".IO" || s.endsWith ".BaseIO" || s.endsWith ".EIO" || s.endsWith ".ST" || s.endsWith ".EST" || s.endsWith ".Void"
    return false

def hasProofParam (type : Expr) : MetaM Bool := do
  forallTelescope type fun xs _ => do
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      try
        if (← isProp ldecl.type) then
          return true
      catch _ => pure ()
    return false

def getDeclKind (cinfo : ConstantInfo) : String :=
  match cinfo with
  | .axiomInfo ..  => "axiom"
  | .defnInfo ..   => "def"
  | .thmInfo ..    => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo ..   => "quot"
  | .inductInfo .. => "inductive"
  | .ctorInfo ..   => "constructor"
  | .recInfo ..    => "recursor"

/-- Sanitize a parameter name: replace internal hygiene names (containing `._@.`) with `h`. -/
def sanitizeParamName (name : Name) : String :=
  let s := name.toString
  if name.isAnonymous || s.contains "._@." || s.contains "@" then "h" else s

-- Format a domain expression that is known to be a Prop.  Strips `autoParam`
-- and returns (typeString, optionalDefault) where optionalDefault is like
-- " := by get_elem_tactic" or "".
unsafe def formatPropDomain (env : Environment) (d : Expr) : MetaM (String × String) := do
  let d := d.consumeMData
  match d with
  | .app (.app (.const ``autoParam _) innerType) (.const tacticDecl _) =>
    let innerStr ← formatPropExprStr innerType
    let tacStr   ← formatAutoParamTacticStr env tacticDecl
    return (innerStr, s!" := by {tacStr}")
  | _ =>
    let s ← formatPropExprStr d
    return (s, "")

unsafe def formatTypeWithBorrow (env : Environment) (type : Expr) : MetaM String := do
  go type #[]
where
  formatDomain (d : Expr) : MetaM (Bool × String × String) := do
    let isBorrowed := isMarkedBorrowed d
    let inner := d.consumeMData
    -- Check if this domain is a Prop; if so, use the pretty Prop formatter.
    let isPropDom ← try isProp inner catch _ => pure false
    if isPropDom then
      let (typeStr, defStr) ← formatPropDomain env inner
      return (isBorrowed, typeStr, defStr)
    else
      let innerFmt ← ppExpr inner
      return (isBorrowed, innerFmt.pretty, "")

  go (e : Expr) (binders : Array String) : MetaM String := do
    match e with
    | .forallE name domain body bi =>
      let (isBorrowed, domStr, domDefault) ← formatDomain domain
      let borrowPrefix := if isBorrowed then "@& " else ""
      let isDep := body.hasLooseBVars

      -- For non-dependent default-binder Prop args: still use named form so we
      -- can show the `:= by ...` default.  For non-Prop non-dep args keep the
      -- arrow style.
      let isPropDom ← try isProp domain.consumeMData catch _ => pure false
      if !isDep && bi == .default && !isPropDom then
        let isArrow := domain.consumeMData.isForall
        let domStrFinal := if isArrow then s!"({domStr})" else domStr
        let argStr := if isBorrowed then s!"({borrowPrefix}{domStrFinal})" else domStrFinal
        let rest ← go body #[]
        let prefixStr := if binders.isEmpty then "" else String.join (binders.toList.map (· ++ " → "))
        return s!"{prefixStr}{argStr} → {rest}"
      else
        withLocalDecl name bi domain fun fvar =>
          let instantiatedBody := body.instantiate1 fvar
          let binderStr := match bi with
            | .implicit => "{" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "}"
            | .strictImplicit => "⦃" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "⦄"
            | .instImplicit =>
              if name.hasMacroScopes then
                "[" ++ s!"{borrowPrefix}{domStr}" ++ "]"
              else
                "[" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "]"
            | .default =>
              let displayName := sanitizeParamName name
              "(" ++ s!"{displayName} : {borrowPrefix}{domStr}{domDefault}" ++ ")"
          go instantiatedBody (binders.push binderStr)
    | other =>
      let bodyFmt ← ppExpr other
      let prefixStr := if binders.isEmpty then "" else String.join (binders.toList.map (· ++ " → "))
      return s!"{prefixStr}{bodyFmt.pretty}"

partial def collectTypes (e : Expr) (acc : IO.Ref (Std.HashSet String)) : MetaM Unit := do
  let e := e.consumeMData
  match e with
  | .forallE _ d b _ =>
    collectTypes d acc
    withLocalDecl `_ .default d fun fvar => do
      collectTypes (b.instantiate1 fvar) acc
  | .app f a =>
    checkIfType e acc
    collectTypes f acc
    collectTypes a acc
  | other => checkIfType other acc
where
  checkIfType (e : Expr) (acc : IO.Ref (Std.HashSet String)) : MetaM Unit := do
    let e := e.consumeMData
    if e.isSort || e.isFVar || e.isBVar then return
    try
      let ty ← inferType e
      let tyWhnf ← whnf ty
      if tyWhnf.isSort then
        let isP ← isProp e
        if !isP then
          let fmt ← ppExpr e
          let s := fmt.pretty
          if !s.contains "autoParam" && !s.contains "optParam" && !s.contains "inst" && !s.contains "✝" then
            acc.modify (·.insert s)
            if s == "Unit" then
              acc.modify (·.insert "PUnit")
    catch _ => pure ()

structure DeclEntry where
  externIdent : String
  declName    : Name
  kind        : String
  typeExpr    : Expr
  typeStr     : String
  isImpure    : Bool
  deriving Inhabited

structure ModuleGroup where
  moduleName : String
  decls      : Array DeclEntry

partial def sanitizeTableCell (s : String) : String :=
  let singleLine := s.replace "\r" " " |>.replace "\n" " "
  let escaped := singleLine.replace "|" "\\|"
  let rec collapse (str : String) : String :=
    let next := str.replace "  " " "
    if next.length == str.length then str else collapse next
  collapse escaped

structure TableRow where
  c0 : String
  c1 : String
  c2 : String
  c3 : String

def padRight (s : String) (w : Nat) : String :=
  if s.length >= w then s
  else s ++ "".pushn ' ' (w - s.length)

def makeSeparator (w : Nat) : String :=
  "".pushn '-' (max w 3)

def formatAlignedTable (headers : TableRow) (rows : Array TableRow) : List String := Id.run do
  let allRows := #[headers] ++ rows
  let w0 := allRows.foldl (fun m r => max m r.c0.length) 0
  let w1 := allRows.foldl (fun m r => max m r.c1.length) 0
  let w2 := allRows.foldl (fun m r => max m r.c2.length) 0
  let w3 := allRows.foldl (fun m r => max m r.c3.length) 0

  let sepRow : TableRow := {
    c0 := makeSeparator w0
    c1 := makeSeparator w1
    c2 := makeSeparator w2
    c3 := makeSeparator w3
  }

  let formatRow (r : TableRow) : String :=
    s!"| {padRight r.c0 w0} | {padRight r.c1 w1} | {padRight r.c2 w2} | {padRight r.c3 w3} |"

  let mut lines := []
  lines := lines.concat (formatRow headers)
  lines := lines.concat (formatRow sepRow)
  for r in rows do
    lines := lines.concat (formatRow r)
  lines

def generateFileContent (groups : Array ModuleGroup) (forImpure : Bool) : MetaM String := do
  let typesRef ← IO.mkRef ({} : Std.HashSet String)
  let mut lines : List String := []

  -- 1. Collect types from relevant declarations
  for g in groups do
    for d in g.decls do
      if d.isImpure == forImpure then
        forallTelescope d.typeExpr fun xs body => do
          for x in xs do
            let ldecl ← x.fvarId!.getDecl
            collectTypes ldecl.type typesRef
          collectTypes body typesRef

  let allTypes ← typesRef.get
  let sortedTypes := allTypes.toArray.qsort (fun a b => a < b)

  -- 2. Add header with unique types
  lines := lines.concat "/-"
  for t in sortedTypes do
    lines := lines.concat t
  lines := lines.concat "-/"
  lines := lines.concat ""

  let headers : TableRow := {
    c0 := "name of extern",
    c1 := "def",
    c2 := "full name of func",
    c3 := "type of func"
  }

  -- 3. Add tables grouped by module / filename
  for g in groups do
    let declsInGroup := g.decls.filter (fun d => d.isImpure == forImpure)
    if declsInGroup.isEmpty then continue

    let fileName := g.moduleName.replace "." "/" ++ ".lean"
    lines := lines.concat s!"# {fileName}"
    lines := lines.concat ""

    -- Group by externIdent in order of first appearance
    let mut grouped : Array (String × Array DeclEntry) := #[]
    let mut externIndex : Std.HashMap String Nat := {}

    for d in declsInGroup do
      match externIndex.get? d.externIdent with
      | some idx =>
        let (name, list) := grouped[idx]!
        grouped := grouped.set! idx (name, list.push d)
      | none =>
        externIndex := externIndex.insert d.externIdent grouped.size
        grouped := grouped.push (d.externIdent, #[d])

    let mut tableRows : Array TableRow := #[]
    for (_, (decls : Array DeclEntry)) in grouped do
      for i in [:decls.size] do
        let d : DeclEntry := decls[i]!
        let escapedType := sanitizeTableCell d.typeStr
        if i == 0 then
          tableRows := tableRows.push {
            c0 := d.externIdent
            c1 := d.kind
            c2 := d.declName.toString
            c3 := escapedType
          }
        else
          let prev : DeclEntry := decls[i - 1]!
          let prevEscapedType := sanitizeTableCell prev.typeStr
          tableRows := tableRows.push {
            c0 := ""
            c1 := if d.kind == prev.kind then "" else d.kind
            c2 := if d.declName == prev.declName then "" else d.declName.toString
            c3 := if escapedType == prevEscapedType then "" else escapedType
          }

    let tableLines := formatAlignedTable headers tableRows
    for l in tableLines do
      lines := lines.concat l

    lines := lines.concat ""

  return String.intercalate "\n" lines ++ "\n"

-- ============================================================
-- Lean inductive file generator
-- ============================================================

/-- Look up if an Expr is a tracked type-variable FVar; return its MyTy name. -/
def lookupTyVar (tvars : Array (FVarId × String)) (e : Expr) : Option String :=
  if let .fvar fid := e.consumeMData then
    tvars.findSome? fun (id, n) => if id == fid then some n else none
  else none

/-- Map a Lean return type expression to a MyTy expression string. -/
partial def mapReturnExpr (tvars : Array (FVarId × String)) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  -- Tracked type variable?
  if let some n := lookupTyVar tvars e then return n
  -- Unit → X: lazy value
  if let .forallE _ dom body _ := e then
    if let .const `Unit _ := dom.consumeMData then
      let inner ← mapReturnExpr tvars body
      return s!"(lazy {inner})"
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const `Nat _        => return "nat"
  | .const `Bool _       => return "LeanPrimTy.bool"
  | .const `UInt8 _      => return "uint8"
  | .const `UInt16 _     => return "uint16"
  | .const `UInt32 _     => return "uint32"
  | .const `UInt64 _     => return "uint64"
  | .const `Int _        => return "int"
  | .const `Int8 _       => return "int8"
  | .const `Int16 _      => return "int16"
  | .const `Int32 _      => return "int32"
  | .const `Int64 _      => return "int64"
  | .const `String _     => return "string"
  | .const `Char _       => return "char"
  | .const `Float _      => return "float"
  | .const `Float32 _    => return "float32"
  | .const `Float.Model _   => return "floatModel"
  | .const `Float32.Model _ => return "float32Model"
  | .const `ByteArray _  => return "byteArray"
  | .const `FloatArray _ => return "floatArray"
  | .const `USize _      => return "LeanPrimTy.usize"
  | .const `ISize _      => return "LeanPrimTy.isize"
  | .const `Lean.Name _  => return "name"
  | .const `Ordering _   => return "ordering"
  | .const `String.Pos.Raw _ => return "stringPosRaw"
  | .const `Substring.Raw _  => return "substringRaw"
  | .const `String.Slice _   => return "stringSlice"
  | .const `ShareCommon.Object _ => return "shareCommonObject"
  | .const `Unit _       => return "()"
  | .const `PUnit _      => return "()"
  | .const `Decidable _  => return "LeanPrimTy.bool"
  | .const `Subtype _ =>
    if args.size >= 1 then
      return ← mapReturnExpr tvars args[0]!
    return "nat"
  | .const `Prod _ =>
    if args.size >= 2 then
      let t1 ← mapReturnExpr tvars args[args.size - 2]!
      let t2 ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(prod {t1} {t2})"
    return "(prod ? ?)"
  | .const `ShareCommon.State _ =>
    if args.size >= 1 then
      let sFmt ← ppExpr args[0]!
      return s!"(shareCommonState {sFmt.pretty})"
    return "shareCommonState"
  | .const `String.Pos _ =>
    if args.size >= 1 then
      let sFmt ← ppExpr args[0]!
      return s!"(LeanPrimTy.stringPos {sFmt.pretty})"
    return "stringPosRaw"
  | .const `Task _ =>
    if args.size >= 1 then
      let elem ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(task {elem})"
    return "(task ?)"
  | .const `Thunk _ =>
    if args.size >= 1 then
      let elem ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(thunk {elem})"
    return "(thunk ?)"
  | .const `Array _ =>
    if args.size >= 1 then
      let elem ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(array {elem})"
    return "(array ?)"
  | .const `List _ =>
    if args.size >= 1 then
      let elem ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(list {elem})"
    return "(list ?)"
  | .const `Option _ =>
    if args.size >= 1 then
      let elem ← mapReturnExpr tvars args[args.size - 1]!
      return s!"(option {elem})"
    return "(option ?)"
  | .const `BitVec _ =>
    if args.size >= 1 then
      let n := args[args.size - 1]!
      let nFmt ← ppExpr n
      let nStr := if nFmt.pretty.contains "numBits" then "64" else nFmt.pretty
      return s!"(bitvec {nStr})"
    return "(bitvec ?)"
  | .const n _ =>
    let s := n.toString
    if s == "IO" || s == "BaseIO" || s == "EIO" || s == "ST" ||
       s.endsWith ".IO" || s.endsWith ".BaseIO" || s.endsWith ".ST" then
      if args.size >= 1 then
        return ← mapReturnExpr tvars args[args.size - 1]!
    let fmt ← ppExpr e
    return s!"({fmt.pretty})"
  | _ =>
    let fmt ← ppExpr e
    return s!"({fmt.pretty})"

/-- Map a value argument type expression to a constructor arg type string.
    Type-variable FVars become `denote <varName>`. -/
partial def mapArgTypeStr (tvars : Array (FVarId × String)) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some n := lookupTyVar tvars e then return s!"denote {n}"
  if let .forallE _ dom body _ := e then
    if dom.consumeMData.isConstOf `Unit then
      let inner ← mapReturnExpr tvars body
      return s!"denote (lazy {inner})"
    else
      let dStr ← mapArgTypeStr tvars dom
      let bStr ← mapArgTypeStr tvars body
      return s!"{dStr} → {bStr}"
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const `BitVec _ =>
    if args.size >= 1 then
      let n := args[args.size - 1]!
      let nFmt ← ppExpr n
      let nStr := if nFmt.pretty.contains "numBits" then "64" else nFmt.pretty
      return s!"BitVec {nStr}"
    return "BitVec ?"
  | .const `Task _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"Task {elemStr}"
    return "Task ?"
  | .const `Thunk _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"Thunk {elemStr}"
    return "Thunk ?"
  | .const `IO.Promise _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"IO.Promise {elemStr}"
    return "IO.Promise ?"
  | .const `Float.Model _ => return "Float.Model"
  | .const `Float32.Model _ => return "Float32.Model"
  | .const `Substring.Raw _ => return "Substring.Raw"
  | .const `String.Pos.Raw _ => return "String.Pos.Raw"
  | .const `Array _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"Array {elemStr}"
    return "Array ?"
  | .const `List _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"List {elemStr}"
    return "List ?"
  | .const `Option _ =>
    if args.size >= 1 then
      let elem ← mapArgTypeStr tvars args[args.size - 1]!
      let elemStr := if elem.contains ' ' then s!"({elem})" else elem
      return s!"Option {elemStr}"
    return "Option ?"
  | _ =>
    let fmt ← ppExpr e
    return fmt.pretty

/-- Format a type variable name from the original source binder name. -/
def makeTypeVarName (nm : Name) (tvc : Nat) : String :=
  let s := (nm.toString.takeWhile (fun c => c != '.' && c != '_')).toString
  if s.isEmpty || s.startsWith "✝" || s.startsWith "@" then
    if tvc == 0 then "t" else s!"t{tvc + 1}"
  else
    s!"{s}t"

/-- Check whether any subsequent parameter domain in `e` contains `fvarId`. -/
partial def subsequentDomainMentionsFVar (e : Expr) (fvarId : FVarId) : MetaM Bool := do
  let e := e.consumeMData
  match e with
  | .forallE _ dom body _ =>
    if dom.containsFVar fvarId then
      return true
    withLocalDecl `_ .default dom fun fvar =>
      subsequentDomainMentionsFVar (body.instantiate1 fvar) fvarId
  | _ => pure false

/-- Build a constructor identifier from the extern name.
    When multiple Lean decls share one extern, suffix with `__DeclName_dots_to_underscores`. -/
def makeCtorName (externIdent : String) (declName : Name) (isSingle : Bool) : String :=
  if isSingle then externIdent
  else
    let raw := declName.toString.replace "." "_"
    let suffix := if raw.startsWith "_private_" then raw.drop 9 else raw
    s!"{externIdent}__{suffix}"

/-- Generate constructor params and return MyTy type for one DeclEntry.
    State (tvars, tvarCount, params) is threaded through the recursion. -/
unsafe def generateCtorSignature (env : Environment) (d : DeclEntry)
    : MetaM (Array String × String) :=
  go d.typeExpr #[] 0 #[]
where
  go (e : Expr) (tvars : Array (FVarId × String)) (tvc : Nat) (params : Array String)
      : MetaM (Array String × String) := do
    let e := e.consumeMData
    match e with
    | .forallE nm dom body bi =>
      let domClean := dom.consumeMData
      match bi with
      | .implicit =>
        if domClean.isSort && !domClean.isProp then
          -- Type variable {α : Type u}
          let tvName := makeTypeVarName nm tvc
          withLocalDecl nm .implicit domClean fun fvar =>
            go (body.instantiate1 fvar)
               (tvars.push (fvar.fvarId!, tvName))
               (tvc + 1)
               (params.push s!"({tvName} : MyTy)")
        else
          withLocalDecl nm .implicit domClean fun fvar => do
            let isNeeded ← subsequentDomainMentionsFVar (body.instantiate1 fvar) fvar.fvarId!
            let inReturn := (body.instantiate1 fvar).containsFVar fvar.fvarId!
            if isNeeded || inReturn then
              let argTypeStr ← mapArgTypeStr tvars domClean
              let cleanNm := sanitizeParamName nm
              go (body.instantiate1 fvar) tvars tvc (params.push ("{" ++ cleanNm ++ " : " ++ argTypeStr ++ "}"))
            else
              go (body.instantiate1 fvar) tvars tvc params
      | .strictImplicit =>
        withLocalDecl nm .strictImplicit domClean fun fvar =>
          go (body.instantiate1 fvar) tvars tvc params
      | .instImplicit =>
        let fn := domClean.getAppFn.consumeMData
        let fnArgs := domClean.getAppArgs
        withLocalDecl nm .instImplicit domClean fun fvar => do
          let body' := body.instantiate1 fvar
          let newParams ← match fn with
            | .const `Inhabited _ =>
              if d.declName == `panicCore then
                pure params
              else if fnArgs.size >= 1 then
                let tvMatch := lookupTyVar tvars fnArgs[fnArgs.size - 1]! |>.getD "t"
                pure (params.push s!"(inhabited_default : denote {tvMatch})")
              else pure params
            | _ => pure params  -- drop [Nonempty] and other instances
          go body' tvars tvc newParams
      | .default =>
        if domClean.isSort && !domClean.isProp then
          let tvName := makeTypeVarName nm tvc
          withLocalDecl nm .default domClean fun fvar =>
            go (body.instantiate1 fvar)
               (tvars.push (fvar.fvarId!, tvName))
               (tvc + 1)
               (params.push s!"({tvName} : MyTy)")
        else
          let isPropDom ← try isProp domClean catch _ => pure false
          if isPropDom then
            let (typeStr, defStr) ← formatPropDomain env domClean
            let cleanNm := sanitizeParamName nm
            withLocalDecl nm .default domClean fun fvar => do
              let isNeeded ← subsequentDomainMentionsFVar (body.instantiate1 fvar) fvar.fvarId!
              let newParam :=
                if !defStr.isEmpty || cleanNm == "h" then
                  s!"(h : {typeStr}{defStr})"
                else if isNeeded then
                  s!"({cleanNm} : {typeStr})"
                else
                  typeStr
              go (body.instantiate1 fvar) tvars tvc (params.push newParam)
          else if domClean.isAppOf `optParam then
            let optArgs := domClean.getAppArgs
            let tyExpr := if optArgs.size >= 1 then optArgs[0]! else domClean
            let defExpr := if optArgs.size >= 2 then optArgs[1]! else Expr.bvar 0
            let argTypeStr ← mapArgTypeStr tvars tyExpr
            let cleanNm := sanitizeParamName nm
            let defStr ←
              if defExpr.isConstOf `Bool.false then pure "false"
              else if defExpr.isConstOf `Bool.true then pure "true"
              else do let p ← ppExpr defExpr; pure p.pretty
            withLocalDecl nm .default domClean fun fvar =>
              go (body.instantiate1 fvar) tvars tvc
                 (params.push s!"({cleanNm} : {argTypeStr} := {defStr})")
          else if params.all (·.endsWith ": MyTy)") && domClean.isConstOf `Unit then
            -- Unit → X: whole thing is lazy
            let retStr ← mapReturnExpr tvars body
            return (params, s!"(lazy {retStr})")
          else
            let argStr ← mapArgTypeStr tvars domClean
            let cleanNm := sanitizeParamName nm
            withLocalDecl nm .default domClean fun fvar => do
              let isNeeded ← subsequentDomainMentionsFVar (body.instantiate1 fvar) fvar.fvarId!
              let newParam :=
                if isNeeded then
                  s!"({cleanNm} : {argStr})"
                else
                  if domClean.isForall then s!"({argStr})" else argStr
              go (body.instantiate1 fvar) tvars tvc (params.push newParam)
    | other =>
      let retStr ← mapReturnExpr tvars other
      return (params, retStr)

/-- Fixed preamble for the generated lean extern inductive file. -/
def leanFilePreamble (inductiveName : String) : String :=
  "module\nprelude\n" ++
  "public import LeanScript.LeanPrimTy\n" ++
  "public import LeanScript.LeanPrimTyCovariant\n" ++
  "public import Init.Data.FloatArray.Basic\n" ++
  "public import Init.System.IO\n" ++
  "public import Init.System.Promise\n" ++
  "public import Init.ShareCommon\n" ++
  "set_option autoImplicit false\n" ++
  "@[expose] public section\n" ++
  "namespace LeanScript\n\n" ++
  "open LeanPrimTy\n" ++
  "open LeanPrimTyCovariant\n\n" ++
  "protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64\n" ++
  "protected abbrev LeanPrimTy.isize : LeanPrimTy := int64\n\n" ++
  "variable {MyTy : Type}\n" ++
  "  (denote : MyTy → Type)\n" ++
  "  [Coe LeanPrimTy MyTy]\n" ++
  "  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]\n" ++
  "  [Coe (LeanPrimTyCovariant MyTy) MyTy]\n" ++
  "  (option : MyTy → MyTy)\n" ++
  "  (list : MyTy → MyTy)\n" ++
  "  (fn1 : MyTy → MyTy → MyTy)\n" ++
  "  (fn2 : MyTy → MyTy → MyTy → MyTy)\n" ++
  "  (prod : MyTy → MyTy → MyTy)\n" ++
  "  (name : MyTy)\n" ++
  "  (ordering : MyTy)\n" ++
  "  (byteArray : MyTy)\n" ++
  "  (floatArray : MyTy)\n\n" ++
  s!"inductive {inductiveName} : MyTy → Type where"

/-- Generate full `.lean` file with an inductive of extern constructors. -/
unsafe def generateLeanContent (env : Environment) (groups : Array ModuleGroup)
    (forImpure : Bool) (pkg : String) : MetaM String := do
  let inductiveName := s!"Lean{pkg}{if forImpure then "Impure" else "Pure"}Extern"
  let mut lines : List String := [leanFilePreamble inductiveName]

  -- Count total occurrences of each externIdent globally across all groups for this purity
  let mut globalExternCounts : Std.HashMap String Nat := {}
  for g in groups do
    for d in g.decls do
      if d.isImpure == forImpure then
        let count := globalExternCounts.getD d.externIdent 0
        globalExternCounts := globalExternCounts.insert d.externIdent (count + 1)

  for g in groups do
    let declsInGroup := g.decls.filter (fun d => d.isImpure == forImpure)
    if declsInGroup.isEmpty then continue

    let fileName := g.moduleName.replace "." "/" ++ ".lean"
    let commentLine := s!"-- {fileName}"
    let sep := "  " ++ "".pushn '-' commentLine.length
    lines := lines.concat sep
    lines := lines.concat s!"  {commentLine}"
    lines := lines.concat sep

    -- Group by externIdent (preserving order of first appearance)
    let mut grouped : Array (String × Array DeclEntry) := #[]
    let mut externIndex : Std.HashMap String Nat := {}
    for d in declsInGroup do
      match externIndex.get? d.externIdent with
      | some idx =>
        let (n, list) := grouped[idx]!
        grouped := grouped.set! idx (n, list.push d)
      | none =>
        externIndex := externIndex.insert d.externIdent grouped.size
        grouped := grouped.push (d.externIdent, #[d])

    for (externIdent, decls) in grouped do
      let isGloballySingle := globalExternCounts.getD externIdent 0 == 1
      for i in [:decls.size] do
        let d := decls[i]!
        let ctorName := makeCtorName externIdent d.declName isGloballySingle
        let origName := d.declName.toString
        let (paramArr, retTy) ← try
          generateCtorSignature env d
        catch ex =>
          let msg ← ex.toMessageData.toString
          pure (#[], s!"(-- ERROR: {msg})")
        let paramStr := if paramArr.isEmpty then ""
                        else String.join (paramArr.toList.map (· ++ " → "))
        lines := lines.concat
          s!"  | {ctorName} : {paramStr}{inductiveName} {retTy} -- {origName}"

  lines := lines.concat ""
  lines := lines.concat "end LeanScript"
  lines := lines.concat ""
  lines := lines.concat "end"
  lines := lines.concat ""
  return String.intercalate "\n" lines ++ "\n"

def showHelpMessage : IO Unit := do
  IO.println "Usage: lean --run srghmascripts/generate_init_funcs.lean [options] [pkg]

Scans Lean packages for @[extern] definitions and attributes, classifies them into
pure and impure functions, collects all unique types used, and generates
InitFuncsPure.md and InitFuncsImpure.md.

Arguments:
  pkg                     Package to process: Init (default), Std, or Lean

Options:
  -p, --print             Print generated content to stdout
  --no-write              Do not write generated files to disk
  --out-dir <path>        Custom output directory (default: .)
  -h, --help              Show this help message
"

unsafe def main (args : List String) : IO Unit := do
  let cfg := parseArgs args
  if cfg.showHelp then
    showHelpMessage
    return

  initSearchPath (← findSysroot)
  let pkgName := cfg.pkg.toName
  let env ← importModules #[{ module := pkgName }] {}
  let coreCtx : Core.Context := { fileName := "<stdin>", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }

  let ((), _) ← (MetaM.run' do
    let mut groups : Array ModuleGroup := #[]

    for i in [:env.header.moduleNames.size] do
      let modName := env.header.moduleNames[i]!
      if !modName.getRoot.toString.startsWith cfg.pkg then
        continue

      let modData := env.header.moduleData[i]!
      let mut decls : Array DeclEntry := #[]

      for cinfo in modData.constants do
        if let some extName := getExternNameFor env `all cinfo.name then
          let impure ← isImpureType cinfo.type
          let tyFmt ← formatTypeWithBorrow env cinfo.type
          let mut kind := getDeclKind cinfo
          if (← hasProofParam cinfo.type) then
            kind := s!"{kind} 🌌"
          decls := decls.push {
            externIdent := extName
            declName    := cinfo.name
            kind        := kind
            typeExpr    := cinfo.type
            typeStr     := tyFmt
            isImpure    := impure
          }

      if !decls.isEmpty then
        groups := groups.push {
          moduleName := modName.toString
          decls      := decls
        }

    let pureContent ← generateFileContent groups false
    let impureContent ← generateFileContent groups true

    if cfg.print then
      IO.println "=== PURE ==="
      IO.println pureContent
      IO.println "=== IMPURE ==="
      IO.println impureContent

    if !cfg.noWrite then
      let outDirStr : String := cfg.outDir
      let pkgStr : String := cfg.pkg
      let pureOutPath : String := outDirStr ++ "/" ++ pkgStr ++ "FuncsPure.md"
      let impureOutPath : String := outDirStr ++ "/" ++ pkgStr ++ "FuncsImpure.md"
      IO.FS.writeFile pureOutPath pureContent
      IO.FS.writeFile impureOutPath impureContent
      IO.eprintln s!"Wrote {pureOutPath}"
      IO.eprintln s!"Wrote {impureOutPath}"

      let pureLeanPath  := "/home/srghma/projects/leanscript/LeanScript/Lean" ++ pkgStr ++ "PureExterns.lean"
      let impureLeanPath := "/home/srghma/projects/leanscript/LeanScript/Lean" ++ pkgStr ++ "ImpureExterns.lean"
      let pureLeanContent  ← generateLeanContent env groups false pkgStr
      let impureLeanContent ← generateLeanContent env groups true  pkgStr
      IO.FS.writeFile pureLeanPath  pureLeanContent
      IO.FS.writeFile impureLeanPath impureLeanContent
      IO.eprintln s!"Wrote {pureLeanPath}"
      IO.eprintln s!"Wrote {impureLeanPath}"
  ).toIO coreCtx coreState

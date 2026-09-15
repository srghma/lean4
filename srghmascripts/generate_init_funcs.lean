import Lean
import Std.Data.HashSet
import Std.Data.HashMap

open Lean Meta

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
      return s == "IO" || s == "BaseIO" || s == "EIO" || s == "ST" || s == "EST"
        || s.endsWith ".IO" || s.endsWith ".BaseIO" || s.endsWith ".EIO" || s.endsWith ".ST" || s.endsWith ".EST"
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

partial def formatTypeWithBorrow (type : Expr) : MetaM String := do
  go type #[]
where
  formatDomain (d : Expr) : MetaM (Bool × String) := do
    let isBorrowed := isMarkedBorrowed d
    let inner := d.consumeMData
    let innerFmt ← ppExpr inner
    return (isBorrowed, innerFmt.pretty)

  go (e : Expr) (binders : Array String) : MetaM String := do
    match e with
    | .forallE name domain body bi =>
      let (isBorrowed, domStr) ← formatDomain domain
      let borrowPrefix := if isBorrowed then "@& " else ""
      let isDep := body.hasLooseBVars
      
      if !isDep && bi == .default then
        let isArrow := domain.consumeMData.isForall
        let domStrFinal := if isArrow then s!"({domStr})" else domStr
        let argStr := if isBorrowed then s!"({borrowPrefix}{domStrFinal})" else domStrFinal
        let rest ← go body #[]
        let prefixStr := if binders.isEmpty then "" else String.join (binders.toList.map (· ++ " → "))
        return s!"{prefixStr}{argStr} → {rest}"
      else
        withLocalDecl name bi domain fun fvar => do
          let instantiatedBody := body.instantiate1 fvar
          let binderStr := match bi with
            | .implicit => "{" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "}"
            | .strictImplicit => "⦃" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "⦄"
            | .instImplicit =>
              if name.hasMacroScopes then
                "[" ++ s!"{borrowPrefix}{domStr}" ++ "]"
              else
                "[" ++ s!"{name} : {borrowPrefix}{domStr}" ++ "]"
            | .default => "(" ++ s!"{name} : {borrowPrefix}{domStr}" ++ ")"
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

def main (args : List String) : IO Unit := do
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
          let tyFmt ← formatTypeWithBorrow cinfo.type
          let kind := getDeclKind cinfo
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
  ).toIO coreCtx coreState

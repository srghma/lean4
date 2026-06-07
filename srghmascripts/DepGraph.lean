import Std.Data.HashMap
import Std.Data.HashSet
import Init.System.FilePath

/-!
  DepGraph.lean — generate order_of_review.md + interactive Force-Directed DAG HTML pages
-/

open System (FilePath)

def String.containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else (haystack.splitOn needle).length > 1

-- Pure, fast path normalizer to replace slow external `realpath` processes
def normalizePath (p : FilePath) : FilePath := Id.run do
  let isAbsolute := p.toString.startsWith "/"
  let components := p.toString.splitOn "/"
  let mut norm : Array String := #[]
  for c in components do
    if c == "" || c == "." then continue
    else if c == ".." then
      norm := norm.pop
    else
      norm := norm.push c
  let res := String.intercalate "/" norm.toList
  if isAbsolute then ⟨"/" ++ res⟩ else ⟨res⟩

def realpathSafe (p : FilePath) : IO FilePath :=
  pure (normalizePath p)

-- ─── Known external dependency groups ────────────────────────────────────────

def knownExternals : Array (String × Array String) := #[
  ("cadical",          #["cadical"]),
  ("mimalloc",         #["mimalloc"]),
  ("libuv",            #["libuv.h", "uv.h"]),
  ("ICU (<icu.h>)",    #["icu.h", "unicode/"]),
  ("emscripten",       #["emscripten.h", "emscripten/"]),
  ("<windows.h>",      #["windows.h", "psapi.h", "ntdef.h", "bcrypt.h",
                          "tchar.h", "strsafe.h"]),
  ("<pthread.h>",      #["pthread.h"]),
  ("<unistd.h>",       #["unistd.h"]),
  ("<dlfcn.h>",        #["dlfcn.h"]),
  ("<dirent.h>",       #["dirent.h"]),
  ("<link.h>",         #["link.h"]),
  ("<execinfo.h>",     #["execinfo.h"]),
  ("<sys/mman.h>",     #["sys/mman.h"]),
  ("<sys/stat.h>",     #["sys/stat.h", "sys/types.h", "sys/wait.h",
                          "sys/syscall.h", "sys/resource.h", "sys/time.h",
                          "sys/random.h", "sys/file.h"]),
  ("<mach-o/dyld.h>",  #["mach-o/dyld.h", "mach-o/getsect.h", "mach/mach.h"]),
  ("<sanitizer>",      #["sanitizer/lsan_interface.h"]),
  ("<jemalloc>",       #["jemalloc/jemalloc.h"]),
  ("LLVM",             #["llvm-c/Core.h", "llvm.h", "llvm-c/"]),
  ("libc",             #["use libc", "libc::"]),
  ("libuv-sys2",       #["use libuv_sys2", "libuv_sys2::"]),
]

def stdHeaders : Std.HashSet String :=
  Std.HashSet.ofList [
    "string", "vector", "map", "set", "memory", "algorithm", "iostream",
    "sstream", "cstdlib", "cstdio", "cstdint", "cstring", "new", "utility",
    "functional", "thread", "mutex", "condition_variable", "atomic", "chrono",
    "cassert", "cmath", "climits", "csignal", "cerrno", "cwchar", "cwctype",
    "locale", "bitset", "initializer_list", "typeinfo", "numeric", "iterator",
    "type_traits", "tuple", "array", "deque", "forward_list", "list", "queue",
    "stack", "unordered_map", "unordered_set", "ios", "system_error", "iomanip",
    "fstream",
  ]

-- ─── FilePair & TaskTree ──────────────────────────────────────────────────────

abbrev Stem := FilePath

structure FilePair where
  stem : Stem
  name : FilePath
  h    : Option FilePath
  cpp  : Option FilePath
  deriving Repr, Inhabited

def collapsedLabel (pair : FilePair) : String :=
  let base := pair.stem.fileName.getD ""
  match pair.h, pair.cpp with
  | some h, some cpp =>
    let hExt := h.extension.getD "h"
    let cppExt := cpp.extension.getD "cpp"
    base ++ ".{" ++ cppExt ++ "," ++ hExt ++ "}"
  | some h, none => base ++ "." ++ h.extension.getD "h"
  | none, some cpp => base ++ "." ++ cpp.extension.getD "cpp"
  | none, none => base

inductive TaskTree where
  | node : FilePair → Array TaskTree → TaskTree
  deriving Repr, Inhabited

-- ─── File system helpers ──────────────────────────────────────────────────────

def isFile (p : FilePath) : IO Bool :=
  (p.metadata).map (·.type == .file) |>.catchExceptions (fun _ => pure false)

def isDir (p : FilePath) : IO Bool :=
  (p.metadata).map (·.type == .dir) |>.catchExceptions (fun _ => pure false)

partial def walkDir (dir : FilePath) (exts : Array String) : IO (Array FilePath) := do
  unless ← isDir dir do return #[]
  let entries ← System.FilePath.readDir dir
  let names := entries.map (·.fileName) |>.qsort (· < ·)
  let mut result : Array FilePath := #[]
  for name in names do
    if name.startsWith "." then continue
    if name == "target" || name == "build" || name == "node_modules" then continue
    let full := dir / name
    if ← isDir full then
      result := result ++ (← walkDir full exts)
    else if exts.any (fun e => full.extension == some e) then
      result := result.push full
  return result

def stemOf (p : FilePath) : Stem :=
  match p.extension with
  | none     => p
  | some ext => ⟨(p.toString.dropEnd (ext.length + 1)).toString⟩

def nodeId (root : FilePath) (p : FilePath) : String :=
  let b := root.toString
  let t := p.toString
  let rel := if t.startsWith (b ++ "/") then (t.drop (b.length + 1)).toString else t
  rel.map fun c => if c.isAlphanum || c == '_' then c else '_'

def relPath (base : FilePath) (target : FilePath) : FilePath :=
  let b := base.toString ++ "/"
  let t := target.toString
  if t.startsWith b then ⟨(t.drop b.length).toString⟩ else target

-- ─── Review status ────────────────────────────────────────────────────────────

def isReviewed (srcPath : FilePath) : IO Bool := do
  let ext := srcPath.extension.getD ""
  let mdPath : FilePath := ⟨(srcPath.toString.dropEnd (ext.length + 1)).toString ++ "md"⟩
  unless ← isFile mdPath do return false
  let text ← IO.FS.readFile mdPath
  if text.containsSubstr "- [ ]" then return false
  if text.toUpper.containsSubstr "TODO" then return false
  return true

-- ─── Include parsing ──────────────────────────────────────────────────────────

def parseInclude (line : String) : Option String :=
  let s := line.trimAsciiStart.toString
  if !s.startsWith "#include" then none
  else
    let rest := (s.drop 8).trimAsciiStart.toString
    let (_, close') := if rest.startsWith "\"" then ('\"', '\"') else ('<', '>')
    let inner := (rest.drop 1).toString
    (inner.splitOn (toString close')).head?

def matchExternal (target : String) : Option String :=
  knownExternals.findSome? fun ⟨lbl, pats⟩ =>
    if pats.any (fun pat => target.containsSubstr pat) then some lbl else none

-- ─── Kahn's topological sort ──────────────────────────────────────────────────

def kahnSort (allStems : Array Stem)
    (stemDepsOn : Std.HashMap Stem (Std.HashSet Stem)) : Array Stem := Id.run do
  let mut inDegree : Std.HashMap Stem Nat := {}
  let mut revGraph : Std.HashMap Stem (Array Stem) := {}
  for s in allStems do
    inDegree := inDegree.insert s 0
    revGraph := revGraph.insert s #[]

  for (stem, deps) in stemDepsOn.toList do
    for dep in deps.toList do
      if revGraph.contains dep then
        revGraph  := revGraph.insert dep ((revGraph.getD dep #[]).push stem)
        inDegree  := inDegree.insert stem ((inDegree.getD stem 0) + 1)

  let mut queue : Array Stem :=
    allStems.filter (fun s => inDegree.getD s 0 == 0)
    |>.qsort (·.toString < ·.toString)
  let mut sorted : Array Stem := #[]

  while queue.size > 0 do
    queue := queue.qsort (·.toString < ·.toString)
    let cur := queue[0]!
    queue   := queue.extract 1 queue.size
    sorted  := sorted.push cur
    for nb in revGraph.getD cur #[] do
      let d := (inDegree.getD nb 0) - 1
      inDegree := inDegree.insert nb d
      if d == 0 then queue := queue.push nb

  let sortedSet : Std.HashSet Stem := sorted.foldl (·.insert ·) {}
  let remaining := allStems.filter (fun s => !sortedSet.contains s)
    |>.qsort (·.toString < ·.toString)
  return sorted ++ remaining

-- ─── Rose tree construction ───────────────────────────────────────────────────

def makePair (cppRoot : FilePath) (stem : Stem) : IO FilePair := do
  let dir  := stem.parent.getD cppRoot
  let base := stem.fileName.getD ""
  return {
    stem
    name := relPath cppRoot stem
    h    := ← do
      if ← isFile (dir / (base ++ ".h"))   then return some (relPath cppRoot (dir / (base ++ ".h")))
      if ← isFile (dir / (base ++ ".hpp")) then return some (relPath cppRoot (dir / (base ++ ".hpp")))
      return none
    cpp  := ← do
      if ← isFile (dir / (base ++ ".cpp")) then return some (relPath cppRoot (dir / (base ++ ".cpp")))
      if ← isFile (dir / (base ++ ".c"))   then return some (relPath cppRoot (dir / (base ++ ".c")))
      return none
  }

def buildRoseTree (cppRoot : FilePath) (sortedStems : Array Stem)
    (stemDepsOn : Std.HashMap Stem (Std.HashSet Stem)) : IO (Array TaskTree) := do
  let mut stemToIdx : Std.HashMap Stem Nat := {}
  for i in [:sortedStems.size] do
    stemToIdx := stemToIdx.insert sortedStems[i]! i

  let pairs ← sortedStems.mapM (makePair cppRoot)

  let n := sortedStems.size
  let mut childrenOf : Array (Array Nat) := Array.replicate n #[]
  let mut parentOf   : Array (Option Nat) := Array.replicate n none

  for i in [:n] do
    let stem := sortedStems[i]!
    let eligible := (stemDepsOn.getD stem {}).toList.filterMap fun dep =>
      stemToIdx.get? dep |>.bind fun j => if j < i then some j else none
    match eligible with
    | [] => pure ()
    | _  =>
      let bestJ := eligible.foldl (init := eligible.head!) fun best j =>
        if j > best then j else best
      parentOf   := parentOf.set! i (some bestJ)
      childrenOf := childrenOf.set! bestJ (childrenOf[bestJ]!.push i)

  -- We build all nodes upfront, then assemble the tree
  let mut nodes : Array TaskTree := Array.replicate n (.node default #[])
  -- Build leaves first (no children), then parents bottom-up
  -- Since children always have higher indices than parents (j < i constraint above),
  -- iterating in reverse order guarantees children are built before parents.
  for i in [:n] do
    let ri := n - 1 - i  -- reverse index
    let childTrees := childrenOf[ri]!.map fun ci => nodes[ci]!
    nodes := nodes.set! ri (.node pairs[ri]! childTrees)

  let roots := (Array.range n).filter (fun i => parentOf[i]! == none)
  return roots.map fun i => nodes[i]!

-- ─── Rose tree → Markdown ────────────────────────────────────────────────────

def renderTree (cppRoot : FilePath) (roots : Array TaskTree) : IO (Array String) := do
  let mut lines : Array String := #[]
  let rec visit (t : TaskTree) (depth : Nat) (acc : Array String) : IO (Array String) := do
    let .node pair children := t
    let files : Array FilePath := (pair.h.toList ++ pair.cpp.toList).toArray
    let fileStr := (files.map fun f => s!"`{f}`").toList |> ", ".intercalate
    let fileStr := fileStr.replace ", " " and "
    let allDone ← files.allM fun f => isReviewed (cppRoot / f)
    let checkbox := if allDone then "[x]" else "[ ]"
    let indent   := String.ofList (List.replicate (depth * 2) ' ')
    let mut acc := acc.push s!"{indent}- {checkbox} {pair.name} ({fileStr})"
    for child in children do
      acc ← visit child (depth + 1) acc
    return acc
  for root in roots do
    lines ← visit root 0 lines
  return lines

-- ─── MD validation ───────────────────────────────────────────────────────────

def validateMd (lines : Array String) : Except String Unit := do
  let mut prevIndent := 0
  for i in [:lines.size] do
    let line    := lines[i]!
    let trimmed := line.trimAsciiStart.toString
    unless trimmed.startsWith "- " do
      prevIndent := 0; continue
    let indent := line.length - trimmed.length
    if indent % 2 != 0 then
      throw s!"MD007: line {i+1} indent={indent} not a multiple of 2\n  {line}"
    if indent > prevIndent + 2 then
      throw s!"MD007 no-skip: line {i+1} jumped {prevIndent}→{indent}\n  {line}"
    prevIndent := indent

-- ─── Markdown file writer ────────────────────────────────────────────────────

def buildOrderMd (root : FilePath) (sortedStems : Array Stem)
    (stemDepsOn : Std.HashMap Stem (Std.HashSet Stem)) : IO Unit := do
  let roots  ← buildRoseTree root sortedStems stemDepsOn
  let body   ← renderTree root roots

  let count := body.filter (·.trimAsciiStart.toString.startsWith "- ") |>.size
  if count != sortedStems.size then
    throw <| .userError s!"Rose tree completeness failure: {count} items rendered, expected {sortedStems.size}.\nCycle in rose tree — check buildRoseTree."

  let header : Array String := #[
    "# C++ to Rust Porting Review Order", "",
    "Files are topologically sorted by dependency order (leaves first).",
    "Siblings at the same indentation level are independent and can be reviewed in any order.",
    "",
  ]
  let allLines := header ++ body

  match validateMd allLines with
  | .error msg => throw <| .userError msg
  | .ok ()     => pure ()

  let mdPath := root / "srghmascripts" / "order_of_review.md"
  IO.FS.writeFile mdPath (String.intercalate "\n" allLines.toList ++ "\n")
  IO.println s!"✅  Written {mdPath}"

-- ─── DOT state monad ─────────────────────────────────────────────────────────

structure DotSt where
  lines       : Array String              := #[]
  addedNodes  : Std.HashSet String        := {}
  addedEdges  : Std.HashSet String        := {}
  externalIds : Std.HashMap String String := {}
  -- JS data collection for force-graph simulation
  jsNodes     : Array String              := #[]
  jsLinks     : Array String              := #[]
  deriving Repr, Inhabited

abbrev DotM := StateT DotSt IO

def emitLine (s : String) : DotM Unit :=
  modify fun st => { st with lines := st.lines.push s }

def dotAddNode (id label : String) (attrs : Array (String × String)) : DotM Unit := do
  let st ← get
  if st.addedNodes.contains id then return
  modify fun s => { s with addedNodes := s.addedNodes.insert id }
  let allAttrs := #[("label", label)] ++ attrs
  let attrList := allAttrs.map (fun (k, v) => s!"{k}=\"{v}\"") |>.toList
    |> ", ".intercalate
  emitLine s!"  {id} [{attrList}];"

  -- Determine Node category details for the JS Force Simulation Graph
  let type :=
    if id.startsWith "ext_" then "external"
    else if id.startsWith "missing_" then "missing"
    else if id.startsWith "cpp_" || id.contains "src_kernel" || id.contains "src_library" || id.contains "src_util" || id.contains "src_runtime" || id.contains "src_shell" || id.contains "src_initialize" then "cpp"
    else "rust"

  let group :=
    if id.startsWith "ext_" then "external"
    else if id.startsWith "missing_" then "missing"
    else
      let parts := id.splitOn "_"
      if parts.length > 2 then parts[1]! else "main"

  let escapedLabel := label.replace "\\" "\\\\" |>.replace "\"" "\\\""
  let jsNode := "{" ++
    " id: \"" ++ id ++ "\"," ++
    " label: \"" ++ escapedLabel ++ "\"," ++
    " type: \"" ++ type ++ "\"," ++
    " group: \"" ++ group ++ "\"" ++
    " }"
  modify fun s => { s with jsNodes := s.jsNodes.push jsNode }

def dotAddEdge (from' to' : String) (attrs : Array (String × String)) : DotM Unit := do
  let key := s!"{from'}->{to'}"
  let st ← get
  if st.addedEdges.contains key then return
  modify fun s => { s with addedEdges := s.addedEdges.insert key }
  let attrStr := (attrs.map (fun (k,v) => s!"{k}=\"{v}\"")).toList |> ", ".intercalate
  let line := if attrStr.isEmpty then s!"  {from'} -> {to'};"
    else s!"  {from'} -> {to'} [{attrStr}];"
  emitLine line

  -- Output edge link representation for JS Force Simulation Graph
  let style := attrs.findSome? (fun (k,v) => if k == "style" then some v else none) |>.getD "solid"
  let color := attrs.findSome? (fun (k,v) => if k == "color" then some v else none) |>.getD ""
  let jsLink := "{" ++
    " source: \"" ++ from' ++ "\"," ++
    " target: \"" ++ to' ++ "\"," ++
    " style: \"" ++ style ++ "\"," ++
    " color: \"" ++ color ++ "\"" ++
    " }"
  modify fun s => { s with jsLinks := s.jsLinks.push jsLink }

def ensureExt (label : String) : DotM String := do
  let st ← get
  if let some id := st.externalIds.get? label then return id
  let id := "ext_" ++ label.map fun c => if c.isAlphanum || c == '_' then c else '_'
  modify fun s => { s with externalIds := s.externalIds.insert label id }
  dotAddNode id label #[
    ("shape", "diamond"), ("style", "filled"),
    ("fillcolor", "#ffcccc"), ("fontcolor", "#880000"),
  ]
  return id

-- ─── Rust subgraph ───────────────────────────────────────────────────────────

def findSubstrIdx? (haystack needle : String) : Option Nat :=
  if needle.isEmpty then some 0
  else
    let parts := haystack.splitOn needle
    if parts.length <= 1 then none
    else some parts[0]!.length

def tomlStr (src key : String) : Option String := do
  let idx ← findSubstrIdx? src key
  let after := (src.drop (idx + key.length)).trimAsciiStart.toString
  guard (after.startsWith "=")
  let after := (after.drop 1).trimAsciiStart.toString
  guard (after.startsWith "\"")
  let inner := (after.drop 1).toString
  (inner.splitOn "\"").head?

def cargoMembers (src : String) : Array String :=
  let go : Option String := do
    let idx ← findSubstrIdx? src "members"
    let after := (src.drop (idx + 7)).trimAsciiStart.toString
    guard (after.startsWith "=")
    let after := (after.drop 1).trimAsciiStart.toString
    guard (after.startsWith "[")
    let inner := (after.drop 1).toString
    (inner.splitOn "]").head?
  match go with
  | none => #[]
  | some content =>
    content.splitOn ","
      |>.toArray
      |>.map (fun s => s.trimAscii.toString.replace "\"" "" |>.trimAscii.toString)
      |>.filter (· != "")

def buildRustGraph (root rustRoot : FilePath) (collapsed : Bool) : DotM Unit := do
  let wsPath := rustRoot / "Cargo.toml"
  unless ← isFile wsPath do return
  let wsToml  ← IO.FS.readFile wsPath
  let members := cargoMembers wsToml

  emitLine "  subgraph cluster_rust {"
  emitLine "    label=\"Rust workspace (src/rust)\";"
  emitLine "    style=filled; fillcolor=\"#e8f4e8\"; color=\"#228822\";"

  for member in members do
    let mDir   := rustRoot / member
    let mCargo := mDir / "Cargo.toml"
    unless ← isFile mCargo do continue
    let cargo ← IO.FS.readFile mCargo

    let pkgName :=
      match findSubstrIdx? cargo "[package]" with
      | none => member
      | some pi =>
        let after := (cargo.drop (pi + 9)).toString
        tomlStr after "name" |>.getD member

    let rsFiles ← walkDir (mDir / "src") #["rs"]

    let clusterId := nodeId root mDir
    emitLine s!"    subgraph cluster_{clusterId} {"{"}"
    emitLine s!"      label=\"{pkgName}\"; style=filled; fillcolor=\"#d0ecd0\";"
    for rs in rsFiles do
      let id := nodeId root rs
      dotAddNode id (rs.fileName.getD rs.toString) #[
        ("shape", "box"), ("style", "filled"), ("fillcolor", "#f0fff0"), ("fontsize", "10"),
      ]
      emitLine s!"      {id};"
    emitLine "    }"

    for rs in rsFiles do
      let id  := nodeId root rs
      let src ← IO.FS.readFile rs
      for (extLabel, pats) in knownExternals do
        if pats.any (fun pat => src.containsSubstr pat) then
          let extId ← ensureExt extLabel
          dotAddEdge id extId #[("style", "dashed"), ("color", "#cc4400")]
      for line in src.splitOn "\n" do
        let t := line.trimAsciiStart.toString
        if (t.startsWith "// Port" || t.startsWith "// port") then
          match findSubstrIdx? t " of " with
          | none => pure ()
          | some oi =>
            let cppRel := (t.drop (oi + 4)).trimAsciiEnd.toString.replace "src/" ""
            let cppStem := stemOf ⟨cppRel⟩
            let cppId := if collapsed then
              "cpp_" ++ cppStem.toString.map (fun c => if c.isAlphanum || c == '_' then c else '_')
            else
              "cpp_" ++ cppRel.map (fun c => if c.isAlphanum || c == '_' then c else '_')

            let pair ← makePair (root / "src") cppStem
            let label := if collapsed then collapsedLabel pair else cppRel

            dotAddNode cppId label #[
              ("shape", "note"), ("style", "filled"), ("fillcolor", "#fff0cc"),
              ("fontsize", "9"), ("fontcolor", "#664400"),
            ]
            dotAddEdge id cppId #[
              ("style", "dotted"), ("color", "#888800"),
              ("label", "port of"), ("fontsize", "8"),
            ]

  emitLine "  }"

-- ─── C++ dependency graph helpers ─────────────────────────────────────────────

structure CppDeps where
  allStems      : Array Stem
  stemDepsOn    : Std.HashMap Stem (Std.HashSet Stem)
  dotEdges      : Array (String × String × String)
  dotMissing    : Array (String × String × String)
  externalEdges : Array (String × String)
  deriving Repr, Inhabited

def buildCppDeps (root cppRoot cppIncludeRoot : FilePath)
    (cppFiles : Array FilePath) (collapsed : Bool) : IO CppDeps := do
  let mut resolvedToStem : Std.HashMap String Stem := {}
  for f in cppFiles do
    let s := stemOf f
    resolvedToStem := resolvedToStem.insert f.toString s
    resolvedToStem := resolvedToStem.insert s.toString s
    let rp ← realpathSafe f
    resolvedToStem := resolvedToStem.insert rp.toString s

  let allStemsArr := cppFiles.map stemOf
  let allStemsSet : Std.HashSet Stem :=
    allStemsArr.foldl (·.insert ·) {}

  let mut stemDepsOn : Std.HashMap Stem (Std.HashSet Stem) := {}
  for s in allStemsArr do
    stemDepsOn := stemDepsOn.insert s {}

  let mut dotEdges      : Array (String × String × String) := #[]
  let mut dotMissing    : Array (String × String × String) := #[]
  let mut externalEdges : Array (String × String) := #[]
  let mut addedEdgesSet : Std.HashSet (String × String) := {}

  for f in cppFiles do
    let fromStem := stemOf f
    let fId      := if collapsed then nodeId root fromStem else nodeId root f
    let src      ← IO.FS.readFile f
    let baseDir  := f.parent.getD cppRoot

    for line in src.splitOn "\n" do
      let some target := parseInclude line | continue

      if let some extLabel := matchExternal target then
        let edgeKey := (fId, extLabel)
        unless addedEdgesSet.contains edgeKey do
          externalEdges := externalEdges.push (fId, extLabel)
          addedEdgesSet := addedEdgesSet.insert edgeKey
        continue

      let candidates := #[baseDir / target, cppRoot / target, cppIncludeRoot / target]
      let mut resolved : Option FilePath := none
      for c in candidates do
        if ← isFile c then resolved := some c; break

      if let some res := resolved then
        let rp ← realpathSafe res
        let toStem : Option Stem :=
          resolvedToStem.get? res.toString
          |>.orElse (fun _ => resolvedToStem.get? rp.toString)
          |>.orElse (fun _ =>
            let s := stemOf res
            if allStemsSet.contains s then some s else none)

        match toStem with
        | some ts =>
          let toId := if collapsed then nodeId root ts else nodeId root res
          if !collapsed || ts != fromStem then
            let edgeKey := (fId, toId)
            unless addedEdgesSet.contains edgeKey do
              dotEdges := dotEdges.push (fId, toId, "#882288")
              addedEdgesSet := addedEdgesSet.insert edgeKey
          if ts != fromStem then
            let cur := stemDepsOn.getD fromStem {}
            stemDepsOn := stemDepsOn.insert fromStem (cur.insert ts)
        | none =>
          IO.eprintln s!"  ⚠ include outside CPP_ROOT: {res} (from {relPath cppRoot f})"
      else
        let isAngle := target.startsWith "<"
        let bare    := !target.contains '/'
        if !isAngle && !(bare && stdHeaders.contains target) then
          let misId := "missing_" ++
            target.map fun c => if c.isAlphanum || c == '_' then c else '_'
          let edgeKey := (fId, misId)
          unless addedEdgesSet.contains edgeKey do
            dotMissing := dotMissing.push (fId, misId, target)
            addedEdgesSet := addedEdgesSet.insert edgeKey

  let result : CppDeps := {
    allStems := allStemsArr
    stemDepsOn := stemDepsOn
    dotEdges := dotEdges
    dotMissing := dotMissing
    externalEdges := externalEdges
  }
  return result

-- ─── C++ subgraph ────────────────────────────────────────────────────────────

def buildCppGraph (root cppRoot cppIncludeRoot : FilePath) (collapsed : Bool) : DotM Unit := do
  -- Exclude src/rust and focus only on the target C++ folders in src/
  let subdirs := ["include", "initialize", "kernel", "library", "runtime", "shell", "util"]
  let mut cppFiles : Array FilePath := #[]
  for subdir in subdirs do
    let subdirPath := cppRoot / subdir
    if ← isDir subdirPath then
      cppFiles := cppFiles ++ (← walkDir subdirPath #["cpp", "c", "h", "hpp"])

  emitLine "  subgraph cluster_cpp {"
  if collapsed then
    emitLine "    label=\"C++ source (src) [Collapsed]\"; style=filled; fillcolor=\"#f0e8ff\"; color=\"#882288\";"
  else
    emitLine "    label=\"C++ source (src)\"; style=filled; fillcolor=\"#f0e8ff\"; color=\"#882288\";"

  if collapsed then
    let mut groups : Std.HashMap String (Array Stem) := {}
    let mut addedStems : Std.HashSet Stem := {}
    for f in cppFiles do
      let s := stemOf f
      if addedStems.contains s then continue
      addedStems := addedStems.insert s
      let rel   := relPath cppRoot s
      let group := rel.components.head?.getD "(root)"
      groups := groups.insert group ((groups.getD group #[]).push s)

    for (group, stems) in groups.toList.toArray.qsort (·.1 < ·.1) do
      let gid := "cpp_grp_" ++ group.map fun c => if c.isAlphanum || c == '_' then c else '_'
      emitLine s!"    subgraph cluster_{gid} {"{"}"
      emitLine s!"      label=\"{group}\"; style=filled; fillcolor=\"#e8d8ff\";"
      for s in stems do
        let id := nodeId root s
        let pair ← makePair cppRoot s
        let lbl := collapsedLabel pair
        dotAddNode id lbl #[
          ("shape", "box"), ("style", "filled"), ("fillcolor", "#fff8ff"), ("fontsize", "9"),
        ]
        emitLine s!"      {id};"
      emitLine "    }"
  else
    let mut groups : Std.HashMap String (Array FilePath) := {}
    for f in cppFiles do
      let rel   := relPath cppRoot f
      let group := rel.components.head?.getD "(root)"
      groups := groups.insert group ((groups.getD group #[]).push f)

    for (group, files) in groups.toList.toArray.qsort (·.1 < ·.1) do
      let gid := "cpp_grp_" ++ group.map fun c => if c.isAlphanum || c == '_' then c else '_'
      emitLine s!"    subgraph cluster_{gid} {"{"}"
      emitLine s!"      label=\"{group}\"; style=filled; fillcolor=\"#e8d8ff\";"
      for f in files do
        let id    := nodeId root f
        let color := if f.extension == some "cpp" then "#fff8ff" else "#f8f0ff"
        dotAddNode id (f.fileName.getD f.toString) #[
          ("shape", "box"), ("style", "filled"), ("fillcolor", color), ("fontsize", "9"),
        ]
        emitLine s!"      {id};"
      emitLine "    }"

  emitLine "  }"

  let deps ← buildCppDeps root cppRoot cppIncludeRoot cppFiles collapsed

  let mut missingAdded : Std.HashSet String := {}
  for (f, t, color) in deps.dotEdges do
    dotAddEdge f t #[("color", color)]
  for (f, misId, lbl) in deps.dotMissing do
    unless missingAdded.contains misId do
      dotAddNode misId lbl #[("shape", "plaintext"), ("fontsize", "8"), ("fontcolor", "#aaaaaa")]
      missingAdded := missingAdded.insert misId
    dotAddEdge f misId #[("style", "dotted"), ("color", "#aaaaaa")]
  for (f, extLabel) in deps.externalEdges do
    let extId ← ensureExt extLabel
    dotAddEdge f extId #[("style", "dashed"), ("color", "#cc00cc")]

  let sorted := kahnSort deps.allStems deps.stemDepsOn
  buildOrderMd root sorted deps.stemDepsOn

-- ─── Force-Directed Interactive HTML Builder ─────────────────────────────────

def buildHtmlPage (nodesJs linksJs title : String) : String :=
  "<!DOCTYPE html>\n" ++
  "<html lang=\"en\">\n" ++
  "<head>\n" ++
  "  <meta charset=\"UTF-8\">\n" ++
  "  <title>" ++ title ++ "</title>\n" ++
  "  <style>\n" ++
  "    body { margin: 0; background: #0d0e15; font-family: system-ui, sans-serif; overflow: hidden; }\n" ++
  "    #search-box {\n" ++
  "      position: absolute; top: 20px; left: 20px; z-index: 100;\n" ++
  "      background: rgba(20, 22, 33, 0.95); border: 1px solid #2d3142;\n" ++
  "      border-radius: 8px; padding: 12px; width: 280px;\n" ++
  "      box-shadow: 0 4px 20px rgba(0,0,0,0.4);\n" ++
  "    }\n" ++
  "    #search-box input {\n" ++
  "      width: calc(100% - 16px); padding: 8px; background: #181b28; border: 1px solid #3c4257;\n" ++
  "      border-radius: 4px; color: #fff; outline: none; font-size: 0.9rem;\n" ++
  "    }\n" ++
  "    #search-box input:focus { border-color: #5856d6; }\n" ++
  "    #search-results {\n" ++
  "      max-height: 200px; overflow-y: auto; margin-top: 8px;\n" ++
  "    }\n" ++
  "    .search-item {\n" ++
  "      padding: 6px 8px; cursor: pointer; color: #a0aec0; font-size: 0.85rem; border-radius: 4px;\n" ++
  "    }\n" ++
  "    .search-item:hover { background: #5856d6; color: #fff; }\n" ++
  "    #legend {\n" ++
  "      position: absolute; bottom: 20px; left: 20px; z-index: 100;\n" ++
  "      background: rgba(20, 22, 33, 0.95); border: 1px solid #2d3142;\n" ++
  "      border-radius: 8px; padding: 12px; color: #a0aec0; font-size: 0.8rem;\n" ++
  "    }\n" ++
  "    .legend-item { display: flex; align-items: center; margin-bottom: 6px; }\n" ++
  "    .legend-color { width: 12px; height: 12px; border-radius: 50%; margin-right: 8px; }\n" ++
  "    #header {\n" ++
  "      position: absolute; top: 20px; right: 20px; z-index: 100; text-align: right; color: #fff;\n" ++
  "      pointer-events: none;\n" ++
  "    }\n" ++
  "    #header h1 { margin: 0; font-size: 1.25rem; font-weight: 600; }\n" ++
  "    #header p { margin: 4px 0 0 0; font-size: 0.8rem; color: #718096; }\n" ++
  "  </style>\n" ++
  "  <script src=\"https://cdn.jsdelivr.net/npm/force-graph\"></script>\n" ++
  "</head>\n" ++
  "<body>\n" ++
  "  <div id=\"header\">\n" ++
  "    <h1>" ++ title ++ "</h1>\n" ++
  "    <p>Hover nodes to highlight paths. Click nodes to focus & zoom.</p>\n" ++
  "  </div>\n" ++
  "  <div id=\"search-box\">\n" ++
  "    <input type=\"text\" id=\"search-input\" placeholder=\"Search file or module...\" oninput=\"onSearchInput()\">\n" ++
  "    <div id=\"search-results\"></div>\n" ++
  "  </div>\n" ++
  "  <div id=\"legend\">\n" ++
  "    <div style=\"font-weight:600; margin-bottom: 8px; color: #fff;\">Legend</div>\n" ++
  "    <div class=\"legend-item\"><div class=\"legend-color\" style=\"background: #9c27b0;\"></div>C++ Stems/Files</div>\n" ++
  "    <div class=\"legend-item\"><div class=\"legend-color\" style=\"background: #4caf50;\"></div>Rust Sources</div>\n" ++
  "    <div class=\"legend-item\"><div class=\"legend-color\" style=\"background: #2196f3;\"></div>Externals (Libs)</div>\n" ++
  "    <div class=\"legend-item\"><div class=\"legend-color\" style=\"background: #9e9e9e;\"></div>Unresolved Stems</div>\n" ++
  "  </div>\n" ++
  "  <div id=\"graph\"></div>\n" ++
  "\n" ++
  "  <script type=\"module\">\n" ++
  "    import { GUI } from 'https://esm.sh/dat.gui';\n" ++
  "    const gData = {\n" ++
  "      nodes: [\n" ++ nodesJs ++ "\n      ],\n" ++
  "      links: [\n" ++ linksJs ++ "\n      ]\n" ++
  "    };\n" ++
  "\n" ++
  "    const highlightNodes = new Set();\n" ++
  "    const highlightLinks = new Set();\n" ++
  "    let hoverNode = null;\n" ++
  "\n" ++
  "    // Cross-link nodes dynamically\n" ++
  "    const nodeMap = {};\n" ++
  "    gData.nodes.forEach(n => nodeMap[n.id] = n);\n" ++
  "\n" ++
  "    gData.links.forEach(link => {\n" ++
  "      const a = nodeMap[link.source];\n" ++
  "      const b = nodeMap[link.target];\n" ++
  "      if (a && b) {\n" ++
  "        !a.neighbors && (a.neighbors = []);\n" ++
  "        !b.neighbors && (b.neighbors = []);\n" ++
  "        a.neighbors.push(b);\n" ++
  "        b.neighbors.push(a);\n" ++
  "\n" ++
  "        !a.links && (a.links = []);\n" ++
  "        !b.links && (b.links = []);\n" ++
  "        a.links.push(link);\n" ++
  "        b.links.push(link);\n" ++
  "      }\n" ++
  "    });\n" ++
  "\n" ++
  "    const elem = document.getElementById('graph');\n" ++
  "    const Graph = ForceGraph()(elem)\n" ++
  "      .graphData(gData)\n" ++
  "      .dagMode('td')\n" ++
  "      .dagLevelDistance(100)\n" ++
  "      .backgroundColor('#0d0e15')\n" ++
  "      .nodeId('id')\n" ++
  "      .nodeRelSize(5)\n" ++
  "      .nodeLabel(node => `${node.label} [${node.group}]`)\n" ++
  "      .nodeColor(node => {\n" ++
  "        if (node === hoverNode) return '#ff3b30';\n" ++
  "        if (highlightNodes.has(node)) return '#ff9500';\n" ++
  "        if (node.type === 'cpp') return '#9c27b0';\n" ++
  "        if (node.type === 'rust') return '#4caf50';\n" ++
  "        if (node.type === 'external') return '#2196f3';\n" ++
  "        return '#9e9e9e';\n" ++
  "      })\n" ++
  "      .linkWidth(link => highlightLinks.has(link) ? 3 : 1)\n" ++
  "      .linkColor(link => highlightLinks.has(link) ? '#ff9500' : 'rgba(255,255,255,0.15)')\n" ++
  "      .linkDirectionalParticles(link => highlightLinks.has(link) ? 4 : 0)\n" ++
  "      .linkDirectionalParticleWidth(2.5)\n" ++
  "      .onNodeHover(node => {\n" ++
  "        highlightNodes.clear();\n" ++
  "        highlightLinks.clear();\n" ++
  "        if (node) {\n" ++
  "          highlightNodes.add(node);\n" ++
  "          node.neighbors?.forEach(neighbor => highlightNodes.add(neighbor));\n" ++
  "          node.links?.forEach(link => highlightLinks.add(link));\n" ++
  "        }\n" ++
  "        hoverNode = node || null;\n" ++
  "        updateStyle();\n" ++
  "      })\n" ++
  "      .onNodeClick(node => {\n" ++
  "        Graph.centerAt(node.x, node.y, 800);\n" ++
  "        Graph.zoom(3.5, 800);\n" ++
  "      });\n" ++
  "\n" ++
  "    function updateStyle() {\n" ++
  "      Graph.nodeColor(Graph.nodeColor())\n" ++
  "           .linkWidth(Graph.linkWidth())\n" ++
  "           .linkColor(Graph.linkColor());\n" ++
  "    }\n" ++
  "\n" ++
  "    // Search autocomplete logic\n" ++
  "    window.onSearchInput = function() {\n" ++
  "      const query = document.getElementById('search-input').value.toLowerCase();\n" ++
  "      const resultsDiv = document.getElementById('search-results');\n" ++
  "      resultsDiv.innerHTML = '';\n" ++
  "      if (!query) return;\n" ++
  "\n" ++
  "      const matches = gData.nodes.filter(n => n.label.toLowerCase().includes(query)).slice(0, 10);\n" ++
  "      matches.forEach(node => {\n" ++
  "        const item = document.createElement('div');\n" ++
  "        item.className = 'search-item';\n" ++
  "        item.textContent = node.label;\n" ++
  "        item.onclick = () => {\n" ++
  "          Graph.centerAt(node.x, node.y, 800);\n" ++
  "          Graph.zoom(3.5, 800);\n" ++
  "\n" ++
  "          highlightNodes.clear();\n" ++
  "          highlightLinks.clear();\n" ++
  "          highlightNodes.add(node);\n" ++
  "          node.neighbors?.forEach(neigh => highlightNodes.add(neigh));\n" ++
  "          node.links?.forEach(l => highlightLinks.add(l));\n" ++
  "          hoverNode = node;\n" ++
  "          updateStyle();\n" ++
  "\n" ++
  "          resultsDiv.innerHTML = '';\n" ++
  "          document.getElementById('search-input').value = node.label;\n" ++
  "        };\n" ++
  "        resultsDiv.appendChild(item);\n" ++
  "      });\n" ++
  "    };\n" ++
  "\n" ++
  "    // GUI Controls for Dag Orientation\n" ++
  "    const controls = { 'DAG Orientation': 'td' };\n" ++
  "    const gui = new GUI({ autoPlace: true });\n" ++
  "    gui.domElement.style.position = 'absolute';\n" ++
  "    gui.domElement.style.top = '20px';\n" ++
  "    gui.domElement.style.right = '20px';\n" ++
  "    gui.domElement.style.zIndex = '100';\n" ++
  "    gui.add(controls, 'DAG Orientation', ['td', 'bu', 'lr', 'rl', 'radialout', 'radialin', null])\n" ++
  "       .onChange(orientation => Graph.dagMode(orientation));\n" ++
  "    document.body.appendChild(gui.domElement);\n" ++
  "  </script>\n" ++
  "</body>\n" ++
  "</html>\n"

-- ─── Main ────────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  let args := args.toArray
  let rustOnly := args.contains "--rust-only"
  let cppOnly  := args.contains "--cpp-only"

  let outFile : FilePath :=
    match args.findIdx? (· == "--out") with
    | some i => args[i + 1]? |>.map (⟨·⟩) |>.getD "dep_graph.dot"
    | none   => "dep_graph.dot"

  let cwd ← IO.currentDir
  let root : FilePath ← do
    let mut dir := cwd
    let mut found := false
    for _ in [:10] do
      if ← isFile (dir / "lean-toolchain") then
        found := true; break
      match dir.parent with
      | some p => dir := p
      | none => break
    if found then pure dir else pure cwd

  let rustRoot       := root / "src" / "rust"
  let cppRoot        := root / "src"
  let cppIncludeRoot := cppRoot / "include"

  let preamble := [
    "digraph lean_deps {",
    "  rankdir=LR;", "  overlap=false;", "  splines=true;",
    "  fontname=\"sans-serif\";",
    "  node [fontname=\"monospace\", fontsize=10];",
    "  edge [fontsize=8];", "",
    "  subgraph cluster_externals {",
    "    label=\"External dependencies\"; style=filled; fillcolor=\"#fff0f0\"; color=\"#aa0000\";",
    "  }", "",
  ]

  -- Generate uncollapsed Graph Data
  let (_, dotSt) ← (do
    unless cppOnly do buildRustGraph root rustRoot false
    unless rustOnly do buildCppGraph root cppRoot cppIncludeRoot false
    : DotM Unit).run {}
  let dotContent :=
    String.intercalate "\n" (preamble ++ dotSt.lines.toList ++ ["}"]) ++ "\n"
  IO.FS.writeFile outFile dotContent
  IO.println s!"✅  Written uncollapsed DOT to {outFile}  ({dotContent.length} bytes)"

  -- Generate collapsed Graph Data
  let outFileColl : FilePath := ⟨outFile.toString.replace ".dot" "_collapsed.dot"⟩
  let (_, dotStColl) ← (do
    unless cppOnly do buildRustGraph root rustRoot true
    unless rustOnly do buildCppGraph root cppRoot cppIncludeRoot true
    : DotM Unit).run {}
  let dotContentColl :=
    String.intercalate "\n" (preamble ++ dotStColl.lines.toList ++ ["}"]) ++ "\n"
  IO.FS.writeFile outFileColl dotContentColl
  IO.println s!"✅  Written collapsed DOT to {outFileColl}  ({dotContentColl.length} bytes)"

  -- Write interactive Uncollapsed HTML Page (Force-Directed DAG)
  let htmlFile1 : FilePath := ⟨outFile.toString.replace ".dot" ".html"⟩
  let nodesJsStr1 := ",\n".intercalate dotSt.jsNodes.toList
  let linksJsStr1 := ",\n".intercalate dotSt.jsLinks.toList
  IO.FS.writeFile htmlFile1 (buildHtmlPage nodesJsStr1 linksJsStr1 "Lean4 Dependencies (Uncollapsed)")
  IO.println s!"✅  Written interactive uncollapsed page to {htmlFile1}"

  -- Write interactive Collapsed HTML Page (Force-Directed DAG)
  let htmlFile2 : FilePath := ⟨outFileColl.toString.replace ".dot" ".html"⟩
  let nodesJsStr2 := ",\n".intercalate dotStColl.jsNodes.toList
  let linksJsStr2 := ",\n".intercalate dotStColl.jsLinks.toList
  IO.FS.writeFile htmlFile2 (buildHtmlPage nodesJsStr2 linksJsStr2 "Lean4 Dependencies (Collapsed)")
  IO.println s!"✅  Written interactive collapsed page to {htmlFile2}"

  IO.println s!"Open uncollapsed interactive graph: xdg-open \"{htmlFile1}\""
  IO.println s!"Open collapsed interactive graph: xdg-open \"{htmlFile2}\""

  let mut dotBin := false
  try
    let _ ← IO.Process.run { cmd := "which", args := #["dot"] }
    dotBin := true
  catch _ =>
    pure ()

  if dotBin then
    try
      IO.println "🔄  Rendering SVGs with dot…"
      let svgFile : FilePath := ⟨outFile.toString.replace ".dot" "" ++ ".svg"⟩
      let svgFileColl : FilePath := ⟨outFileColl.toString.replace ".dot" "" ++ ".svg"⟩
      let _ ← IO.Process.run { cmd := "dot", args := #["-Tsvg", outFile.toString, "-o", svgFile.toString] }
      IO.println s!"✅  Written {svgFile}"
      let _ ← IO.Process.run { cmd := "dot", args := #["-Tsvg", outFileColl.toString, "-o", svgFileColl.toString] }
      IO.println s!"✅  Written {svgFileColl}"
    catch e =>
      IO.eprintln s!"⚠️  dot render failed: {e}"
  return 0

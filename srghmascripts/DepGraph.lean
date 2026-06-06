import Std.Data.HashMap
import Std.Data.HashSet
import System.FilePath

/-!
  DepGraph.lean — generate order_of_review.md + dep_graph.dot

  Walk src/removed_cpp/** for C++ files, parse #include lines,
  build a stem-level dependency graph, topo-sort (Kahn's algorithm),
  build a rose tree for display, and render both a Markdown review
  order and a Graphviz DOT file.

  As a Lake script (add `script depGraph { run := DepGraph.main }` to
  your lakefile.lean after importing this file, or just use lake run):

    lake run depGraph [--rust-only | --cpp-only] [--out graph.dot]

  As a standalone Lean script:

    elan run --install leanprover/lean4:v4.30.0 lean --run DepGraph.lean
-/

open System (FilePath)

-- ─── Known external dependency groups ────────────────────────────────────────
-- Each entry: (label, patterns).  If any pattern is a substring of an #include
-- target, the include is classified as that external.

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
  name : FilePath        -- relative to cppRoot, no extension
  h    : Option FilePath -- relative .h or .hpp
  cpp  : Option FilePath -- relative .cpp
  deriving Repr

inductive TaskTree where
  | node : FilePair → Array TaskTree → TaskTree
  deriving Repr

-- ─── File system helpers ──────────────────────────────────────────────────────

def isFile (p : FilePath) : IO Bool :=
  (IO.FS.metadata p).map (·.type == IO.FS.FileType.file) |>.catchExceptions (fun _ => pure false)

def isDir (p : FilePath) : IO Bool :=
  (IO.FS.metadata p).map (·.type == IO.FS.FileType.dir) |>.catchExceptions (fun _ => pure false)

partial def walkDir (dir : FilePath) (exts : Array String) : IO (Array FilePath) := do
  unless ← isDir dir do return #[]
  let entries ← IO.FS.readDir dir
  let names := entries.toArray.map (·.fileName) |>.qsort (· < ·)
  let mut result : Array FilePath := #[]
  for name in names do
    if name.startsWith "." then continue
    let full := dir / name
    if ← isDir full then
      result := result ++ (← walkDir full exts)
    else if exts.any (fun e => full.extension == some e) then
      result := result.push full
  return result

/-- Drop the extension: "/foo/bar.cpp" → "/foo/bar" -/
def stemOf (p : FilePath) : Stem :=
  match p.extension with
  | none     => p
  | some ext => ⟨p.toString.dropRight (ext.length + 1)⟩

/-- Make a DOT-safe identifier from an absolute path relative to `root`. -/
def nodeId (root : FilePath) (p : FilePath) : String :=
  let b := root.toString
  let t := p.toString
  let rel := if t.startsWith (b ++ "/") then t.drop (b.length + 1) else t
  rel.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Simple relative-path computation (string prefix strip). -/
def relPath (base : FilePath) (target : FilePath) : FilePath :=
  let b := base.toString ++ "/"
  let t := target.toString
  if t.startsWith b then ⟨t.drop b.length⟩ else target

/-- Safely canonicalise a path via `realpath`. -/
def realpathSafe (p : FilePath) : IO FilePath :=
  (IO.Process.run { cmd := "realpath", args := #[p.toString] }).map
    (fun s => ⟨s.trimRight⟩)
  |>.catchExceptions (fun _ => pure p)

-- ─── Review status ────────────────────────────────────────────────────────────

def isReviewed (srcPath : FilePath) : IO Bool := do
  let ext := srcPath.extension.getD ""
  let mdPath : FilePath := ⟨srcPath.toString.dropRight (ext.length + 1) ++ "md"⟩
  unless ← isFile mdPath do return false
  let text ← IO.FS.readFile mdPath
  if text.containsSubstr "- [ ]" then return false
  if text.toUpper.containsSubstr "TODO" then return false
  return true

-- ─── Include parsing ──────────────────────────────────────────────────────────

/-- Parse `#include "foo.h"` or `#include <foo.h>` → some "foo.h".
    Returns none for non-include lines. -/
def parseInclude (line : String) : Option String :=
  let s := line.trimLeft
  guard (s.startsWith "#include") |>.map fun () =>
    let rest := (s.drop 8).trimLeft
    let (open', close') := if rest.startsWith "\"" then ('"', '"') else ('<', '>')
    let inner := rest.drop 1
    let endIdx := inner.indexOf close'
    inner.take endIdx
  |>.join

/-- Match `target` against known externals; return label if matched. -/
def matchExternal (target : String) : Option String :=
  knownExternals.findSome? fun (lbl, pats) =>
    if pats.any (target.containsSubstr ·) then some lbl else none

-- ─── C++ dependency graph ─────────────────────────────────────────────────────

structure CppDeps where
  allStems      : Array Stem
  stemDepsOn    : Std.HashMap Stem (Std.HashSet Stem)
  dotEdges      : Array (String × String × String)  -- (from, to, color)
  dotMissing    : Array (String × String × String)  -- (from, misId, label)
  externalEdges : Array (String × String)           -- (from, extLabel)

def buildCppDeps (root cppRoot cppIncludeRoot : FilePath)
    (cppFiles : Array FilePath) : IO CppDeps := do
  -- Build resolved-path → stem lookup (raw path + realpath → stem)
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

  for f in cppFiles do
    let fromStem := stemOf f
    let fId      := nodeId root f
    let src      ← IO.FS.readFile f
    let baseDir  := f.parent.getD cppRoot

    for line in src.splitOn "\n" do
      let some target := parseInclude line | continue

      if let some extLabel := matchExternal target then
        externalEdges := externalEdges.push (fId, extLabel)
        continue

      -- Try three resolution strategies in order
      let candidates := #[baseDir / target, cppRoot / target, cppIncludeRoot / target]
      let mut resolved : Option FilePath := none
      for c in candidates do
        if ← isFile c then resolved := some c; break

      if let some res := resolved then
        let toId := nodeId root res
        dotEdges := dotEdges.push (fId, toId, "#882288")

        let rp ← realpathSafe res
        let toStem : Option Stem :=
          resolvedToStem.get? res.toString
          |>.orElse (fun _ => resolvedToStem.get? rp.toString)
          |>.orElse (fun _ =>
            let s := stemOf res
            if allStemsSet.contains s then some s else none)

        match toStem with
        | some ts =>
          if ts != fromStem then
            let cur := stemDepsOn.getD fromStem {}
            stemDepsOn := stemDepsOn.insert fromStem (cur.insert ts)
        | none =>
          IO.eprintln s!"  ⚠ include outside CPP_ROOT: {res} (from {relPath cppRoot f})"
      else
        -- not angle-bracket and not a known std header
        let isAngle := target.startsWith "<"
        let bare    := !target.contains '/'
        if !isAngle && !(bare && stdHeaders.contains target) then
          let misId := "missing_" ++
            target.map fun c => if c.isAlphanum || c == '_' then c else '_'
          dotMissing := dotMissing.push (fId, misId, target)

  return { allStems := allStemsArr, stemDepsOn, dotEdges, dotMissing, externalEdges }

-- ─── Kahn's topological sort ──────────────────────────────────────────────────

/-- Returns stems in deps-first order (leaves of the include graph first).
    Cycle members are appended alphabetically. -/
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

  -- Append any cycle members alphabetically
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
      return none
  }

/-- Build the display rose tree.

    Parent selection: for each stem, its parent is the eligible dependency
    (idx < curIdx) with the HIGHEST index.  Only strictly-earlier deps are
    eligible — later-appearing ones are due to dep-graph cycles and would
    create cycles in the rose tree, causing DFS to silently drop nodes. -/
def buildRoseTree (cppRoot : FilePath) (sortedStems : Array Stem)
    (stemDepsOn : Std.HashMap Stem (Std.HashSet Stem)) : IO (Array TaskTree) := do
  -- Index each stem
  let mut stemToIdx : Std.HashMap Stem Nat := {}
  for i in [:sortedStems.size] do
    stemToIdx := stemToIdx.insert sortedStems[i]! i

  -- Build FilePairs
  let pairs ← sortedStems.mapM (makePair cppRoot)

  -- For each node: which child indices?
  let n := sortedStems.size
  let mut childrenOf : Array (Array Nat) := Array.mkArray n #[]
  let mut parentOf   : Array (Option Nat) := Array.mkArray n none

  for i in [:n] do
    let stem := sortedStems[i]!
    -- Eligible deps: those with index strictly < i
    let eligible := (stemDepsOn.getD stem {}).toList.filterMap fun dep =>
      stemToIdx.get? dep |>.bind fun j => if j < i then some j else none
    match eligible with
    | [] => pure ()  -- root
    | _  =>
      -- Highest index wins; tie-break: prefer lower index (deterministic)
      let bestJ := eligible.foldl (init := eligible.head!) fun best j =>
        if j > best then j else best
      parentOf   := parentOf.set! i (some bestJ)
      childrenOf := childrenOf.set! bestJ (childrenOf[bestJ]!.push i)

  -- Assemble immutable rose tree via DFS
  let rec build (i : Nat) : TaskTree :=
    .node pairs[i]! (childrenOf[i]!.map build)

  let roots := (Array.range n).filter (fun i => parentOf[i]! == none)
  return roots.map build

-- ─── Rose tree → Markdown ────────────────────────────────────────────────────

def renderTree (cppRoot : FilePath) (roots : Array TaskTree) : IO (Array String) := do
  let mut lines : Array String := #[]
  let rec visit (t : TaskTree) (depth : Nat) : IO Unit := do
    let .node pair children := t
    let files : Array FilePath := (pair.h.toList ++ pair.cpp.toList).toArray
    let fileStr := (files.map fun f => s!"`{f}`").toList |> ", ".intercalate
    -- rewrite "a.h, b.cpp" → "a.h and b.cpp"
    let fileStr := fileStr.replace ", " " and "
    let allDone ← files.allM fun f => isReviewed (cppRoot / f)
    let checkbox := if allDone then "[x]" else "[ ]"
    let indent   := String.mk (List.replicate (depth * 2) ' ')
    lines := lines.push s!"{indent}- {checkbox} {pair.name} ({fileStr})"
    for child in children do
      visit child (depth + 1)
  for root in roots do
    visit root 0
  return lines

-- ─── MD validation ───────────────────────────────────────────────────────────

def validateMd (lines : Array String) : Except String Unit := do
  let mut prevIndent := 0
  for i in [:lines.size] do
    let line    := lines[i]!
    let trimmed := line.trimLeft
    unless trimmed.startsWith "- " do
      prevIndent := 0; continue
    let indent := line.length - trimmed.length
    if indent % 2 != 0 then
      throw s!"MD007: line {i+1} indent={indent} not a multiple of 2\n  {line}"
    if indent > prevIndent + 2 then
      throw s!"MD007 no-skip: line {i+1} jumped {prevIndent}→{indent}\n  {line}"
    prevIndent := indent

-- ─── Markdown file writer ────────────────────────────────────────────────────

def buildOrderMd (cppRoot : FilePath) (sortedStems : Array Stem)
    (stemDepsOn : Std.HashMap Stem (Std.HashSet Stem)) : IO Unit := do
  let roots  ← buildRoseTree cppRoot sortedStems stemDepsOn
  let body   ← renderTree cppRoot roots

  -- Completeness check
  let count := body.filter (·.trimLeft.startsWith "- ") |>.size
  if count != sortedStems.size then
    throw <| .userError s!"Rose tree completeness failure: {count} items rendered, expected {sortedStems.size}.\
      \nCycle in rose tree — check buildRoseTree."

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

  let mdPath := cppRoot / "order_of_review.md"
  IO.FS.writeFile mdPath (String.intercalate "\n" allLines.toList ++ "\n")
  IO.println s!"✅  Written {mdPath}"

-- ─── DOT state monad ─────────────────────────────────────────────────────────

structure DotSt where
  lines       : Array String             := #[]
  addedNodes  : Std.HashSet String       := {}
  addedEdges  : Std.HashSet String       := {}
  externalIds : Std.HashMap String String := {}

abbrev DotM := StateT DotSt IO

def emitLine (s : String) : DotM Unit :=
  modify fun st => { st with lines := st.lines.push s }

def dotAddNode (id label : String) (attrs : Array (String × String)) : DotM Unit := do
  let st ← get
  if st.addedNodes.contains id then return
  modify fun s => { s with addedNodes := s.addedNodes.insert id }
  let attrList := (#[("label", label)] ++ attrs)
    .map (fun (k, v) => s!"{k}=\"{v}\"")
    .toList |> ", ".intercalate
  emitLine s!"  {id} [{attrList}];"

def dotAddEdge (from' to' : String) (attrs : Array (String × String)) : DotM Unit := do
  let key := s!"{from'}->{to'}"
  let st ← get
  if st.addedEdges.contains key then return
  modify fun s => { s with addedEdges := s.addedEdges.insert key }
  let attrStr := (attrs.map (fun (k,v) => s!"{k}=\"{v}\"")).toList |> ", ".intercalate
  let line := if attrStr.isEmpty then s!"  {from'} -> {to'};"
    else s!"  {from'} -> {to'} [{attrStr}];"
  emitLine line

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

/-- Crude TOML value extraction: find `key = "value"` in a section. -/
def tomlStr (src key : String) : Option String := do
  let idx ← src.findSubstr? key
  let after := (src.drop (idx + key.length)).trimLeft
  guard (after.startsWith "=")
  let after := (after.drop 1).trimLeft
  guard (after.startsWith "\"")
  let inner := after.drop 1
  let end' ← inner.findSubstr? "\""
  return inner.take end'

/-- Parse `members = [...]` from workspace Cargo.toml. -/
def cargoMembers (src : String) : Array String :=
  let go := do
    let idx ← src.findSubstr? "members"
    let after := (src.drop (idx + 7)).trimLeft
    guard (after.startsWith "=")
    let after := (after.drop 1).trimLeft
    guard (after.startsWith "[")
    let inner := after.drop 1
    let end' ← inner.findSubstr? "]"
    return inner.take end'
  match go with
  | none => #[]
  | some content =>
    content.splitOn ","
      |>.toArray
      |>.map (·.trim.replace "\"" "" |>.trim)
      |>.filter (· != "")

def buildRustGraph (root rustRoot : FilePath) : DotM Unit := do
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

    -- Find package name after [package]
    let pkgName :=
      match cargo.findSubstr? "[package]" with
      | none => member
      | some pi =>
        let after := cargo.drop (pi + 9)
        tomlStr after "name" |>.getD member

    let rsFiles ← walkDir (mDir / "src") #["rs"]

    let clusterId := nodeId root mDir
    emitLine s!"    subgraph cluster_{clusterId} {{"
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
      -- External deps used in source
      for (extLabel, pats) in knownExternals do
        if pats.any (src.containsSubstr ·) then
          let extId ← ensureExt extLabel
          dotAddEdge id extId #[("style", "dashed"), ("color", "#cc4400")]
      -- Port-of annotation
      for line in src.splitOn "\n" do
        let t := line.trimLeft
        if (t.startsWith "// Port" || t.startsWith "// port") then
          if let some oi := t.findSubstr? " of " then
            let cppRel := (t.drop (oi + 4)).trim |>.replace "src/" ""
            let cppId  := "cpp_" ++ cppRel.map fun c =>
              if c.isAlphanum || c == '_' then c else '_'
            dotAddNode cppId cppRel #[
              ("shape", "note"), ("style", "filled"), ("fillcolor", "#fff0cc"),
              ("fontsize", "9"), ("fontcolor", "#664400"),
            ]
            dotAddEdge id cppId #[
              ("style", "dotted"), ("color", "#888800"),
              ("label", "port of"), ("fontsize", "8"),
            ]

  emitLine "  }"

-- ─── C++ subgraph ────────────────────────────────────────────────────────────

def buildCppGraph (root cppRoot cppIncludeRoot : FilePath) : DotM Unit := do
  let cppFiles ← walkDir cppRoot #["cpp", "h", "hpp"]

  emitLine "  subgraph cluster_cpp {"
  emitLine "    label=\"C++ source (src/removed_cpp)\"; style=filled; fillcolor=\"#f0e8ff\"; color=\"#882288\";"

  -- Group by first path component
  let mut groups : Std.HashMap String (Array FilePath) := {}
  for f in cppFiles do
    let rel   := relPath cppRoot f
    let group := rel.components.head?.getD "(root)"
    groups := groups.insert group ((groups.getD group #[]).push f)

  for (group, files) in groups.toList.toArray.qsort (·.1 < ·.1) do
    let gid := "cpp_grp_" ++ group.map fun c => if c.isAlphanum || c == '_' then c else '_'
    emitLine s!"    subgraph cluster_{gid} {{"
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

  -- Build dependency graph
  let deps ← buildCppDeps root cppRoot cppIncludeRoot cppFiles

  -- Emit DOT edges
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

  -- order_of_review.md
  let sorted := kahnSort deps.allStems deps.stemDepsOn
  buildOrderMd cppRoot sorted deps.stemDepsOn

-- ─── Main ────────────────────────────────────────────────────────────────────

def main (args : List String) : IO UInt32 := do
  let args := args.toArray
  let rustOnly := args.contains "--rust-only"
  let cppOnly  := args.contains "--cpp-only"

  -- Parse --out <file>
  let outFile : FilePath :=
    match args.findIdx? (· == "--out") with
    | some i => args.get? (i + 1) |>.map (⟨·⟩) |>.getD "dep_graph.dot"
    | none   => "dep_graph.dot"

  -- Determine project root: walk upward from cwd until lean-toolchain is found
  let cwd ← IO.currentDir
  let root : FilePath ← do
    let mut dir := cwd
    let mut found := false
    for _ in [:10] do
      if ← isFile (dir / "lean-toolchain") do
        found := true; break
      if let some p := dir.parent then dir := p else break
    if found then pure dir else pure cwd

  let rustRoot       := root / "src" / "rust"
  let cppRoot        := root / "src" / "removed_cpp"
  let cppIncludeRoot := cppRoot / "include"

  -- Run DOT builder
  let (_, dotSt) ← (do
    unless cppOnly do buildRustGraph root rustRoot
    unless rustOnly do buildCppGraph root cppRoot cppIncludeRoot
    : DotM Unit).run {}

  -- Write DOT file
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
  let dotContent :=
    String.intercalate "\n" (preamble ++ dotSt.lines.toList ++ ["}"]) ++ "\n"
  IO.FS.writeFile outFile dotContent

  IO.println s!"✅  Written {outFile}  ({dotContent.length} bytes)"
  IO.println s!"   Nodes: {dotSt.addedNodes.size}   Edges: {dotSt.addedEdges.size}"

  -- Auto-render SVG
  let svgFile : FilePath := ⟨outFile.toString.replace ".dot" "" ++ ".svg"⟩
  let dotBin ←
    (IO.Process.run { cmd := "which", args := #["dot"] }).map (fun _ => true)
    |>.catchExceptions (fun _ => pure false)

  if dotBin then
    try
      IO.println "🔄  Rendering SVG with dot…"
      let _ ← IO.Process.run { cmd := "dot", args := #["-Tsvg", outFile.toString, "-o", svgFile.toString] }
      IO.println s!"✅  Written {svgFile}"
      IO.println s!"\nOpen: xdg-open \"{svgFile}\""
    catch e =>
      IO.eprintln s!"⚠️  dot render failed: {e}"
      printManual outFile svgFile
  else
    printManual outFile svgFile
  return 0
where
  printManual (outFile svgFile : FilePath) : IO Unit := do
    IO.println s!"Render with:"
    IO.println s!"   dot -Tsvg {outFile} -o {svgFile}"
    IO.println s!"   dot -Tpng {outFile} -o {⟨outFile.toString.replace \".dot\" \".png\"⟩}"

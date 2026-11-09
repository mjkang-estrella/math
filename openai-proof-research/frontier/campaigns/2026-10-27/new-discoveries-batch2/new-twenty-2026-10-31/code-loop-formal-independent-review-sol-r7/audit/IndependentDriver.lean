import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Environment
import Lean.Util.Path
open Lean

def nodeParts : Expr → String × Array Expr
  | .bvar i => (s!"bvar {i}",#[])
  | .fvar i => (s!"fvar {reprStr i}",#[])
  | .mvar i => (s!"mvar {reprStr i}",#[])
  | .sort l => (s!"sort {reprStr l}",#[])
  | .const n ls => (s!"const {reprStr n} {reprStr ls}",#[])
  | .app f a => ("app",#[f,a])
  | .lam n t b bi => (s!"lam {reprStr n} {reprStr bi}",#[t,b])
  | .forallE n t b bi => (s!"forall {reprStr n} {reprStr bi}",#[t,b])
  | .letE n t v b nd => (s!"let {reprStr n} {nd}",#[t,v,b])
  | .lit l => (s!"literal {reprStr l}",#[])
  | .mdata md e => (s!"mdata {reprStr md}",#[e])
  | .proj n i e => (s!"proj {reprStr n} {i}",#[e])

def dumpDAG (root : Expr) : IO Unit := do
  let mut ids : ExprMap Nat := {}
  ids := ids.insert root 0
  let mut seen : ExprSet := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    let (tag,children) := nodeParts e
    let mut links : Array Nat := #[]
    for c in children do
      unless ids.contains c do
        ids := ids.insert c ids.size
        todo := todo.push c
      links := links.push (ids[c]!)
    IO.println s!"NODE {ids[e]!} {tag} CHILDREN {links}"
  IO.println s!"DAG_COMPLETE NODES {ids.size}"

def main : IO Unit := do
  IO.println "STANDALONE_AUDIT_START"
  (← IO.getStdout).flush
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `CodeLoopTransport, importAll := true}] {} 0
  let modules := #[`CodeLoopFactor, `CodeLoopCount, `CodeLoopSets, `CodeLoopGeom,
    `CodeLoopCodes, `CodeLoopSpace, `CodeLoopWeight, `CodeLoopLoop, `CodeLoopClasses,
    `CodeLoopIntersections, `CodeLoopRepresentations, `CodeLoopSigns, `CodeLoopLiteral, `CodeLoopFin50, `CodeLoopTransport]
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData
  do
    IO.println "AUDIT_HEADER_READY"
    (← IO.getStdout).flush
  let mut roots : Array Name := #[]
  for idx in [:moduleData.size] do
    if modules.contains moduleNames[idx]! then
      let data := moduleData[idx]!
      IO.println s!"MODULE_INVENTORY {moduleNames[idx]!} CONSTANTS {data.constNames.size} EXTRA {data.extraConstNames}"
      roots := roots ++ data.constNames
      for n in data.extraConstNames do
        if (env.find? n).isSome then roots := roots.push n
        else IO.println s!"IR_ONLY_EXTRA {n}"
  if roots.isEmpty then throw (IO.userError "empty root audit")
  for m in modules do
    unless moduleNames.contains m do throw (IO.userError s!"missing production module {m}")
  let mut independentRoots : NameSet := {}
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modules.contains moduleNames[idx.toNat]! then
        independentRoots := independentRoots.insert n
        unless roots.contains n do throw (IO.userError s!"origin declaration omitted {n}")
  for n in roots do
    unless independentRoots.contains n do throw (IO.userError s!"foreign root {n}")
  IO.println s!"INDEPENDENT_ORIGIN_MATCH {independentRoots.size}"

  IO.println s!"ROOTS {roots} COUNT {roots.size}"
  (← IO.getStdout).flush
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw (IO.userError s!"missing actual constant {n}")
    if ci.isUnsafe || ci.isPartial then throw (IO.userError s!"unsafe/partial actual dependency {n}")
    if roots.contains n then
      if (Compiler.getImplementedBy? env n).isSome || (getExternAttrData? env n).isSome then
        throw (IO.userError s!"production extern/implementedBy {n}")
    let origin := match env.getModuleIdxFor? n with
      | some idx => toString moduleNames[idx.toNat]!
      | none => "current-module"
    let value := ci.value? (allowOpaque := true)
    if let .axiomInfo _ := ci then
      axioms := axioms.insert n
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throw (IO.userError s!"forbidden actual axiom {n}")
    IO.println s!"ACTUAL {n} ORIGIN {origin} UNSAFE {ci.isUnsafe} TYPE_DAG"
    dumpDAG ci.type
    if let some v := value then
      IO.println "VALUE_DAG"
      dumpDAG v
    else IO.println "NO_VALUE"

    for d in ci.type.getUsedConstants do pending := pending.push d
    if let some v := value then
      for d in v.getUsedConstants do pending := pending.push d
  IO.println s!"AUDIT_COMPLETE ROOTS {roots.size} CLOSURE {seen.size} AXIOMS {axioms.toArray}"


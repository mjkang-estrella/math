import CodeLoopFin50
import Lean

open Lean Elab Command


run_cmd liftIO do
  IO.println "BEFORE_NODE_PARTS"
  (← IO.getStdout).flush

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

run_cmd liftIO do
  IO.println "BEFORE_DAG_DUMPER"
  (← IO.getStdout).flush

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

run_cmd liftIO do
  IO.println "DAG_FUNCTIONS_ELABORATED"
  (← IO.getStdout).flush

elab "audit_actual_closure" : command => do
  liftIO do
    IO.println "AUDIT_START"
    (← IO.getStdout).flush
  let env ← getEnv
  let modules := #[`CodeLoopFactor, `CodeLoopCount, `CodeLoopSets, `CodeLoopGeom,
    `CodeLoopCodes, `CodeLoopSpace, `CodeLoopWeight, `CodeLoopLoop, `CodeLoopClasses,
    `CodeLoopIntersections, `CodeLoopRepresentations, `CodeLoopSigns, `CodeLoopLiteral, `CodeLoopFin50]
  let moduleNames := env.header.moduleNames
  liftIO do
    IO.println "AUDIT_HEADER_READY"
    (← IO.getStdout).flush
  let mut roots : Array Name := #[]
  for idx in [:env.header.moduleData.size] do
    if modules.contains moduleNames[idx]! then
      let data := env.header.moduleData[idx]!
      liftIO <| IO.println s!"MODULE_INVENTORY {moduleNames[idx]!} CONSTANTS {data.constNames.size} EXTRA {data.extraConstNames}"
      roots := roots ++ data.constNames
      for n in data.extraConstNames do
        if (env.find? n).isSome then roots := roots.push n
        else liftIO <| IO.println s!"IR_ONLY_EXTRA {n}"
  if roots.isEmpty then throwError "empty root audit"
  liftIO <| IO.println s!"ROOTS {roots} COUNT {roots.size}"
  liftIO <| (← IO.getStdout).flush
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing actual constant {n}"
    if ci.isUnsafe then throwError "unsafe actual dependency {n}"
    let origin := match env.getModuleIdxFor? n with
      | some idx => toString moduleNames[idx.toNat]!
      | none => "current-module"
    let value := ci.value? (allowOpaque := true)
    if let .axiomInfo _ := ci then
      axioms := axioms.insert n
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throwError "forbidden actual axiom {n}"
    liftIO <| IO.println s!"ACTUAL {n} ORIGIN {origin} UNSAFE {ci.isUnsafe} TYPE_DAG"
    liftIO <| dumpDAG ci.type
    if let some v := value then
      liftIO <| IO.println "VALUE_DAG"
      liftIO <| dumpDAG v
    else liftIO <| IO.println "NO_VALUE"

    for d in ci.type.getUsedConstants do pending := pending.push d
    if let some v := value then
      for d in v.getUsedConstants do pending := pending.push d
  liftIO <| IO.println s!"AUDIT_COMPLETE ROOTS {roots.size} CLOSURE {seen.size} AXIOMS {axioms.toArray}"

audit_actual_closure
#print axioms literal2019_refuted
#print axioms D50_no_permutation

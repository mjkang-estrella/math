import PolynexusLiteral
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rawIntern (e : Expr) (ids : Std.HashMap Expr Nat) (todo : Array Expr) :
    Nat × Std.HashMap Expr Nat × Array Expr :=
  match ids[e]? with
  | some i => (i,ids,todo)
  | none => (ids.size,ids.insert e ids.size,todo.push e)

def rawParts (e : Expr) : String × Array Expr :=
  match e with
  | .bvar i => (s!"bvar {i}",#[])
  | .fvar i => (s!"fvar {i.name}",#[])
  | .mvar i => (s!"mvar {i.name}",#[])
  | .sort u => (s!"sort {repr u}",#[])
  | .const n us => (s!"const {n} {repr us}",#[])
  | .app f a => ("app",#[f,a])
  | .lam n t b bi => (s!"lam {n} {repr bi}",#[t,b])
  | .forallE n t b bi => (s!"forall {n} {repr bi}",#[t,b])
  | .letE n t v b nd => (s!"let {n} {nd}",#[t,v,b])
  | .lit l => (s!"lit {repr l}",#[])
  | .mdata md b => (s!"mdata {repr md}",#[b])
  | .proj n i b => (s!"proj {n} {i}",#[b])

run_cmd do
  let env ← getEnv
  let own := #[`PolynexusDiag, `PolynexusSrc, `PolynexusProd, `PolynexusClose,
    `PolynexusSrcPrd, `PolynexusPairs, `PolynexusCount, `PolynexusPartition,
    `PolynexusGap, `PolynexusGapCount, `PolynexusEval, `PolynexusLiteral]
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if own.contains env.header.moduleNames[idx.toNat]! then roots := roots.push name
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut axioms : NameSet := {}
  let mut ids : Std.HashMap Expr Nat := {}
  let mut nodes : Array Expr := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "missing {name}"
    let origin := (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!
    if ci.isUnsafe then throwError "unsafe {name}"
    let (ty,ids',nodes') := rawIntern ci.type ids nodes
    ids := ids'; nodes := nodes'
    let mut body : Option Nat := none
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      let (bi,ids',nodes') := rawIntern v ids nodes
      ids := ids'; nodes := nodes'; body := some bi
      deps := deps ++ v.getUsedConstants
    liftIO <| IO.println s!"DECL {name} ORIGIN {origin} UNSAFE {ci.isUnsafe} TYPE_NODE {ty} BODY_NODE {body}"
    if ci matches .axiomInfo _ then
      axioms := axioms.insert name
      if name != `propext && name != `Classical.choice && name != `Quot.sound then
        throwError "forbidden axiom {name}"
    for dep in deps do
      if !seen.contains dep then todo := todo.push dep
    while !nodes.isEmpty do
      let e := nodes.back!
      nodes := nodes.pop
      let i := ids[e]!
      let (tag,children) := rawParts e
      let mut childrenIds : Array Nat := #[]
      for c in children do
        let (j,ids',nodes') := rawIntern c ids nodes
        ids := ids'; nodes := nodes'; childrenIds := childrenIds.push j
      liftIO <| IO.println s!"NODE {i} {tag} CHILDREN {childrenIds}"
  liftIO <| IO.println s!"ROOT_COUNT {roots.size} CLOSURE_COUNT {seen.size} NODE_COUNT {ids.size} AXIOMS {axioms.toList}"

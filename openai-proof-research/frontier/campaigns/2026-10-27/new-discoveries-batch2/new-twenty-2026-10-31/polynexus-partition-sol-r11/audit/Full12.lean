import PolynexusLiteral
import Lean
open Lean Elab Command
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.maxSteps 1000000000
set_option pp.deepTerms true
set_option pp.privateNames true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
run_cmd do
  let env ← getEnv
  let own := #[`PolynexusDiag, `PolynexusSrc, `PolynexusProd, `PolynexusClose,
    `PolynexusSrcPrd, `PolynexusPairs, `PolynexusCount, `PolynexusPartition,
    `PolynexusGap, `PolynexusGapCount, `PolynexusEval, `PolynexusLiteral]
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if own.contains env.header.moduleNames[idx.toNat]! then
        roots := roots.push name
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "missing constant {name}"
    let origin := (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!
    logInfo m!"DECL {name} ORIGIN {origin} UNSAFE {ci.isUnsafe}"
    if ci.isUnsafe then throwError "unsafe declaration {name}"
    let selected := (hash name).toNat % 16 == 12
    if selected then
      logInfo m!"FULL_DECL {name}"
      logInfo m!"TYPE {ci.type}"
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      if selected then logInfo m!"BODY {value}"
      deps := deps ++ value.getUsedConstants
    else
      logInfo m!"NO_BODY {name}"
    if ci matches .axiomInfo _ then
      axioms := axioms.insert name
      if name != `propext && name != `Classical.choice && name != `Quot.sound then
        throwError "forbidden axiom {name}"
    for dep in deps do
      if !seen.contains dep then todo := todo.push dep
  logInfo m!"ROOT_COUNT {roots.size} CLOSURE_COUNT {seen.size} AXIOMS {axioms.toList}"
#print axioms polynexus_literal
#print axioms PNZ_source
#print axioms polynexus_one

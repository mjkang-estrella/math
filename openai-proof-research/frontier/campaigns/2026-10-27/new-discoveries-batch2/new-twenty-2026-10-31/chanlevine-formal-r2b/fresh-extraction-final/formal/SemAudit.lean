import SemRegression
import Lean.Util.CollectAxioms
open Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
run_cmd do
  let env ← getEnv
  let locals := #[`Dynamics, `Reduction, `SourceSemantics, `SemCanonical, `SemWords,
    `SemPeriodic, `SemFinal, `SemRegression]
  let mut work : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if locals.contains env.header.moduleNames[idx.toNat]! then
        work := work.push n
        logInfo m!"ROOT {n}"
  let mut seen : NameSet := {}
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing declaration {n}"
    if let .axiomInfo _ := ci then
      logInfo m!"CLOSURE_AXIOM {n}"
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throwError "Forbidden closure axiom {n}"
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? then deps := deps ++ v.getUsedConstants
    if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
    let impl := Lean.Compiler.getImplementedBy? env n
    let ext := isExtern env n
    logInfo m!"CHECK {n} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} IMPLEMENTED_BY {impl} EXTERN {ext}"
    for dep in deps do
      logInfo m!"EDGE {n} {dep}"
      work := work.push dep
  logInfo m!"TOTAL_CLOSURE {seen.size}"
  for n in #[`ChanLevine.cycleTestBridge, `ChanLevine.canonicalTest,
      `ChanLevine.connectedFibres, `ChanLevine.ambientBridge] do
    let axs ← collectAxioms n
    logInfo m!"TARGET_AXIOMS {n} {axs}"
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Forbidden axiom {ax}"
#print ChanLevine.cycleTestBridge
#print ChanLevine.canonicalTest
#print ChanLevine.connectedFibres
#print ChanLevine.ambientBridge

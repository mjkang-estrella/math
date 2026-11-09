import SemFinal3
import Lean.Util.CollectAxioms
open Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
run_cmd do
  let env ← getEnv
  let locals := #[`Dynamics, `Reduction, `SourceSemantics, `SemCanonical, `SemWords,
    `SemPeriodic, `SemFinal, `SemRegression, `Sem3Coverage, `Sem3Obstruction,
    `Sem3Removal, `SemFinal2, `Sem4Bounded, `Sem4RotorSet, `Sem4Balance,
    `Sem4Residual, `SemFinal3]
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
    if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
    if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
    let impl := Lean.Compiler.getImplementedBy? env n
    let ext := isExtern env n
    logInfo m!"CHECK {n} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} IMPLEMENTED_BY {impl} EXTERN {ext}"
    if ci.isUnsafe || ci.isPartial || n.toString.endsWith "_unsafe_rec" then
      throwError "Forbidden closure property {n}"
    if let some idx := env.getModuleIdxFor? n then
      if locals.contains env.header.moduleNames[idx.toNat]! then
        if impl.isSome || ext then throwError "Forbidden local implementation {n}"
    for dep in deps do
      logInfo m!"EDGE {n} {dep}"
      work := work.push dep
  logInfo m!"TOTAL_CLOSURE {seen.size}"
  for n in #[`ChanLevine.Sem4.quota_terminal_exists, `ChanLevine.Sem4.no_empty_rotor_closed_set,
      `ChanLevine.Sem4.balanced_return, `ChanLevine.Sem4.cycleTestWord,
      `ChanLevine.Sem4.cycleTestBridge, `ChanLevine.Sem4.connectedFibres,
      `ChanLevine.Sem3.closedCoverage, `ChanLevine.Sem3.closedWordRecurrence,
      `ChanLevine.Sem3.closedWordCycleTest, `ChanLevine.Sem3.cycleTestBridge,
      `ChanLevine.Sem3.connectedFibres, `ChanLevine.Sem3.ambientBridge_unconditional] do
    let axs ← collectAxioms n
    logInfo m!"TARGET_AXIOMS {n} {axs}"
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Forbidden axiom {ax}"
#print ChanLevine.cycleTestBridge
#print ChanLevine.canonicalTest
#print ChanLevine.connectedFibres
#print ChanLevine.ambientBridge

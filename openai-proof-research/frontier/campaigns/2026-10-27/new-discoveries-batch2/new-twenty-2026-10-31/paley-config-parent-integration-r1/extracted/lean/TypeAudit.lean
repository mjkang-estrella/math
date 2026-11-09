import Yip355956
set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 100000000
set_option maxRecDepth 1000000
open Lean in
elab "#origin_audit" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Yip355956 | throwError "module absent"
  let mut names := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some ci := env.find? n | throwError "missing declaration"
    logInfo m!"ORIGIN {n} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
    if ci.isUnsafe || ci.isPartial || ci.isAxiom then throwError "disallowed local declaration"
    logInfo m!"FULL_TYPE {n}: {ci.type}"
    logInfo m!"BODY_PRESENT {n}: {ci.value?.isSome}"
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "forbidden axiom {ax}"
    Elab.Command.elabCommand (← `(#print axioms $(mkIdent n)))
  logInfo m!"ORIGIN_COUNT {names.size}"
#origin_audit

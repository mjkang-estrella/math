import V3Config355701
set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 100000000
set_option maxRecDepth 1000000
open Lean in
elab "#origin_audit" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `V3Config355701 | throwError "module absent"
  let mut names := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some ci := env.find? n | throwError "missing declaration"
    logInfo m!"ORIGIN {n} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
    Elab.Command.elabCommand (← `(#print $(mkIdent n)))
    Elab.Command.elabCommand (← `(#print axioms $(mkIdent n)))
  logInfo m!"ORIGIN_COUNT {names.size}"
#origin_audit

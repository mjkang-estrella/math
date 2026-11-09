import Endpoint
set_option warningAsError true
set_option pp.all true
set_option pp.proofs true
set_option pp.maxSteps 10000000
set_option pp.deepTerms true
set_option maxRecDepth 10000
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
  if [some `Defs, some `BoolProbe, some `Checker, some `Endpoint].contains origin then
   count := count + 1
   logInfo m!"DECL {n} ORIGIN {origin} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} BODY {(ci.value? true).isSome}"
   logInfo m!"FULL_TYPE {n}\n{ci.type}"
   if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial {n}"
   if ci matches .axiomInfo _ then throwError "new axiom {n}"
   unless (ci.value? true).isSome do throwError "missing body {n}"
   let axs ← Lean.collectAxioms n
   logInfo m!"TRANSITIVE_AXIOMS {n} {axs}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden axiom {n} {ax}"
   elabCommand (← `(command| #print axioms $(mkIdent n)))
 logInfo m!"TOTAL {count}"
 unless count == 66 do throwError "unexpected inventory {count}"

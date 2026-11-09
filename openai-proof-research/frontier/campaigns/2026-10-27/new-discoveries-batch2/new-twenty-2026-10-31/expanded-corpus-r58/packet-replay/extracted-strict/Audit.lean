import Endpoint
set_option warningAsError true
set_option pp.all true
set_option pp.proofs true
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  if [some `Defs, some `BoolProbe, some `Checker, some `Endpoint].contains ((env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)) then
   count := count + 1
   logInfo m!"MODULE {(env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)} LOCAL {n} TYPE {ci.type}"
   if let some val := ci.value? then logInfo m!"VALUE {n} {val}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "new axiom {n}"
   let axs ← Lean.collectAxioms n
   logInfo m!"TRANSITIVE_AXIOMS {n} {axs}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden axiom {n} {ax}"
   elabCommand (← `(command| #print axioms $(mkIdent n)))
 logInfo m!"LOCAL_TOTAL {count}"

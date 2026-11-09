import Supplement
set_option pp.all true
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  if origin == some `Supplement then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"DECL {n} ORIGIN {origin} TYPE {ci.type} AXIOMS {axs}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "custom axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {ax}"
 logInfo m!"AUDIT_TOTAL {count}"
 if count != 17 then throwError "unexpected count {count}"

import Latin
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  if origin == some `Latin then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"INDEPENDENT {n} ORIGIN {origin} TYPE {ci.type} AXIOMS {axs}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {ax}"
 logInfo m!"INDEPENDENT_TOTAL {count}"
 if count != 22 then throwError "unexpected count {count}"

import DPrime
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
 -- every constant recorded in the imported module data of `DPrime`
 let some idx := env.getModuleIdx? `DPrime | throwError "module DPrime not imported"
 let names := (env.header.moduleData[idx.toNat]!.constNames).qsort (fun a b => a.toString < b.toString)
 for n in names do
  let some ci := env.find? n | throwError "lost {n}"
  let origin := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
  unless origin == some `DPrime do throwError "origin mismatch {n}"
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
 logInfo m!"TOTAL {count}"

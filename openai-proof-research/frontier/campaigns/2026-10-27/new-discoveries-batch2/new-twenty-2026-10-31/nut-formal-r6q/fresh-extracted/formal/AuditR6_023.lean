import NewCertificates0274
import NewCertificates0275
import NewCertificates0276
import NewCertificates0277
import NewCertificates0278
import NewCertificates0279
import NewCertificates0280
import NewCertificates0281
import NewCertificates0282
import NewCertificates0283
import NewCertificates0284
import NewCertificates0285
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0274, `NewCertificates0275, `NewCertificates0276, `NewCertificates0277, `NewCertificates0278, `NewCertificates0279, `NewCertificates0280, `NewCertificates0281, `NewCertificates0282, `NewCertificates0283, `NewCertificates0284, `NewCertificates0285].contains m) then
      count := count + 1
      logInfo m!"MODULE {mod} DECL {n} TYPE {ci.type}"
      logInfo m!"BODY {n} {ci.value? (allowOpaque := true)}"
      logInfo m!"FLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
      if ci.isUnsafe || ci.isPartial || ci.isAxiom then throwError "forbidden declaration {n}"
      let axs ← Lean.collectAxioms n
      logInfo m!"AXIOMS {n} {axs}"
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "forbidden axiom {ax} in {n}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"LOCAL_TOTAL {count}"

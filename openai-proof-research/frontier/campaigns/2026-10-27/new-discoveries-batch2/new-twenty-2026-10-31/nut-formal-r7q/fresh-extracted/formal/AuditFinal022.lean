import NewCertificates0119
import NewCertificates0120
import NewCertificates0121
import NewCertificates0122
import NewCertificates0123
import NewCertificates0124
import NewCertificates0125
import NewCertificates0126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0119, `NewCertificates0120, `NewCertificates0121, `NewCertificates0122, `NewCertificates0123, `NewCertificates0124, `NewCertificates0125, `NewCertificates0126].contains m) then
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

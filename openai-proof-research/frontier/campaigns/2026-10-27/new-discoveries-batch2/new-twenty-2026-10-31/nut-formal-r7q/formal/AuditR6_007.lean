import NewCertificates0082
import NewCertificates0083
import NewCertificates0084
import NewCertificates0085
import NewCertificates0086
import NewCertificates0087
import NewCertificates0088
import NewCertificates0089
import NewCertificates0090
import NewCertificates0091
import NewCertificates0092
import NewCertificates0093
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0082, `NewCertificates0083, `NewCertificates0084, `NewCertificates0085, `NewCertificates0086, `NewCertificates0087, `NewCertificates0088, `NewCertificates0089, `NewCertificates0090, `NewCertificates0091, `NewCertificates0092, `NewCertificates0093].contains m) then
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

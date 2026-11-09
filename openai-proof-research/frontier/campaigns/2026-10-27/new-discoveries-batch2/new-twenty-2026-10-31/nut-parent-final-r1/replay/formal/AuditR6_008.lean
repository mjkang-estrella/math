import NewCertificates0094
import NewCertificates0095
import NewCertificates0096
import NewCertificates0097
import NewCertificates0098
import NewCertificates0099
import NewCertificates0100
import NewCertificates0101
import NewCertificates0102
import NewCertificates0103
import NewCertificates0104
import NewCertificates0105
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0094, `NewCertificates0095, `NewCertificates0096, `NewCertificates0097, `NewCertificates0098, `NewCertificates0099, `NewCertificates0100, `NewCertificates0101, `NewCertificates0102, `NewCertificates0103, `NewCertificates0104, `NewCertificates0105].contains m) then
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

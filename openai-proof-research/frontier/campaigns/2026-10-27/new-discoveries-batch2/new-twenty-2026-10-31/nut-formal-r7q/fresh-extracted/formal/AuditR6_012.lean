import NewCertificates0142
import NewCertificates0143
import NewCertificates0144
import NewCertificates0145
import NewCertificates0146
import NewCertificates0147
import NewCertificates0148
import NewCertificates0149
import NewCertificates0150
import NewCertificates0151
import NewCertificates0152
import NewCertificates0153
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0142, `NewCertificates0143, `NewCertificates0144, `NewCertificates0145, `NewCertificates0146, `NewCertificates0147, `NewCertificates0148, `NewCertificates0149, `NewCertificates0150, `NewCertificates0151, `NewCertificates0152, `NewCertificates0153].contains m) then
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

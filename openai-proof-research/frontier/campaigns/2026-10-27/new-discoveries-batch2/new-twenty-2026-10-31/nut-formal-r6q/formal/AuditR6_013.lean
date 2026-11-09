import NewCertificates0154
import NewCertificates0155
import NewCertificates0156
import NewCertificates0157
import NewCertificates0158
import NewCertificates0159
import NewCertificates0160
import NewCertificates0161
import NewCertificates0162
import NewCertificates0163
import NewCertificates0164
import NewCertificates0165
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0154, `NewCertificates0155, `NewCertificates0156, `NewCertificates0157, `NewCertificates0158, `NewCertificates0159, `NewCertificates0160, `NewCertificates0161, `NewCertificates0162, `NewCertificates0163, `NewCertificates0164, `NewCertificates0165].contains m) then
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

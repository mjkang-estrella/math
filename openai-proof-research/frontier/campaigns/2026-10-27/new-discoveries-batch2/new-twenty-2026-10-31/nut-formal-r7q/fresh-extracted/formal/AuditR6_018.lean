import NewCertificates0214
import NewCertificates0215
import NewCertificates0216
import NewCertificates0217
import NewCertificates0218
import NewCertificates0219
import NewCertificates0220
import NewCertificates0221
import NewCertificates0222
import NewCertificates0223
import NewCertificates0224
import NewCertificates0225
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0214, `NewCertificates0215, `NewCertificates0216, `NewCertificates0217, `NewCertificates0218, `NewCertificates0219, `NewCertificates0220, `NewCertificates0221, `NewCertificates0222, `NewCertificates0223, `NewCertificates0224, `NewCertificates0225].contains m) then
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

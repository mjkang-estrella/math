import NewCertificates0238
import NewCertificates0239
import NewCertificates0240
import NewCertificates0241
import NewCertificates0242
import NewCertificates0243
import NewCertificates0244
import NewCertificates0245
import NewCertificates0246
import NewCertificates0247
import NewCertificates0248
import NewCertificates0249
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0238, `NewCertificates0239, `NewCertificates0240, `NewCertificates0241, `NewCertificates0242, `NewCertificates0243, `NewCertificates0244, `NewCertificates0245, `NewCertificates0246, `NewCertificates0247, `NewCertificates0248, `NewCertificates0249].contains m) then
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

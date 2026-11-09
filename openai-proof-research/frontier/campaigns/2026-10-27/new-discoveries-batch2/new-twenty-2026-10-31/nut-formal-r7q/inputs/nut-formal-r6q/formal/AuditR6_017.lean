import NewCertificates0202
import NewCertificates0203
import NewCertificates0204
import NewCertificates0205
import NewCertificates0206
import NewCertificates0207
import NewCertificates0208
import NewCertificates0209
import NewCertificates0210
import NewCertificates0211
import NewCertificates0212
import NewCertificates0213
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0202, `NewCertificates0203, `NewCertificates0204, `NewCertificates0205, `NewCertificates0206, `NewCertificates0207, `NewCertificates0208, `NewCertificates0209, `NewCertificates0210, `NewCertificates0211, `NewCertificates0212, `NewCertificates0213].contains m) then
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

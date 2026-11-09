import NewCertificates0190
import NewCertificates0191
import NewCertificates0192
import NewCertificates0193
import NewCertificates0194
import NewCertificates0195
import NewCertificates0196
import NewCertificates0197
import NewCertificates0198
import NewCertificates0199
import NewCertificates0200
import NewCertificates0201
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0190, `NewCertificates0191, `NewCertificates0192, `NewCertificates0193, `NewCertificates0194, `NewCertificates0195, `NewCertificates0196, `NewCertificates0197, `NewCertificates0198, `NewCertificates0199, `NewCertificates0200, `NewCertificates0201].contains m) then
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

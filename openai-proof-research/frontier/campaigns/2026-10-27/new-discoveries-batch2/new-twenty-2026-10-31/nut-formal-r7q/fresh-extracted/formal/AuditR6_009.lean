import NewCertificates0106
import NewCertificates0107
import NewCertificates0108
import NewCertificates0109
import NewCertificates0110
import NewCertificates0111
import NewCertificates0112
import NewCertificates0113
import NewCertificates0114
import NewCertificates0115
import NewCertificates0116
import NewCertificates0117
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0106, `NewCertificates0107, `NewCertificates0108, `NewCertificates0109, `NewCertificates0110, `NewCertificates0111, `NewCertificates0112, `NewCertificates0113, `NewCertificates0114, `NewCertificates0115, `NewCertificates0116, `NewCertificates0117].contains m) then
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

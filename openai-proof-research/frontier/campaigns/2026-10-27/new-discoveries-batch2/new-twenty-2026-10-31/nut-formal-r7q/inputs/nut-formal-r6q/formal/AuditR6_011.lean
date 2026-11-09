import NewCertificates0130
import NewCertificates0131
import NewCertificates0132
import NewCertificates0133
import NewCertificates0134
import NewCertificates0135
import NewCertificates0136
import NewCertificates0137
import NewCertificates0138
import NewCertificates0139
import NewCertificates0140
import NewCertificates0141
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0130, `NewCertificates0131, `NewCertificates0132, `NewCertificates0133, `NewCertificates0134, `NewCertificates0135, `NewCertificates0136, `NewCertificates0137, `NewCertificates0138, `NewCertificates0139, `NewCertificates0140, `NewCertificates0141].contains m) then
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

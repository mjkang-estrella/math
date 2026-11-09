import NewCertificates0166
import NewCertificates0167
import NewCertificates0168
import NewCertificates0169
import NewCertificates0170
import NewCertificates0171
import NewCertificates0172
import NewCertificates0173
import NewCertificates0174
import NewCertificates0175
import NewCertificates0176
import NewCertificates0177
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0166, `NewCertificates0167, `NewCertificates0168, `NewCertificates0169, `NewCertificates0170, `NewCertificates0171, `NewCertificates0172, `NewCertificates0173, `NewCertificates0174, `NewCertificates0175, `NewCertificates0176, `NewCertificates0177].contains m) then
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

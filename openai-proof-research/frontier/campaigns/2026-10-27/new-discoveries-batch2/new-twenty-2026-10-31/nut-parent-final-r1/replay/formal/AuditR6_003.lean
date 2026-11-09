import NewCertificates0034
import NewCertificates0035
import NewCertificates0036
import NewCertificates0037
import NewCertificates0038
import NewCertificates0039
import NewCertificates0040
import NewCertificates0041
import NewCertificates0042
import NewCertificates0043
import NewCertificates0044
import NewCertificates0045
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0034, `NewCertificates0035, `NewCertificates0036, `NewCertificates0037, `NewCertificates0038, `NewCertificates0039, `NewCertificates0040, `NewCertificates0041, `NewCertificates0042, `NewCertificates0043, `NewCertificates0044, `NewCertificates0045].contains m) then
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

import NewCertificates0070
import NewCertificates0071
import NewCertificates0072
import NewCertificates0073
import NewCertificates0074
import NewCertificates0075
import NewCertificates0076
import NewCertificates0077
import NewCertificates0078
import NewCertificates0079
import NewCertificates0080
import NewCertificates0081
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0070, `NewCertificates0071, `NewCertificates0072, `NewCertificates0073, `NewCertificates0074, `NewCertificates0075, `NewCertificates0076, `NewCertificates0077, `NewCertificates0078, `NewCertificates0079, `NewCertificates0080, `NewCertificates0081].contains m) then
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

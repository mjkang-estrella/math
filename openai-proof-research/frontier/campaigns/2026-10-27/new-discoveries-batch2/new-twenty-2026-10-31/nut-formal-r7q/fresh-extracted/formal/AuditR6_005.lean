import NewCertificates0058
import NewCertificates0059
import NewCertificates0060
import NewCertificates0061
import NewCertificates0062
import NewCertificates0063
import NewCertificates0064
import NewCertificates0065
import NewCertificates0066
import NewCertificates0067
import NewCertificates0068
import NewCertificates0069
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0058, `NewCertificates0059, `NewCertificates0060, `NewCertificates0061, `NewCertificates0062, `NewCertificates0063, `NewCertificates0064, `NewCertificates0065, `NewCertificates0066, `NewCertificates0067, `NewCertificates0068, `NewCertificates0069].contains m) then
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

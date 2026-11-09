import NewCertificates0046
import NewCertificates0047
import NewCertificates0048
import NewCertificates0049
import NewCertificates0050
import NewCertificates0051
import NewCertificates0052
import NewCertificates0053
import NewCertificates0054
import NewCertificates0055
import NewCertificates0056
import NewCertificates0057
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0046, `NewCertificates0047, `NewCertificates0048, `NewCertificates0049, `NewCertificates0050, `NewCertificates0051, `NewCertificates0052, `NewCertificates0053, `NewCertificates0054, `NewCertificates0055, `NewCertificates0056, `NewCertificates0057].contains m) then
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

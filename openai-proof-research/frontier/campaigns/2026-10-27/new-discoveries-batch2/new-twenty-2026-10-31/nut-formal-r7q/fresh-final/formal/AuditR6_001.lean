import NewCertificates0010
import NewCertificates0011
import NewCertificates0012
import NewCertificates0013
import NewCertificates0014
import NewCertificates0015
import NewCertificates0016
import NewCertificates0017
import NewCertificates0018
import NewCertificates0019
import NewCertificates0020
import NewCertificates0021
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`NewCertificates0010, `NewCertificates0011, `NewCertificates0012, `NewCertificates0013, `NewCertificates0014, `NewCertificates0015, `NewCertificates0016, `NewCertificates0017, `NewCertificates0018, `NewCertificates0019, `NewCertificates0020, `NewCertificates0021].contains m) then
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

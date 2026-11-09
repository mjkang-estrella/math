import SignedEnumeration
import SignedCatalogue
import NewCertificates0000
import NewCertificates0001
import NewCertificates0002
import NewCertificates0003
import NewCertificates0004
import NewCertificates0005
import NewCertificates0006
import NewCertificates0007
import NewCertificates0008
import NewCertificates0009
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SignedEnumeration, `SignedCatalogue, `NewCertificates0000, `NewCertificates0001, `NewCertificates0002, `NewCertificates0003, `NewCertificates0004, `NewCertificates0005, `NewCertificates0006, `NewCertificates0007, `NewCertificates0008, `NewCertificates0009].contains m) then
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

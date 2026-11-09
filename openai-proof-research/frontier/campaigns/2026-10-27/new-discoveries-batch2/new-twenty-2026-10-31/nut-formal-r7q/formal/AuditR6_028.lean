import SignedSupport015_000
import FiniteSupport015
import SupportData016
import SignedSupport016_000
import SignedSupport016_001
import FiniteSupport016
import SupportData017
import SignedSupport017_000
import FiniteSupport017
import SupportData018
import SignedSupport018_000
import FiniteSupport018
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SignedSupport015_000, `FiniteSupport015, `SupportData016, `SignedSupport016_000, `SignedSupport016_001, `FiniteSupport016, `SupportData017, `SignedSupport017_000, `FiniteSupport017, `SupportData018, `SignedSupport018_000, `FiniteSupport018].contains m) then
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

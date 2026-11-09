import SignedSupport122_011
import FiniteSupport122
import SupportData123
import SignedSupport123_000
import SignedSupport123_001
import FiniteSupport123
import SupportData124
import SignedSupport124_000
import FiniteSupport124
import SupportData125
import SignedSupport125_000
import FiniteSupport125
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SignedSupport122_011, `FiniteSupport122, `SupportData123, `SignedSupport123_000, `SignedSupport123_001, `FiniteSupport123, `SupportData124, `SignedSupport124_000, `FiniteSupport124, `SupportData125, `SignedSupport125_000, `FiniteSupport125].contains m) then
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

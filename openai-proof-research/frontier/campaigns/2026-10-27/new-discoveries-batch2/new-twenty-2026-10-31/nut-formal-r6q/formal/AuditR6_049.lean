import SupportData092
import SignedSupport092_000
import FiniteSupport092
import SupportData093
import SignedSupport093_000
import FiniteSupport093
import SupportData094
import SignedSupport094_000
import SignedSupport094_001
import FiniteSupport094
import SupportData095
import SignedSupport095_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData092, `SignedSupport092_000, `FiniteSupport092, `SupportData093, `SignedSupport093_000, `FiniteSupport093, `SupportData094, `SignedSupport094_000, `SignedSupport094_001, `FiniteSupport094, `SupportData095, `SignedSupport095_000].contains m) then
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

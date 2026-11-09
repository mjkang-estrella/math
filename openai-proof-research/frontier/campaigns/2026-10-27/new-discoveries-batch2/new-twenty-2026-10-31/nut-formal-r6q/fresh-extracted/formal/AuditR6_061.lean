import SupportData130
import SignedSupport130_000
import FiniteSupport130
import SupportData131
import SignedSupport131_000
import FiniteSupport131
import SupportData132
import SignedSupport132_000
import FiniteSupport132
import SupportData133
import SignedSupport133_000
import FiniteSupport133
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData130, `SignedSupport130_000, `FiniteSupport130, `SupportData131, `SignedSupport131_000, `FiniteSupport131, `SupportData132, `SignedSupport132_000, `FiniteSupport132, `SupportData133, `SignedSupport133_000, `FiniteSupport133].contains m) then
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

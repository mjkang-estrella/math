import FiniteSupport038
import SupportData039
import SignedSupport039_000
import FiniteSupport039
import SupportData040
import SignedSupport040_000
import FiniteSupport040
import SupportData041
import SignedSupport041_000
import FiniteSupport041
import SupportData042
import SignedSupport042_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport038, `SupportData039, `SignedSupport039_000, `FiniteSupport039, `SupportData040, `SignedSupport040_000, `FiniteSupport040, `SupportData041, `SignedSupport041_000, `FiniteSupport041, `SupportData042, `SignedSupport042_000].contains m) then
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

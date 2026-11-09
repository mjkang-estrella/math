import FiniteSupport042
import SupportData043
import SignedSupport043_000
import FiniteSupport043
import SupportData044
import SignedSupport044_000
import FiniteSupport044
import SupportData045
import SignedSupport045_000
import FiniteSupport045
import SupportData046
import SignedSupport046_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport042, `SupportData043, `SignedSupport043_000, `FiniteSupport043, `SupportData044, `SignedSupport044_000, `FiniteSupport044, `SupportData045, `SignedSupport045_000, `FiniteSupport045, `SupportData046, `SignedSupport046_000].contains m) then
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

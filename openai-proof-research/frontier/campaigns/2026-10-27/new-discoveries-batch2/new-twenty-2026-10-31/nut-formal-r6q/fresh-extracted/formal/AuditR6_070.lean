import FiniteSupport161
import SupportData162
import SignedSupport162_000
import FiniteSupport162
import SupportData163
import SignedSupport163_000
import FiniteSupport163
import SupportData164
import SignedSupport164_000
import FiniteSupport164
import SupportData165
import SignedSupport165_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport161, `SupportData162, `SignedSupport162_000, `FiniteSupport162, `SupportData163, `SignedSupport163_000, `FiniteSupport163, `SupportData164, `SignedSupport164_000, `FiniteSupport164, `SupportData165, `SignedSupport165_000].contains m) then
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

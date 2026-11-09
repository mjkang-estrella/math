import FiniteSupport046
import SupportData047
import SignedSupport047_000
import FiniteSupport047
import SupportData048
import SignedSupport048_000
import FiniteSupport048
import SupportData049
import SignedSupport049_000
import FiniteSupport049
import SupportData050
import SignedSupport050_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport046, `SupportData047, `SignedSupport047_000, `FiniteSupport047, `SupportData048, `SignedSupport048_000, `FiniteSupport048, `SupportData049, `SignedSupport049_000, `FiniteSupport049, `SupportData050, `SignedSupport050_000].contains m) then
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

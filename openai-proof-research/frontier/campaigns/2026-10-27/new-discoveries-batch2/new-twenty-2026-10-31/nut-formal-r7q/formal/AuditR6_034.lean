import SupportData035
import SignedSupport035_000
import SignedSupport035_001
import FiniteSupport035
import SupportData036
import SignedSupport036_000
import FiniteSupport036
import SupportData037
import SignedSupport037_000
import FiniteSupport037
import SupportData038
import SignedSupport038_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData035, `SignedSupport035_000, `SignedSupport035_001, `FiniteSupport035, `SupportData036, `SignedSupport036_000, `FiniteSupport036, `SupportData037, `SignedSupport037_000, `FiniteSupport037, `SupportData038, `SignedSupport038_000].contains m) then
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

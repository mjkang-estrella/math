import FiniteSupport118
import SupportData119
import SignedSupport119_000
import SignedSupport119_001
import FiniteSupport119
import SupportData120
import SignedSupport120_000
import SignedSupport120_001
import FiniteSupport120
import SupportData121
import SignedSupport121_000
import FiniteSupport121
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport118, `SupportData119, `SignedSupport119_000, `SignedSupport119_001, `FiniteSupport119, `SupportData120, `SignedSupport120_000, `SignedSupport120_001, `FiniteSupport120, `SupportData121, `SignedSupport121_000, `FiniteSupport121].contains m) then
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

import SupportData110
import SignedSupport110_000
import SignedSupport110_001
import SignedSupport110_002
import SignedSupport110_003
import FiniteSupport110
import SupportData111
import SignedSupport111_000
import SignedSupport111_001
import SignedSupport111_002
import SignedSupport111_003
import FiniteSupport111
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData110, `SignedSupport110_000, `SignedSupport110_001, `SignedSupport110_002, `SignedSupport110_003, `FiniteSupport110, `SupportData111, `SignedSupport111_000, `SignedSupport111_001, `SignedSupport111_002, `SignedSupport111_003, `FiniteSupport111].contains m) then
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

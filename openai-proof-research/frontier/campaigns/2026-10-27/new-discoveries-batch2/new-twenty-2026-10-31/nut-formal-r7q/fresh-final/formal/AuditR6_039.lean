import FiniteSupport054
import SupportData055
import SignedSupport055_000
import SignedSupport055_001
import SignedSupport055_002
import SignedSupport055_003
import FiniteSupport055
import SupportData056
import SignedSupport056_000
import FiniteSupport056
import SupportData057
import SignedSupport057_000
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport054, `SupportData055, `SignedSupport055_000, `SignedSupport055_001, `SignedSupport055_002, `SignedSupport055_003, `FiniteSupport055, `SupportData056, `SignedSupport056_000, `FiniteSupport056, `SupportData057, `SignedSupport057_000].contains m) then
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

import FiniteSupport065
import SupportData066
import SignedSupport066_000
import FiniteSupport066
import SupportData067
import SignedSupport067_000
import SignedSupport067_001
import FiniteSupport067
import SupportData068
import SignedSupport068_000
import SignedSupport068_001
import FiniteSupport068
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport065, `SupportData066, `SignedSupport066_000, `FiniteSupport066, `SupportData067, `SignedSupport067_000, `SignedSupport067_001, `FiniteSupport067, `SupportData068, `SignedSupport068_000, `SignedSupport068_001, `FiniteSupport068].contains m) then
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

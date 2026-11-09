import SupportData126
import SignedSupport126_000
import FiniteSupport126
import SupportData127
import SignedSupport127_000
import FiniteSupport127
import SupportData128
import SignedSupport128_000
import FiniteSupport128
import SupportData129
import SignedSupport129_000
import FiniteSupport129
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData126, `SignedSupport126_000, `FiniteSupport126, `SupportData127, `SignedSupport127_000, `FiniteSupport127, `SupportData128, `SignedSupport128_000, `FiniteSupport128, `SupportData129, `SignedSupport129_000, `FiniteSupport129].contains m) then
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

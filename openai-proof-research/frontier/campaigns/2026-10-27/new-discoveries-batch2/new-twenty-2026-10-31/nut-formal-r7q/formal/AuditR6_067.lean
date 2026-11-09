import FiniteSupport151
import SupportData152
import SignedSupport152_000
import SignedSupport152_001
import FiniteSupport152
import SupportData153
import SignedSupport153_000
import SignedSupport153_001
import FiniteSupport153
import SupportData154
import SignedSupport154_000
import SignedSupport154_001
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport151, `SupportData152, `SignedSupport152_000, `SignedSupport152_001, `FiniteSupport152, `SupportData153, `SignedSupport153_000, `SignedSupport153_001, `FiniteSupport153, `SupportData154, `SignedSupport154_000, `SignedSupport154_001].contains m) then
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

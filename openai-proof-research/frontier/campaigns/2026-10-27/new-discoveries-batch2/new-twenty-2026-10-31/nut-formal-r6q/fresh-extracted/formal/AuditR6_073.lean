import SignedSupport173_001
import FiniteSupport173
import SupportData174
import SignedSupport174_000
import FiniteSupport174
import SupportData175
import SignedSupport175_000
import FiniteSupport175
import SupportData176
import SignedSupport176_000
import SignedSupport176_001
import FiniteSupport176
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SignedSupport173_001, `FiniteSupport173, `SupportData174, `SignedSupport174_000, `FiniteSupport174, `SupportData175, `SignedSupport175_000, `FiniteSupport175, `SupportData176, `SignedSupport176_000, `SignedSupport176_001, `FiniteSupport176].contains m) then
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

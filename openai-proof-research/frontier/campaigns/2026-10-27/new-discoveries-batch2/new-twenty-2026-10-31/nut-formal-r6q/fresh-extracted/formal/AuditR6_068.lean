import SignedSupport154_002
import FiniteSupport154
import SupportData155
import SignedSupport155_000
import FiniteSupport155
import SupportData156
import SignedSupport156_000
import FiniteSupport156
import SupportData157
import SignedSupport157_000
import SignedSupport157_001
import SignedSupport157_002
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SignedSupport154_002, `FiniteSupport154, `SupportData155, `SignedSupport155_000, `FiniteSupport155, `SupportData156, `SignedSupport156_000, `FiniteSupport156, `SupportData157, `SignedSupport157_000, `SignedSupport157_001, `SignedSupport157_002].contains m) then
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

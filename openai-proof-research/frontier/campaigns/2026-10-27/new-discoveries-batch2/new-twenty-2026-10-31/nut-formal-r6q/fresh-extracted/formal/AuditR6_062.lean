import SupportData134
import SignedSupport134_000
import FiniteSupport134
import SupportData135
import SignedSupport135_000
import FiniteSupport135
import SupportData136
import SignedSupport136_000
import FiniteSupport136
import SupportData137
import SignedSupport137_000
import FiniteSupport137
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData134, `SignedSupport134_000, `FiniteSupport134, `SupportData135, `SignedSupport135_000, `FiniteSupport135, `SupportData136, `SignedSupport136_000, `FiniteSupport136, `SupportData137, `SignedSupport137_000, `FiniteSupport137].contains m) then
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

import FiniteSupport107
import SupportData108
import SignedSupport108_000
import SignedSupport108_001
import SignedSupport108_002
import SignedSupport108_003
import FiniteSupport108
import SupportData109
import SignedSupport109_000
import SignedSupport109_001
import SignedSupport109_002
import FiniteSupport109
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`FiniteSupport107, `SupportData108, `SignedSupport108_000, `SignedSupport108_001, `SignedSupport108_002, `SignedSupport108_003, `FiniteSupport108, `SupportData109, `SignedSupport109_000, `SignedSupport109_001, `SignedSupport109_002, `FiniteSupport109].contains m) then
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

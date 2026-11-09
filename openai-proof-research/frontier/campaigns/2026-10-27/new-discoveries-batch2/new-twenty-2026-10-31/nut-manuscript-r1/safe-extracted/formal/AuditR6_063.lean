import SupportData138
import SignedSupport138_000
import FiniteSupport138
import SupportData139
import SignedSupport139_000
import FiniteSupport139
import SupportData140
import SignedSupport140_000
import FiniteSupport140
import SupportData141
import SignedSupport141_000
import FiniteSupport141
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`SupportData138, `SignedSupport138_000, `FiniteSupport138, `SupportData139, `SignedSupport139_000, `FiniteSupport139, `SupportData140, `SignedSupport140_000, `FiniteSupport140, `SupportData141, `SignedSupport141_000, `FiniteSupport141].contains m) then
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

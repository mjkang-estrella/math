import Candidate
import Lean.Elab.Command
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option pp.maxSteps 1000000
set_option pp.proofs true
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `Candidate then
      for name in env.header.moduleData[i]!.constNames do
        let ci := (env.find? name).get!
        logInfo m!"FULL_TYPE {name} : {ci.type}"
        if let some v := ci.value? true then
          logInfo m!"FULL_VALUE {name} := {v}"
        let axs ← collectAxioms name
        for ax in axs do
          unless allowed.contains ax do
            throwError "Forbidden dependency {name}: {ax}"
        if ci.isUnsafe || ci.isAxiom || ci.isPartial then
          throwError "Forbidden flag {name}"
        logInfo m!"AUDIT {name} AXIOMS {axs} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
        count := count + 1
  logInfo m!"AUDIT_TOTAL {count}"
#print MathDB352038.SourceConjecture
#print axioms MathDB352038.source_refutation

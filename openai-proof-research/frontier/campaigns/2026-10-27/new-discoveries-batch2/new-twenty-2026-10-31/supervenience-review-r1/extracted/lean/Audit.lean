import Hierarchy
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targetModule := env.getModuleIdxFor? `Supervenience.literal_conjecture_false
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == targetModule then
      count := count + 1
      let axs ← collectAxioms n
      logInfo m!"AUDIT {n}: unsafe={ci.isUnsafe}; axiom={ci.isAxiom}; axioms={axs.toList}"
      if ci.isUnsafe || ci.isAxiom then throwError "Disallowed local declaration {n}"
      for ax in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {n}"
  logInfo m!"AUDIT_COUNT {count}"
#print axioms Supervenience.literal_conjecture_false
#print Supervenience.HierarchyConjecture
#print Supervenience.StrictStep
#print Supervenience.eval
#print Supervenience.translate

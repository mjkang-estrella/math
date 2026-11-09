import Inventory
import Lean.Util.CollectAxioms

#print axioms MathDB356266.conjecture_false
#print axioms MathDB356266.conjectureLinear_false

open Lean Elab Command in
run_elab do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants.toList do
    if `MathDB356266 |>.isPrefixOf n then
      let axioms ← collectAxioms n
      for a in axioms do
        unless a == `propext || a == `Classical.choice || a == `Quot.sound do
          throwError "unapproved dependency {a} in {n}"
      count := count + 1
      logInfo m!"AXIOMS {n}: {axioms}"
  logInfo m!"AXIOM AUDIT PASSED: {count} declarations"

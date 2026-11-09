import SignedMass
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (n.toString.splitOn "MathDB368007").length > 1 then
      let axs ← collectAxioms n
      unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
        throwError m!"UNAPPROVED AXIOMS {n}: {axs}"
      logInfo m!"AXIOM_AUDIT {n}: {axs}"
#print axioms MathDB368007.source_refutation
#print axioms MathDB368007.euclidean_local_minimum

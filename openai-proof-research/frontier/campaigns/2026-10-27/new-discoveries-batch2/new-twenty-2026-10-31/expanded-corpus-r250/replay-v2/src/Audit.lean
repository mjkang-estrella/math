import Final
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
open Lean Elab Command
#print axioms CommonBasis332371.counterexample
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if (n.toString.splitOn "CommonBasis332371").length > 1 then
      count := count + 1
      if ci.isUnsafe || ci.isPartial ||
          (n.toString.splitOn "_unsafe_rec").length > 1 ||
          isExtern env n || (Compiler.getImplementedBy? env n).isSome then
        throwError "Forbidden declaration metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local axiom: {n}"
      | _ => pure ()
      let axs ← collectAxioms n
      for ax in axs do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden transitive axiom {ax} in {n}"
      logInfo m!"AUDITED {n}"
  logInfo m!"Local declaration metadata audit passed: {count} declarations"

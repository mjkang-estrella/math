import Lean
import Mobius
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Mobius).isPrefixOf name then
      total := total + 1
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
  logInfo m!"LOCAL DECLARATION COUNT {total}"

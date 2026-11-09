import Lean
open Lean Elab Command
-- Negative control: the same collectAxioms machinery must detect sorryAx.
theorem ctrlSad : 1 = 1 := by sorry
run_cmd do
  let axs ← collectAxioms ``ctrlSad
  unless axs.contains `sorryAx do throwError "control: expected sorryAx"
  logInfo m!"CONTROL sorryAx detection works: {axs}"

import Final
import Lean

/-!
# Negative control for the r3 supplement closure check

A genuinely `sorry`ed lemma MUST be reported as carrying `sorryAx` by the same
`collectAxioms`-based closure check used in `Supplement.lean`. This is a control module,
not corpus: its `sorry` is intentional and its build runs without `-DwarningAsError`
(the warning is the expected signal).
-/

open Lean Elab Command

theorem supCtrlSorry : True := by sorry

run_cmd do
  let axs ← collectAxioms `supCtrlSorry
  logInfo m!"SUPCTRL closure of control theorem supCtrlSorry: {axs}"
  unless axs.contains `sorryAx do
    throwError "SUPCTRL-FAIL sorryAx not detected by closure check"
  logInfo "SUPCTRL-PASS sorryAx detection works"

import CanonicalCoverage
import Lean
set_option autoImplicit false
set_option linter.auxLemma false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Diagonal, `Spans, `Placement, `Symmetry, `SignedNormalization, `CanonicalCoverage]
  for i in [:env.header.moduleNames.size] do
    if mods.contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        logInfo m!"CHECK_NAME {n}"
        let id := mkIdent n
        elabCommand (← `(command| #check $id))
        elabCommand (← `(command| #print axioms $id))

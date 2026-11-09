import Completed
import Large16
import Lean
set_option autoImplicit false
set_option linter.auxLemma false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Diagonal, `Spans, `Placement, `Symmetry, `SignedNormalization, `CanonicalCoverage, `Potential, `Bridge, `FiniteBridge, `SmallData, `SmallGeometry, `SmallBase, `SmallEdge, `SmallMerge, `SmallFull, `SmallCase, `Empty00, `Empty01, `Empty02, `Empty03, `Empty04, `Empty05, `Empty06, `Empty07, `Empty08, `Empty09, `Empty10, `Empty11, `Empty12, `Empty13, `Empty14, `Empty15, `Empty16, `Empty17, `Empty18, `Empty19, `Empty20, `Empty21, `Empty22, `Empty23, `Empty24, `Empty25, `Empty26, `Empty27, `Empty28, `Empty29, `Empty30, `Empty31, `Empty32, `Empty33, `Empty34, `Forced730, `Completed, `Large16]
  for i in [:env.header.moduleNames.size] do
    if mods.contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        logInfo m!"CHECK_NAME {n}"
        let id := mkIdent n
        elabCommand (← `(command| #check $id))
        elabCommand (← `(command| #print axioms $id))

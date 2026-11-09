import Refutation
import Charges
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option linter.auxLemma false
set_option pp.privateNames true
#print EdgeIrregulator.SourceClaim
#print EdgeIrregulator.MinimumSourceClaim
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #[`Source, `Boundary, `Gadget, `Edges, `Degrees, `Local, `Lower, `Transport, `Refutation, `Charges]
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if mods.contains env.header.moduleNames[idx.toNat]! then
        elabCommand (← `(command| #check $(mkIdent name)))
        elabCommand (← `(command| #print axioms $(mkIdent name)))

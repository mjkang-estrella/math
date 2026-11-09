import Geometry
import InstanceG
import InstanceH
import Lean
set_option pp.privateNames true
open Lean Elab Command in
elab "#audit_all" : command => do
 let env ← getEnv
 for (name, _) in env.constants do
  if let some idx := env.getModuleIdxFor? name then
   if env.header.moduleNames[idx.toNat]! ∈ [`Literal, `InstanceG, `InstanceH, `Geometry] then
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
#audit_all

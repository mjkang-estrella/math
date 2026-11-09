import Geometry
import Lean
set_option pp.privateNames true
open Lean Elab Command in
elab "#audit_all" : command => do
 let env ← getEnv
 for h : idx in [:env.header.moduleNames.size] do
   if env.header.moduleNames[idx] == `Geometry then
     for name in env.header.moduleData[idx]!.constNames do
       elabCommand (← `(command| #check $(mkIdent name)))
       elabCommand (← `(command| #print axioms $(mkIdent name)))

#audit_all

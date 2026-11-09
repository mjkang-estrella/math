import SignedNormalization
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for i in [:env.header.moduleNames.size] do
  if env.header.moduleNames[i]! == `Growth then
   for n in env.header.moduleData[i]!.constNames do
    if n.toString.startsWith "_private" then
     let id := mkIdent n
     elabCommand (← `(command| #check $id))
     elabCommand (← `(command| #print axioms $id))

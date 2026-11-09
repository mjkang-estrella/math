import Endpoint
open Lean Elab Command
elab "#localNames" : command => do
 for (name, _) in (← getEnv).constants.toList do
  if "R162" ∈ name.toString.splitOn "." then
   logInfo m!"{name}"
#localNames

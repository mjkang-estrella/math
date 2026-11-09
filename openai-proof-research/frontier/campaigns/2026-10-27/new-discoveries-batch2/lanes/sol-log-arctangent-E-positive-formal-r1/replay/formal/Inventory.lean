import MeanEPositive
import FiniteAbel
set_option autoImplicit false
set_option warningAsError true
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (`LogArctangentMean).isPrefixOf name then
      logInfo m!"DECL {name}"

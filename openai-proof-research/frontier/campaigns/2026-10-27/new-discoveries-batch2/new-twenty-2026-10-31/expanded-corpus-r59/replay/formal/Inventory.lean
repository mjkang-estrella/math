import Signed
open Lean Elab Command in
run_elab do
  for (n, _) in (← getEnv).constants.toList do
    if `MathDB364205 |>.isPrefixOf n then
      logInfo m!"LOCAL {n}"

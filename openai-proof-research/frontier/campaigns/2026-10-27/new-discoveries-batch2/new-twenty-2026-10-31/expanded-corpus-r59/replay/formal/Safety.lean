import Signed
open Lean Elab Command in
run_elab do
  for (n, c) in (← getEnv).constants.toList do
    if `MathDB364205 |>.isPrefixOf n then
      if c.isUnsafe then throwError "unsafe declaration: {n}"
      if c.isPartial then throwError "partial declaration: {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom: {n}"
      | _ => pure ()
      logInfo m!"SAFE {n}"

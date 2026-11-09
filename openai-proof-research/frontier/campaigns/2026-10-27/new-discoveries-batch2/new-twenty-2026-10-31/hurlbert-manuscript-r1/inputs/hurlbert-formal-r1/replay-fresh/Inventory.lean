import Control
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, c) in env.constants.toList do
    if `MathDB356266 |>.isPrefixOf n then
      if c.isUnsafe then throwError "unsafe declaration: {n}"
      if c.isPartial then throwError "partial declaration: {n}"
      if (Compiler.getImplementedBy? env n).isSome then throwError "implementation override: {n}"
      if isExtern env n then throwError "external declaration: {n}"
      if (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "unsafe recursion declaration: {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom: {n}"
      | _ => pure ()
      count := count + 1
      logInfo m!"LOCAL {n}"
  logInfo m!"AUDITED {count} declarations"

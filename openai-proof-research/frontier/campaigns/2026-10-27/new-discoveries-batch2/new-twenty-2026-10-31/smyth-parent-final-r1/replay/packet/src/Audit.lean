import Endpoint
import Controls
#print axioms Smyth1512.not_conjecture15
#print axioms Smyth1512.nonvacuity
#print axioms Smyth1512.nonempty_control
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if (`Smyth1512).isPrefixOf c then
      n := n + 1
      if ci.isUnsafe || ci.isPartial then bad := bad.push c
      if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
      if Lean.isExtern env c then bad := bad.push c
      if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
      if let .axiomInfo _ := ci then bad := bad.push c
  if !bad.isEmpty then throwError "Forbidden declaration metadata: {bad}"
  logInfo m!"META local={n} flagged={bad}"

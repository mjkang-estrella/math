import ConferenceMDS324342
import Controls
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if (`ConferenceMDS).isPrefixOf c then
      n := n + 1
      let unsafeOrPartial : Bool := ci.isUnsafe || ci.isPartial
      if unsafeOrPartial then bad := bad.push c
      if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
      if Lean.isExtern env c then bad := bad.push c
      if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
  logInfo m!"ROOT_META local={n} flagged={bad}"
#print axioms ConferenceMDS.conjecture5_false
#check @ConferenceMDS.conjecture5_false

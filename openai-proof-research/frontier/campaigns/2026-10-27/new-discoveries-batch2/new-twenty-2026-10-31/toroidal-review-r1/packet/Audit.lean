import Witness
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if (`Toroidal).isPrefixOf c then
      n := n + 1
      logInfo m!"LOCAL {c}"
      let axs ← Lean.collectAxioms c
      logInfo m!"AXIOMS {c} {axs}"
      for ax in axs do
        if ax != `propext && ax != `Classical.choice && ax != `Quot.sound then bad := bad.push c
      if ci.isUnsafe || ci.isPartial then bad := bad.push c
      if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
      if Lean.isExtern env c then bad := bad.push c
      if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
      if let .axiomInfo _ := ci then bad := bad.push c
  if !bad.isEmpty then throwError "Forbidden declaration metadata: {bad}"
  logInfo m!"META local={n} flagged={bad}"
#print axioms Toroidal.mathdb_369421
#print Toroidal.Conjecture1
#print Toroidal.representationNumber
#print Toroidal.Represents
#print Toroidal.Alternates
#print Toroidal.Adj

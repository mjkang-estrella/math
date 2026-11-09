import SSA5.Endpoint

/-! Axiom audit of the endpoints and of every declaration defined in the `SSA5` modules. -/

#print axioms SSA.conjecture1_false_m5
#print axioms SSA.conjecture1_false_limsup
#print axioms SSA.conjecture1_false_liminf
#print axioms SSA.rate_limit_gap
#print axioms SSA.rate_gap

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`SSA5).isPrefixOf mod then
        count := count + 1
        let axs ← liftCoreM (Lean.collectAxioms name)
        for a in axs do
          unless allowed.contains a do bad := bad.push (name, a)
  logInfo m!"SSA5 audit: {count} declarations checked; disallowed axiom uses: {bad.size} {bad}"

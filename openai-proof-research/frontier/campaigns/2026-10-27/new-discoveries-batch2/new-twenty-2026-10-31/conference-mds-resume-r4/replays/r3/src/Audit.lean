import ConferenceMDS324342
open Lean Elab Command

/-- Print the axioms of every declaration defined in module `ConferenceMDS324342`. -/
elab "#audit_module_axioms" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `ConferenceMDS324342 | throwError "module not found"
  let names := (env.header.moduleData[idx.toNat]!).constNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Nat := 0
  for n in names.qsort (fun a b => a.toString < b.toString) do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let extra := axs.filter (fun a => !allowed.contains a)
    if !extra.isEmpty then bad := bad + 1
    logInfo m!"AXIOMS {n} : {axs.toList}"
  logInfo m!"AUDIT declarations={names.size} disallowed={bad}"

#audit_module_axioms
#print axioms ConferenceMDS.conjecture5_false
#print axioms ConferenceMDS.counterexample
#print axioms ConferenceMDS.conjecture5Std_false
#print axioms ConferenceMDS.mds_claim_false
#print axioms ConferenceMDS.distance_claim_false
#print axioms ConferenceMDS.latticeCode_eq_rowCode
#check @ConferenceMDS.conjecture5_false
#print ConferenceMDS.Conjecture5
#print ConferenceMDS.IsMDS
#print ConferenceMDS.minDistance
#print ConferenceMDS.rowCode
#print ConferenceMDS.IsConferenceMatrix
#print ConferenceMDS.IsWeighingMatrix

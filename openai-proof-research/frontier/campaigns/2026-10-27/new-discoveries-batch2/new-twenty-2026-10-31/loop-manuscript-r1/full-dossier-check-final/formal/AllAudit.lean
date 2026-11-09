import ReviewAudit
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for target in [`Loop, `ReviewAudit] do
  let mut total : Nat := 0
  for (n,c) in env.constants.toList do
   if let some i := env.getModuleIdxFor? n then
    if env.header.moduleNames[i.toNat]! == target then
     total := total + 1
     if c.isUnsafe then throwError "Unsafe declaration: {n}"
     match c with
     | .axiomInfo _ => throwError "Local axiom: {n}"
     | _ => pure ()
     let ax ← Lean.collectAxioms n
     for a in ax do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
       throwError "Forbidden axiom {a} in {n}"
     logInfo m!"DECL {target} {n} unsafe={c.isUnsafe} axioms={ax.toList} TYPE {c.type}"
  if target == `Loop && total != 28 then throwError "Unexpected Loop count: {total}"
  logInfo m!"TOTAL {target} {total}"
#print axioms Loop380362.source_refutation
#print axioms unpointed_inequivalence

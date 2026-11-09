import AuditR5
import Lean.Util.CollectAxioms
open Lean
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx.toNat]! == `AuditR5 then
        count := count + 1
        let axs ← collectAxioms n
        logInfo m!"AUDITOR_DECL {n} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} AXIOMS {axs}"
        if ci.isUnsafe || ci.isPartial then throwError "Forbidden auditor safety flag: {n}"
        for ax in axs do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "Forbidden auditor axiom: {ax}"
  if count == 0 then throwError "No auditor declarations found"
  logInfo m!"AUDITOR_DECLARATIONS {count}"
#print axioms AuditR5.encode

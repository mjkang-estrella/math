import Reviewer
import Quadratic
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Definitions, `Certificates, `Gram, `Independence, `Deletion0, `Deletion1, `Deletion2, `Deletion3, `Deletion4, `Deletion5, `Bridges, `Quadratic, `Main, `Reviewer]
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if modules.contains m then
        count := count + 1
        let axioms ← collectAxioms n
        if c.isUnsafe || c.isPartial then throwError "unsafe/partial declaration {n}"
        for a in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "forbidden axiom {a} in {n}"
        logInfo m!"AUDIT {n}\nMODULE {m}\nTYPE {repr c.type}\nBODY {repr (c.value? true)}\nUNSAFE {c.isUnsafe}\nPARTIAL {c.isPartial}\nAXIOMS {axioms}"
  logInfo m!"AUDIT_COUNT {count}"

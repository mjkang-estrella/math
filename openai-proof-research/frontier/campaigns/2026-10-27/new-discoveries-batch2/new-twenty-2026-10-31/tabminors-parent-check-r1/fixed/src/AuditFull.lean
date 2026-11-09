import TabMinors
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if m.toString == "TabMinors" then
      count := count + 1
      let ax ← Lean.collectAxioms n
      let hasBody := (c.value? (allowOpaque := true)).isSome
      logInfo m!"DECL|{n}|UNSAFE|{c.isUnsafe}|PARTIAL|{c.isPartial}|BODY|{hasBody}|AXIOMS|{ax.toList}"
      if c.isUnsafe || c.isPartial then throwError "bad safety {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom {n}"
      | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => pure ()
      | _ => if !hasBody then throwError "missing body {n}"
      for x in ax do
        if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains x then
          throwError "disallowed axiom {x} in {n}"
  logInfo m!"AUDITED_LOCAL_DECLARATIONS|{count}"

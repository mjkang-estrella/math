import Control
import Lean.Elab.Command
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
#print axioms IR350452.conjecture_false
#print axioms IR350452.nonvacuity
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? name with
      | some idx => #[`General, `GData, `Four, `Three, `Finite, `Endpoint, `Control].contains
          env.header.moduleNames[idx]!
      | none => false
    if localModule then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || name.toString.endsWith "_unsafe_rec" ||
          (Lean.Compiler.getImplementedBy? env name).isSome ||
          (Lean.externAttr.getParam? env name).isSome then
        throwError "Forbidden local declaration: {name}"
      match ci with
      | .axiomInfo _ => throwError "Local axiom: {name}"
      | _ => pure ()
      logInfo m!"AUDITED {name}"
  logInfo m!"Audited {count} local declarations"

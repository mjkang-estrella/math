import RealBridge
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (["Basic", "Certificates", "Graph", "RealBridge"] : List String).contains m.toString then
      count := count + 1
      let ax ← Lean.collectAxioms n
      logInfo m!"DECL|{n}|MODULE|{m}|UNSAFE|{c.isUnsafe}|PARTIAL|{c.isPartial}|AXIOMS|{ax.toList}"
      logInfo m!"FULL_TYPE_AST|{repr c.type}"
      logInfo m!"FULL_BODY_AST_value?_true|{repr (c.value? true)}"
      if c.isUnsafe || c.isPartial then throwError "bad safety {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom {n}"
      | _ => pure ()
      match c with
      | .inductInfo _ => logInfo m!"KERNEL_DECL_KIND|inductive|{n}"
      | .ctorInfo _ => logInfo m!"KERNEL_DECL_KIND|constructor|{n}"
      | .recInfo _ => logInfo m!"KERNEL_DECL_KIND|recursor|{n}"
      | _ => if !(c.value? true).isSome then throwError "missing body {n}"
      for x in ax do
        if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains x then
          throwError "disallowed axiom {x} in {n}"
  logInfo m!"AUDITED_LOCAL_DECLARATIONS|{count}"

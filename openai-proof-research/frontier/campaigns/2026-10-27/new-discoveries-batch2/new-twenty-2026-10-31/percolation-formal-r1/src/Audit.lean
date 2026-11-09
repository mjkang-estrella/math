import Endpoint
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let localModules : Array String := #["Definitions","Plane5","ControlBase","Sep4_2","Sep4_6","Sep4_8","Sep4_11","Sep4_12","Sep4_16","Sep4_18","Sep4_20","Sep4_21","Sep4_26","Sep5_0","Sep5_3","Sep5_4","Sep5_6","Sep5_7","Sep5_9","Sep5_10","Sep5_12","Sep5_13","Sep5_17","Sep5_18","Sep5_21","Sep5_22","Sep5_25","Sep5_26","Sep5_27","Control4","Control5","Structure","Endpoint","Audit"]
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "Audit"
    if localModules.contains owner then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local declaration metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption declaration: {n}"
      | _ => pure ()
  logInfo m!"Local declaration metadata audit passed: {count} declarations"

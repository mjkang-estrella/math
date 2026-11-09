import ReplayEndpoint
import Pilot500
import PG5CNF
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let localModules : Array String := #["Definitions","Plane5","ControlBase","Sep4_2","Sep4_6","Sep4_8","Sep4_11","Sep4_12","Sep4_16","Sep4_18","Sep4_20","Sep4_21","Sep4_26","Sep5_0","Sep5_3","Sep5_4","Sep5_6","Sep5_7","Sep5_9","Sep5_10","Sep5_12","Sep5_13","Sep5_17","Sep5_18","Sep5_21","Sep5_22","Sep5_25","Sep5_26","Sep5_27","Control4","Control5","Structure","Endpoint","Closure","FiniteSystem","TruthTableCNF","PG5CNF","Audit","RUP","InputLink","Inputs000","Inputs001","Inputs002","Inputs003","Inputs004","Inputs005","Inputs006","Inputs007","Inputs008","Inputs009","Inputs010","Inputs011","Inputs012","Inputs013","Inputs014","Inputs015","Inputs016","Inputs017","Inputs018","Inputs019","Inputs020","Inputs021","Inputs022","Inputs023","Inputs024","Inputs025","Inputs026","Inputs027","Inputs028","Inputs029","Inputs030","Inputs031","Inputs032","Inputs033","Inputs034","Inputs035","Inputs036","Inputs037","Inputs038","Inputs039","Inputs040","Inputs041","Inputs042","Inputs043","Inputs044","Inputs045","Inputs046","Inputs047","Pilot500","Pilot2000","ReplayEndpoint","AuditR3"]
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "AuditR3"
    if localModules.contains owner then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local declaration metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption declaration: {n}"
      | _ => pure ()
  logInfo m!"Local declaration metadata audit passed: {count} declarations"

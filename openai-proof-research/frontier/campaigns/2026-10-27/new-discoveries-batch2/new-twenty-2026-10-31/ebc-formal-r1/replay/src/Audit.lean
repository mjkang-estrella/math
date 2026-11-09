import Endpoint
import BFSCertificate
import Lean.Compiler.ImplementedByAttr
open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if (name.toString.splitOn "EBC337062").length > 1 then
      count := count + 1
      let replacement := (Lean.Compiler.getImplementedBy? env name).isSome
      let foreign := Lean.isExtern env name
      let helper := (name.toString.splitOn "_unsafe_rec").length > 1
      if ci.isUnsafe || ci.isPartial || replacement || foreign || helper then
        throwError "Rejected local declaration {name}"
      match ci with
      | .axiomInfo _ => throwError "Rejected local postulate {name}"
      | _ => pure ()
      logInfo m!"AUDIT {name}: safe, total, kernel definition or theorem"
  logInfo m!"AUDIT PASS: {count} local declarations"
#print axioms EBC337062.conjecture21_false
#print axioms EBC337062.shortestPaths_eq
#print axioms EBC337062.control_uniform

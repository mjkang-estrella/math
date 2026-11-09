import Certificates
open Lean Elab Command
#print axioms SlowNim360653.conjecture1_false
#print axioms SlowNim360653.two_every_profile_nash
#print axioms SlowNim360653.literal_bridge
#print axioms SlowNim360653.run_independent
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if (name.toString.splitOn "SlowNim360653").length > 1 then
      if ci.isUnsafe || ci.isPartial || (name.toString.splitOn "_unsafe_rec").length > 1 ||
          (Compiler.implementedByAttr.getParam? env name).isSome || (externAttr.getParam? env name).isSome then
        throwError "Forbidden metadata: {name}"
      match ci with
      | .axiomInfo _ => throwError "Local axiom: {name}"
      | _ => pure ()
      count := count + 1
      logInfo m!"AUDITED {name}"
  logInfo m!"Local metadata audit passed: {count} declarations"

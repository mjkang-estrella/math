import SignedMass
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (n.toString.splitOn "MathDB368007").length > 1 then
      logInfo m!"LOCAL_DECL {n}"

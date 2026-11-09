import TorusPMD
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (`TorusPMD).isPrefixOf n then
      logInfo m!"LOCAL_DECL {n}"

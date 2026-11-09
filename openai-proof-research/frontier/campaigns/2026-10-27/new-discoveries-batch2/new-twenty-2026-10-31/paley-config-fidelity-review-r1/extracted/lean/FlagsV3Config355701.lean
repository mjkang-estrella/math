import V3Config355701
open Lean in
elab "#flags" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `V3Config355701 | throwError "missing module"
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      logInfo m!"FLAG {n} unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
      count := count + 1
  logInfo m!"FLAG_COUNT {count}"
#flags

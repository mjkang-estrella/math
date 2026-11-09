import Certificate
run_cmd do
 let env ← Lean.getEnv
 for (n, _) in env.constants.toList do
  if n.toString.startsWith "Separation." then
   Lean.logInfo m!"{n}"

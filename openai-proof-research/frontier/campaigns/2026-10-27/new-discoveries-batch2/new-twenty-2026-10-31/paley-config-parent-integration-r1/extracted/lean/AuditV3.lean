import V3Config355701
open Lean in
elab "#audit_ns" : command => do
  let env ← getEnv
  let mut names := #[]
  for (n, _) in env.constants.toList do
    if (`MathDB355701).isPrefixOf n then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    Elab.Command.elabCommand (← `(#print axioms $(mkIdent n)))
  logInfo m!"audited {names.size} declarations"
#audit_ns
#print axioms MathDB355701.conjectureInclusion_false
#print axioms MathDB355701.conjectureMaximum_false
#print MathDB355701.ConjectureInclusion
#print MathDB355701.ConjectureMaximum
#print MathDB355701.IsSymV3Config
#print MathDB355701.MinMonoNonzero
#print MathDB355701.IsTriangle
#print MathDB355701.MutuallyIntersecting
#print MathDB355701.MaximalMutuallyIntersecting

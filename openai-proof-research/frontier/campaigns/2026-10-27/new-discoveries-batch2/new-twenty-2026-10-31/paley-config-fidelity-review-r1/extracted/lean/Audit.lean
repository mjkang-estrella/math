import Yip355956
open Lean in
/-- Print axioms of every declaration in namespace MathDB355956 (incl. auxiliary/generated ones). -/
elab "#audit_ns" : command => do
  let env ← getEnv
  let mut names := #[]
  for (n, _) in env.constants.toList do
    if (`MathDB355956).isPrefixOf n then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    Elab.Command.elabCommand (← `(#print axioms $(mkIdent n)))
  logInfo m!"audited {names.size} declarations"
#audit_ns
#print axioms MathDB355956.yip_conjecture_false
#print axioms MathDB355956.not_maximal_of_card
#print MathDB355956.YipConjecture
#print MathDB355956.IsMaximalGPClique
#print MathDB355956.IsGPClique
#print MathDB355956.GPAdj
#print MathDB355956.dPowers
#print MathDB355956.subfieldSet
#print MathDB355956.admissibleR
#print axioms MathDB355956.yip_conjecture_SG_false

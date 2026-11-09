import Certificate
import Lean.Util.CollectAxioms
run_cmd do
 let env ← Lean.getEnv
 let mut count : Nat := 0
 for (n, _) in env.constants.toList do
  if n.toString.startsWith "Separation." then
   let axioms ← Lean.collectAxioms n
   for a in axioms do
    unless a == `propext || a == `Classical.choice || a == `Quot.sound do
     throwError "Forbidden axiom {a} in {n}"
   Lean.logInfo m!"{n}: {axioms}"
   count := count + 1
 Lean.logInfo m!"Audited {count} local declarations, including generated ones"

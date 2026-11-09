import Semantics
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if (`Rainbow).isPrefixOf n then
      let ax ← collectAxioms n
      unless ax.all (fun a => allowed.contains a) do
        throwError "Disallowed axioms for {n}: {ax}"
      logInfo m!"AUDIT {n}: {ax}"
      count := count + 1
  logInfo m!"AUDITED_LOCAL_DECLARATIONS {count}"
#print axioms Rainbow.mathdb_346167_literal
#print axioms Rainbow.counterexample
#print axioms Rainbow.rvd_isLeast
#check Rainbow.mathdb_346167_literal

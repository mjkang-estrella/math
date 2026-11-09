import Taylor
-- Generated constants are intentionally named for the complete axiom audit.
set_option linter.auxLemma false
open Lean in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (`MathDB358323).isPrefixOf n then
      logInfo m!"LOCAL {n} AXIOMS {← Lean.collectAxioms n}"

#print axioms MathDB358323.F
#print axioms MathDB358323.Generated
#print axioms MathDB358323.HasZeroSetLimit
#print axioms MathDB358323.Lower
#print axioms MathDB358323.P
#print axioms MathDB358323.P.eq_1
#print axioms MathDB358323.Upper
#print axioms MathDB358323.base
#print axioms MathDB358323.exact_mathdb_negation
#print axioms MathDB358323.generated_witness
#print axioms MathDB358323.generating
#print axioms MathDB358323.literal_counterexample
#print axioms MathDB358323.minimal_root
#print axioms MathDB358323.nonzero_t₁
#print axioms MathDB358323.origin_upper
#print axioms MathDB358323.origin_upper._proof_1_1
#print axioms MathDB358323.period
#print axioms MathDB358323.period._proof_1_1
#print axioms MathDB358323.period._proof_1_2
#print axioms MathDB358323.recur
#print axioms MathDB358323.recur._proof_1_1
#print axioms MathDB358323.recurring
#print axioms MathDB358323.recurring._proof_1_1
#print axioms MathDB358323.root_norm
#print axioms MathDB358323.root_t₁
#print axioms MathDB358323.source_refutation
#print axioms MathDB358323.t₁
#print axioms MathDB358323.t₁._proof_1
#print axioms MathDB358323.t₁._proof_2
#print axioms MathDB358323.t₁.eq_1
#print axioms MathDB358323.zero_identity

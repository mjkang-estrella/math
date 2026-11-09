/-
# AuditFinal — axiom audit and statement check of the final assembly

Prints the literal type of the endpoint, its full declaration, and the transitive axiom
dependencies of the literal endpoint and every main new theorem, plus the two supplied
endpoint theorems it consumes.
-/
import BunFinalModel

#check Bun.bunkbed_E7_transitive
#print Bun.bunkbed_E7_transitive

#print axioms Bun.window_factor
#print axioms Bun.bunkbed_E7_transitive
#print axioms Bun.card_pairLt
#print axioms Bun.card_htoken
#print axioms Bun.card_token
#print axioms Bun.card_out
#print axioms Bun.prob_layer_true_le_false
#print axioms Bun.state_endpoint
#print axioms Bun.stf_reach_endpoint
#print axioms Bun.reach_of_lt

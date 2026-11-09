/-
# BunFinalProbe — development-time availability probe (scratch, not a proof module)

First attempt (`probe1`) deliberately failed: it asked for `Nat.even_mul_pred_self`,
`div_le_div_right` and `Nat.cast_le` under the wrong imports, and its true exit 1 is kept
in `probe1.receipt.json`.  This version only checks that the final assembly's public
statements exist; it adds no mathematics of its own.
-/
import BunFinalModel

#check Bun.window_factor
#check Bun.bunkbed_E7_transitive
#check Bun.card_token
#check Bun.card_out
#check Bun.prob_layer_true_le_false

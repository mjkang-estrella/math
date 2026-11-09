/-
INDEPENDENT expected-FAILURE audit controls (r6).  AUDIT-ONLY.
Every `example` below is FALSE; each is compiled to a true, expected,
informative failure exit.  The residual goals expose the true values,
so a proxy/encoding/convention error in the production certificate
would surface here as a different diagnostic.

Expected diagnostics (true values): 9, 10 vs 9, 4 > 1, 6, 4 vs 3, 0.
-/
import FlatBalanceBridges

namespace FlatBalance.IndNegControl

/-- N1. The 2-clique count is 9, not 8 (proxy-count detector). -/
example : cliqueCount K33 2 = 8 := by
  rw [cliqueCount_K33_two]

/-- N2. Convention separation is real: 10 ≠ 9. -/
example : evenCliqueSum K33 = evenCliqueSumPos K33 := by
  rw [evenCliqueSum_K33, evenCliqueSumPos_K33]

/-- N3. The witness discrepancy is 4, so `≤ 1` is false. -/
example : discrepancyNat K33 ≤ 1 := by
  rw [discrepancyNat_K33]

/-- N4. The odd sum is 6, not 7. -/
example : oddCliqueSum K33 = 7 := by
  rw [oddCliqueSum_K33]

/-- N5. The `c_0` discrepancy is 4, not the positive-index 3. -/
example : discrepancyNat K33 = 3 := by
  rw [discrepancyNat_K33]

/-- N6. The witness has no 3-cliques: count is 0, not 9. -/
example : cliqueCount K33 3 = 9 := by
  rw [cliqueCount_K33_three]

end FlatBalance.IndNegControl

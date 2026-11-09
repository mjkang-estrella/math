/-
INDEPENDENT positive audit controls (r6).  AUDIT-ONLY: outside the
production modules; exercises nonvacuity / coverage of the certificate.

Independent coverage beyond the author suite:
  * the EMPTY vertex type (generic definitions with no vertices);
  * a second, different cutoff (N = 20) and the maximal cutoff value;
  * parity partition with explicit values 6 + 10 = 16;
  * integer bound-equivalence instance and the empty-graph balance;
  * the bridge endpoint is a real existential with concrete witness;
  * the two conventions stay distinct values (10 vs 9).
Pins: Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/
import FlatBalanceBridges
import Mathlib.Tactic.Linarith  -- audit-only: Real-cast norm_num support

namespace FlatBalance.IndControl

/-- Empty graph on zero vertices. -/
def EmptyGraph : SimpleGraph (Fin 0) :=
  ⟨fun _ _ => False, fun _ _ h => h, fun _ h => h⟩

/-- P1. EMPTY-graph coverage: `c_0 = 1` on the zero-vertex graph. -/
example : cliqueCount EmptyGraph 0 = 1 :=
  cliqueCount_zero _

/-- P2. EMPTY-graph coverage: positive counts vanish (no vertices at all). -/
example (k : ℕ) (hk : 0 < k) : cliqueCount EmptyGraph k = 0 := by
  have h0 : Fintype.card (Fin 0) = 0 := by simp
  exact cliqueCount_of_card_lt EmptyGraph (by omega)

/-- P3. EMPTY-graph coverage: the empty graph is Balanced, discrepancy
`|0 - 1| = 1` under the `c_0` convention (nonvacuous boundary case). -/
example : Balanced EmptyGraph := by
  have h0 : Fintype.card (Fin 0) = 0 := by simp
  have hodd : oddCliqueSum EmptyGraph = 0 := by
    rw [oddCliqueSum, h0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
    have hz : (0 : ℕ) % 2 ≠ 1 := by decide
    simp [hz]
  have heven : evenCliqueSum EmptyGraph = 1 := by
    rw [evenCliqueSum, h0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
    have hp : (0 : ℕ) % 2 = 0 := by decide
    simp [hp, cliqueCount_zero]
  show discrepancyNat EmptyGraph ≤ 1
  rw [discrepancyNat, hodd, heven]
  omega

/-- P4. EMPTY-graph cutoff independence: any larger cutoff agrees. -/
example : ∑ d ∈ Finset.range 7, (if d % 2 = 1 then cliqueCount EmptyGraph d else 0)
    = oddCliqueSum EmptyGraph :=
  oddCliqueSum_cutoff EmptyGraph (show Fintype.card (Fin 0) < 7 by simp)

/-- P5. Second cutoff instance on the witness, N = 20 (author used 9). -/
example : ∑ d ∈ Finset.range 20, (if d % 2 = 0 then cliqueCount K33 d else 0)
    = evenCliqueSum K33 :=
  evenCliqueSum_cutoff K33 (show Fintype.card (Fin 3 ⊕ Fin 3) < 20 by decide)

/-- P6. Parity partition with explicit values: 6 + 10 = 16. -/
example : oddCliqueSum K33 + evenCliqueSum K33 = 16 := by
  rw [oddCliqueSum_K33, evenCliqueSum_K33]

/-- P7. Integer bound-equivalence instance: the abs form of the witness
discrepancy is exactly 4. -/
example : |((oddCliqueSum K33 : ℤ) - (evenCliqueSum K33 : ℤ))| = 4 := by
  rw [evenCliqueSum_K33, oddCliqueSum_K33]; decide

/-- P8. The bridge endpoint is a genuine existential with the concrete
witness graph (no proxy witness). -/
example : ∃ (G : SimpleGraph (Fin 3 ⊕ Fin 3)),
    @Flat (Fin 3 ⊕ Fin 3) _ G ∧ ¬ @Balanced (Fin 3 ⊕ Fin 3) _ G :=
  ⟨K33, K33_flat, K33_not_balanced⟩

/-- P9. The two conventions are distinct values on the witness: 10 vs 9. -/
example : evenCliqueSum K33 = 10 ∧ evenCliqueSumPos K33 = 9 := by
  exact ⟨evenCliqueSum_K33, evenCliqueSumPos_K33⟩

/-- P10. Real-cast bridge: the real absolute difference of the clique sums
is exactly 4 (the true discrepancy value, through the cast bridge). -/
example : |(Nat.cast (oddCliqueSum K33) : ℝ) - (Nat.cast (evenCliqueSum K33) : ℝ)| = 4 := by
  rw [evenCliqueSum_K33, oddCliqueSum_K33]
  push_cast
  norm_num

/-- P11. The real cast of the discrepancy itself is 4 (no truncation). -/
example : (Nat.cast (discrepancyNat K33) : ℝ) = 4 := by
  rw [discrepancyNat_K33]; norm_num

end FlatBalance.IndControl

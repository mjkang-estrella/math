import Transport
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
 theorem minimum_source_refutation : ¬ MinimumSourceClaim := by
  rintro ⟨c,_hc,h⟩
  obtain ⟨t,ht⟩ := exists_nat_gt (3*c)
  have hu := h _ (finGraph t) (fin_connected t)
  have hl : (3*t : ℝ) ≤ (minimum (finGraph t) : ℝ) := by
    exact_mod_cast fin_minimum_lower t
  rw [fin_edge_card] at hu
  push_cast at hu
  linarith
 theorem source_refutation : ¬ SourceClaim :=
  fun h => minimum_source_refutation (source_minimum_equivalence.mp h)
end EdgeIrregulator

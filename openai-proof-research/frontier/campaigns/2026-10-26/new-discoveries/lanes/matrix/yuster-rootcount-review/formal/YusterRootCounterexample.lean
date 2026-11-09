import YusterSigns
import FourRoots

open Set Polynomial

namespace YusterCounterexample

theorem source_four_ordered_roots :
    ∃ a b c d : ℝ, 0<a ∧ a<b ∧ b<c ∧ c<d ∧ d<1 ∧
      (sourceP 48 sourceAlpha48).eval a=0 ∧ (sourceP 48 sourceAlpha48).eval b=0 ∧
      (sourceP 48 sourceAlpha48).eval c=0 ∧ (sourceP 48 sourceAlpha48).eval d=0 := by
  rcases sourceP_signs with ⟨h0,h1,h2,h3,h4⟩
  exact FourRoots.ordered_four_roots _ h0 h1 h2 h3 h4

/-- At least four roots, counting multiplicity exactly as in the source. -/
theorem source_rootcount_ge_four :
    4 ≤ FourRoots.interiorRootCount (sourceP 48 sourceAlpha48) := by
  rcases sourceP_signs with ⟨h0,h1,h2,h3,h4⟩
  exact FourRoots.four_le_interiorRootCount _ h0 h1 h2 h3 h4

theorem source_instance_false :
    ¬ FourRoots.interiorRootCount (sourceP 48 sourceAlpha48)≤2 := by
  have h := source_rootcount_ge_four
  omega

/-- Yuster Conjecture 3.9 with its exact defining source parameter is false. -/
theorem source_conjecture_357503_false :
    ¬∀ (k : ℕ) (psi : ℝ), 2≤k → psi∈Set.Icc (0:ℝ) 1 →
      (1-psi)^k=psi →
      FourRoots.interiorRootCount (sourceP k ((1-psi)^(k-1)))≤2 := by
  intro h
  have hi := h 48 sourcePsi48 (by norm_num) sourcePsi48_spec.1 sourcePsi48_spec.2
  have he : (1-sourcePsi48)^(48-1)=sourceAlpha48 := by
    simp [sourcePsi48,sourceAlpha48]
  rw [he] at hi
  exact source_instance_false hi

end YusterCounterexample

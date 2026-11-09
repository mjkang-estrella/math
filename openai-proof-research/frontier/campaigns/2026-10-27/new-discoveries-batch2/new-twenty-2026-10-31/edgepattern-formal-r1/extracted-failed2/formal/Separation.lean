import Definitions
namespace EdgePattern
open scoped BigOperators

theorem finite_separation {r m : ℕ} (a : Fin (r+1) → ℚ)
    (p : Fin (r+1) → ℝ) (t : Fin m → Fin (r+1) → ℝ) (w : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : (∑ i, (a i : ℝ) * p i) < 1)
    (ht : ∀ j, 1 ≤ ∑ i, (a i : ℝ) * t j i)
    (hw : ∀ j, 0 ≤ w j) (hs : (∑ j, w j) = 1) :
    ¬ Weaker p (fun i => ∑ j, w j * t j i) := by
  intro h
  have hsum : 1 ≤ ∑ j, w j * ∑ i, (a i : ℝ) * t j i := by
    calc
      1 = ∑ j, w j * 1 := by simpa using hs.symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ht j) (hw j))
  have heq : (∑ i, (a i : ℝ) * ∑ j, w j * t j i) =
      ∑ j, w j * ∑ i, (a i : ℝ) * t j i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext j
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (not_le_of_gt hp) (h a ha (heq ▸ hsum))
end EdgePattern

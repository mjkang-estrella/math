import Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace Adverse381433

variable {V L : Type} [Fintype V] [Fintype L] [DecidableEq V]

omit [DecidableEq V] in
theorem gram_energy (B : L → V → ℝ) (z : V → ℝ) :
    (∑ i, z i * ∑ l, B l i * ∑ j, B l j * z j) =
      ∑ l, (∑ i, B l i * z i)^2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gram_eigenvalue_lower (G : SimpleGraph V) (B : L → V → ℝ)
    (hgram : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (μ : ℝ) (z : V → ℝ) (hz : z ≠ 0)
    (he : (adjacency G).mulVec z = μ • z) : -3 ≤ μ := by
  classical
  have hc (i : V) : (∑ l, B l i * ∑ j, B l j * z j) = (μ+3)*z i := by
    have hi := congrFun he i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    simp_rw [hgram, sub_mul, Finset.sum_sub_distrib] at hi
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hi
    have hex : (∑ j, (∑ l, B l i * B l j) * z j) =
        ∑ l, B l i * ∑ j, B l j * z j := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hex] at hi
    linarith
  have hn : 0 ≤ ∑ l, (∑ i, B l i * z i)^2 := Finset.sum_nonneg (by intros; positivity)
  rw [← gram_energy B z] at hn
  simp_rw [hc] at hn
  have hid : (∑ i, z i * ((μ+3)*z i)) = (μ+3) * ∑ i, (z i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at hn
  have hz' : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i,hi⟩ := hz'
  have hp : 0 < ∑ j, (z j)^2 :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))
  nlinarith

theorem leastEigenvalue_eq_of_gram (G : SimpleGraph V) (B : L → V → ℝ)
    (hgram : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (hattain : (-3 : ℝ) ∈ realEigenvalues G) : leastEigenvalue G = -3 := by
  have hl : ∀ μ ∈ realEigenvalues G, (-3 : ℝ) ≤ μ := by
    rintro μ ⟨z,hz,he⟩
    exact gram_eigenvalue_lower G B hgram μ z hz he
  exact le_antisymm (csInf_le ⟨-3, hl⟩ hattain) (le_csInf ⟨-3,hattain⟩ hl)

end Adverse381433

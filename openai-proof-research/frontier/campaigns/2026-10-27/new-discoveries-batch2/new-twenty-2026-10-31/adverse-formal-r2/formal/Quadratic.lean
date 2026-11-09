import Gram
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
namespace Adverse381433

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem normalized_energy (B : (Fin 3 × ZMod 6) → V → ℝ) (x : V → ℝ) :
    (∑ i, ∑ j, x i * ((∑ l, B l i * B l j) / 3) * x j) =
      (∑ l, (∑ i, B l i * x i)^2) / 3 := by
  rw [← gram_energy B x]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem objective_gram (G : SimpleGraph V) (B : (Fin 3 × ZMod 6) → V → ℝ)
    (hg : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (hm : leastEigenvalue G = -3) (x : V → ℝ) :
    objective G x = 2 * ∑ i, x i - (∑ l, (∑ i, B l i * x i)^2) / 3 := by
  unfold objective
  congr 1
  trans ∑ i, ∑ j, x i * ((∑ l, B l i * B l j) / 3) * x j
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hg, hm]
    split_ifs <;> ring
  · exact normalized_energy B x

theorem objective_le_six (G : SimpleGraph V) (B : (Fin 3 × ZMod 6) → V → ℝ)
    (hg : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (hm : leastEigenvalue G = -3) (hcol : ∀ i, ∑ l, B l i = 3) (x : V → ℝ) :
    objective G x ≤ 6 := by
  rw [objective_gram G B hg hm]
  have hs : (∑ l, ∑ i, B l i * x i) = 3 * ∑ i, x i := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hcol]
  have hn : 0 ≤ ∑ l, (1 - ∑ i, B l i * x i)^2 :=
    Finset.sum_nonneg (by intros; positivity)
  have he : (∑ l, (1 - ∑ i, B l i * x i)^2) =
      18 - 2 * (∑ l, ∑ i, B l i * x i) + ∑ l, (∑ i, B l i * x i)^2 := by
    simp_rw [sub_sq]
    simp only [one_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [← Finset.mul_sum]
  rw [he, hs] at hn
  linarith

theorem upsilon_eq_six (G : SimpleGraph V) (B : (Fin 3 × ZMod 6) → V → ℝ)
    (hg : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (hm : leastEigenvalue G = -3) (hcol : ∀ i, ∑ l, B l i = 3)
    (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) (hline : ∀ l, ∑ i, B l i * x i = 1) :
    upsilon G = 6 := by
  have hs : 3 * ∑ i, x i = 18 := by
    calc 3 * ∑ i, x i = ∑ l, ∑ i, B l i * x i := by
           rw [Finset.sum_comm, Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro i _
           rw [← Finset.sum_mul, hcol]
         _ = 18 := by simp [hline]
  have ho : objective G x = 6 := by
    rw [objective_gram G B hg hm]
    simp only [hline, one_pow]
    norm_num at *
    linarith
  have hb : BddAbove {r | ∃ x : V → ℝ, (∀ i, 0 ≤ x i) ∧ r = objective G x} := by
    refine ⟨6, ?_⟩
    rintro r ⟨y,_,rfl⟩
    exact objective_le_six G B hg hm hcol y
  have hin : (6 : ℝ) ∈ {r | ∃ x : V → ℝ, (∀ i, 0 ≤ x i) ∧ r = objective G x} :=
    ⟨x,hx,ho.symm⟩
  exact le_antisymm (csSup_le ⟨6,hin⟩ (by rintro r ⟨y,_,rfl⟩; exact objective_le_six G B hg hm hcol y)) (le_csSup hb hin)

end Adverse381433

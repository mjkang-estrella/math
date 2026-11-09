import ArrowheadCriterion

open Finset Matrix
namespace FlatBernoulli
noncomputable section

def gridNode (N : ℕ) (i : Fin N) : ℝ := (i:ℝ)/(N:ℝ)
def gridR (N : ℕ) (_ : Fin N) : ℝ := Real.sqrt ((N:ℝ)⁻¹)
def gridS (N : ℕ) (i : Fin N) : ℝ := Real.sqrt (1-gridNode N i)
def gridV (N : ℕ) (i : Fin N) : ℝ := gridS N i*gridR N i

theorem gridNode_nonneg (N : ℕ) (i : Fin N) : 0 ≤ gridNode N i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gridNode_lt_one (N : ℕ) (hN : 0 < N) (i : Fin N) : gridNode N i < 1 := by
  unfold gridNode
  exact (div_lt_one (by exact_mod_cast hN)).mpr (by exact_mod_cast i.isLt)

theorem gridR_sq (N : ℕ) (i : Fin N) : gridR N i^2 = (N:ℝ)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem gridS_sq (N : ℕ) (hN : 0 < N) (i : Fin N) : gridS N i^2 = 1-gridNode N i :=
  Real.sq_sqrt (by linarith [gridNode_lt_one N hN i])

theorem gridR_mass (N : ℕ) (hN : 0 < N) : ∑ i, gridR N i^2 = 1 := by
  simp only [gridR_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hN))

theorem gridNode_sum (N : ℕ) (hN : 0 < N) : ∑ i, gridNode N i = ((N:ℝ)-1)/2 := by
  have hcast := congrArg (fun k : ℕ => (k:ℝ)) (Finset.sum_range_id_mul_two N)
  push_cast at hcast
  rw [Nat.cast_sub (by omega)] at hcast
  simp only [Nat.cast_one] at hcast
  have hsum : (∑ i : Fin N, (i:ℝ))*2 = (N:ℝ)*((N:ℝ)-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hcast
  simp only [gridNode, ← Finset.sum_div]
  apply (div_eq_iff (by exact_mod_cast (Nat.ne_of_gt hN))).mpr
  nlinarith

theorem gridV_second (N : ℕ) (hN : 0 < N) :
    ∑ i, gridV N i^2 = ((N:ℝ)+1)/(2*(N:ℝ)) := by
  simp_rw [gridV, mul_pow, gridS_sq N hN, gridR_sq, sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, gridNode_sum N hN]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

theorem gridV_second_lower (N : ℕ) (hN : 0 < N) : 1/2 ≤ ∑ i, gridV N i^2 := by
  rw [gridV_second N hN]
  apply (le_div_iff₀ (by positivity : 0 < 2*(N:ℝ))).mpr
  nlinarith

end
end FlatBernoulli

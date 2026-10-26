import PolynomialWitness

set_option maxHeartbeats 2000000

open Matrix
open scoped ComplexOrder
namespace CstarPolynomial
noncomputable section

def correction (a : Fin 3 → M₂) : M₂ :=
  (∑ i, (a i) ^ 2) - (1 / 9 : ℂ) • (∑ i, a i) ^ 2

def shifted (a : Fin 3 → M₂) (i : Fin 3) : M₂ :=
  a i + (1 / 3 : ℂ) • (∑ j, a j)

/-- The full degree-three left-hand defect in source Conjecture 2.4. -/
def kushelLeft (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  -leftMoment a 2 + (1 / 9 : ℂ) • (leftMoment a 1) ^ 2 +
    (1 / 9 : ℂ) • (correction a * star (correction a)) +
    (2 / 3 : ℂ) • (∑ i, a i * shifted a i * star (shifted a i) * star (a i)) -
    (4 / 27 : ℂ) • (∑ i, a i * (∑ j, a j) * star (∑ j, a j) * star (a i)) -
    leftMoment b 2

/-- The full degree-three right-hand defect in source Conjecture 2.4. -/
def kushelRight (a : Fin 3 → M₂) (b : Fin 2 → M₂) : M₂ :=
  -rightMoment a 2 + (1 / 9 : ℂ) • (rightMoment a 1) ^ 2 +
    (1 / 9 : ℂ) • (star (correction a) * correction a) +
    (2 / 3 : ℂ) • (∑ i, star (a i) * star (shifted a i) * shifted a i * a i) -
    (4 / 27 : ℂ) • (∑ i, star (a i) * star (∑ j, a j) * (∑ j, a j) * a i) -
    rightMoment b 2

def defects : Fin 6 → M₂ :=
  ![schoenbergLeft roots critical, schoenbergRight roots critical,
    deBruinLeft roots critical, deBruinRight roots critical,
    kushelLeft roots critical, kushelRight roots critical]

lemma defect_matrices : defects =
    ![!![8,-4; -4,0], !![0,4; 4,8], !![56,-24; -24,8],
      !![8,24; 24,56], !![-392,168; 168,-56], !![-56,-168; -168,-392]] := by
  funext k
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [defects, schoenbergLeft, schoenbergRight, deBruinLeft, deBruinRight,
      kushelLeft, kushelRight, correction, shifted, leftMoment, rightMoment,
      roots, critical, A, Matrix.mul_apply, Fin.sum_univ_succ, pow_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.ofNat_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct,
      map_ofNat]

lemma defects_hermitian (k : Fin 6) : (defects k).IsHermitian := by
  rw [defect_matrices]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose_apply, map_ofNat]

lemma kushel_left_form :
    star (![1,0] : Fin 2 → ℂ) ⬝ᵥ (defects 4 *ᵥ ![1,0]) = -392 := by
  rw [defect_matrices]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

lemma kushel_right_form :
    star (![0,1] : Fin 2 → ℂ) ⬝ᵥ (defects 5 *ᵥ ![0,1]) = -392 := by
  rw [defect_matrices]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

lemma defects_not_posSemidef (k : Fin 6) : ¬ (defects k).PosSemidef := by
  fin_cases k
  · exact source_counterexample_355008_355009.2.2.1
  · exact source_counterexample_355008_355009.2.2.2.1
  · exact source_counterexample_355008_355009.2.2.2.2.1
  · exact source_counterexample_355008_355009.2.2.2.2.2
  · intro h
    have hh := h.dotProduct_mulVec_nonneg (![1,0] : Fin 2 → ℂ)
    change (0 : ℂ) ≤ star (![1,0] : Fin 2 → ℂ) ⬝ᵥ (defects 4 *ᵥ ![1,0]) at hh
    rw [kushel_left_form] at hh
    have hr : (0 : ℝ) ≤ -392 := by exact_mod_cast hh
    norm_num at hr
  · intro h
    have hh := h.dotProduct_mulVec_nonneg (![0,1] : Fin 2 → ℂ)
    change (0 : ℂ) ≤ star (![0,1] : Fin 2 → ℂ) ⬝ᵥ (defects 5 *ᵥ ![0,1]) at hh
    rw [kushel_right_form] at hh
    have hr : (0 : ℝ) ≤ -392 := by exact_mod_cast hh
    norm_num at hr

lemma genuine_roots (i : Fin 3) : cubic roots (roots i) = 0 := by
  fin_cases i <;> simp [cubic, roots]

lemma genuine_critical_points (i : Fin 2) : sourceDerivative roots (critical i) = 0 := by
  rw [derivative_factorization]
  fin_cases i <;> simp [critical]

theorem source_all_three_conjectures_false :
    (∑ i, roots i) = 0 ∧
    (∀ i, cubic roots (roots i) = 0) ∧
    (∀ z : M₂, sourceDerivative roots z =
      (3 : ℂ) • ((z - critical 0) * (z - critical 1))) ∧
    (∀ i, sourceDerivative roots (critical i) = 0) ∧
    (∀ k : Fin 6, (defects k).IsHermitian ∧ ¬ (defects k).PosSemidef) :=
  ⟨centered, genuine_roots, derivative_factorization, genuine_critical_points,
    fun k => ⟨defects_hermitian k, defects_not_posSemidef k⟩⟩

end
end CstarPolynomial

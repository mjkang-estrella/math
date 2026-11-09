import Mathlib

open Matrix Polynomial
namespace CoefficientMinorCounterexample
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def D1 : Mat := !![1, 0, 0; 0, 2, 0; 0, 0, 1]
def D2 : Mat := !![13, 9, 7; 9, 7, 5; 7, 5, 4]
def D3 : Mat := !![5, 7, 8; 7, 11, 12; 8, 12, 14]

theorem symmetric_D1 : D1.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D1, Matrix.conjTranspose_apply]
theorem symmetric_D2 : D2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D2, Matrix.conjTranspose_apply]
theorem symmetric_D3 : D3.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D3, Matrix.conjTranspose_apply]

theorem nonzero_coordinate (v : Fin 3 → ℝ) (h : v ≠ 0) :
    v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  by_contra hn
  simp only [not_or, not_not] at hn
  apply h
  ext i
  fin_cases i <;> simp [hn]

theorem D1_posDef : D1.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos symmetric_D1
  intro v hv
  simp [dotProduct, mulVec, Fin.sum_univ_succ, D1]
  rcases nonzero_coordinate v hv with h | h | h
  all_goals nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem D2_quadratic (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (D2 *ᵥ v) =
      13 * (v 0 + 9 / 13 * v 1 + 7 / 13 * v 2)^2 +
      (10 / 13) * (v 1 + (1 / 5) * v 2)^2 + (1 / 5) * (v 2)^2 := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, D2]
  ring

theorem D2_posDef : D2.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos symmetric_D2
  intro v hv
  rw [D2_quadratic]
  have h0 := sq_nonneg (v 0 + 9 / 13 * v 1 + 7 / 13 * v 2)
  have h1 := sq_nonneg (v 1 + (1 / 5) * v 2)
  have h2 := sq_nonneg (v 2)
  by_contra hn
  have z2 : v 2 = 0 := by nlinarith
  have z1 : v 1 = 0 := by simp [z2] at h1 h0 hn; nlinarith
  have z0 : v 0 = 0 := by simp [z2, z1] at hn; nlinarith
  apply hv
  ext i
  fin_cases i <;> simp [z0, z1, z2]

theorem D3_quadratic (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (D3 *ᵥ v) =
      5 * (v 0 + 7 / 5 * v 1 + 8 / 5 * v 2)^2 +
      (6 / 5) * (v 1 + (2 / 3) * v 2)^2 + (2 / 3) * (v 2)^2 := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, D3]
  ring

theorem D3_posDef : D3.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos symmetric_D3
  intro v hv
  rw [D3_quadratic]
  have h0 := sq_nonneg (v 0 + 7 / 5 * v 1 + 8 / 5 * v 2)
  have h1 := sq_nonneg (v 1 + (2 / 3) * v 2)
  have h2 := sq_nonneg (v 2)
  by_contra hn
  have z2 : v 2 = 0 := by nlinarith
  have z1 : v 1 = 0 := by simp [z2] at h1 h0 hn; nlinarith
  have z0 : v 0 = 0 := by simp [z2, z1] at hn; nlinarith
  apply hv
  ext i
  fin_cases i <;> simp [z0, z1, z2]

abbrev PX := Polynomial ℝ
abbrev PXZ := Polynomial PX
abbrev PXYZ := Polynomial PXZ

def pencil : Matrix (Fin 3) (Fin 3) PXYZ := fun i j =>
  C (C ((if i = j then 1 else 0) + X * C (D1 i j))) +
    X * C (C (C (D2 i j))) + C (X * C (C (D3 i j)))
def determinant : PXYZ := pencil.det
def coefficientMatrix : Matrix ℕ ℕ PX := fun i j => (determinant.coeff i).coeff j
def minor : PX := (coefficientMatrix.submatrix (fun i : Fin 3 => i.val)
  (fun j : Fin 3 => j.val)).det

def displayed : Matrix (Fin 3) (Fin 3) PX :=
  !![2*X^3+5*X^2+4*X+1, 49*X^2+79*X+30, 28*X+22;
     41*X^2+65*X+24, 254*X+164, 64;
     19*X+16, 62, 0]

theorem determinant_expansion : determinant =
    C (C (2*X^3+5*X^2+4*X+1) + X*C (49*X^2+79*X+30) +
       X^2*C (28*X+22) + X^3*C 4) +
    X*C (C (41*X^2+65*X+24) + X*C (254*X+164) + X^2*C 64) +
    X^2*C (C (19*X+16) + X*C 62) + X^3*C (C 2) := by
  norm_num [determinant, pencil, D1, D2, D3, Matrix.det_fin_three]
  simp only [map_ofNat]
  ring

theorem coefficient_bridge :
    coefficientMatrix.submatrix (fun i : Fin 3 => i.val)
      (fun j : Fin 3 => j.val) = displayed := by
  apply Matrix.ext
  intro i j
  change (determinant.coeff i.val).coeff j.val = displayed i j
  rw [determinant_expansion]
  fin_cases i <;> fin_cases j <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C,
      Fin.reduceFinMk, Nat.reduceEqDiff, ite_true, ite_false, zero_mul, one_mul,
      add_zero, zero_add, displayed, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> rfl

theorem minor_formula : minor = -4 * (3076*X^3 + 3012*X^2 - 99*X - 440) := by
  rw [minor, coefficient_bridge]
  simp [displayed, Matrix.det_fin_three]
  ring

theorem minor_at_zero : minor.eval 0 = 1760 := by
  rw [minor_formula]
  norm_num

theorem minor_at_one : minor.eval 1 = -22196 := by
  rw [minor_formula]
  norm_num

theorem positive_real_root : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ minor.eval x = 0 := by
  have hc : Continuous (fun x : ℝ => minor.eval x) := Polynomial.continuous _
  have hz : (0 : ℝ) ∈ Set.Ioo (minor.eval 1) (minor.eval 0) := by
    rw [minor_at_zero, minor_at_one]
    constructor <;> norm_num
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn hz
  exact ⟨x, hx.1, hx.2, hx0⟩

def Stable (p : PX) : Prop := ∀ z : ℂ, 0 < z.re → p.eval₂ Complex.ofRealHom z ≠ 0

theorem minor_not_stable : ¬ Stable minor := by
  intro hs
  obtain ⟨x, hx, _, hzero⟩ := positive_real_root
  apply hs (x : ℂ) (by simpa using hx)
  change minor.eval₂ Complex.ofRealHom (Complex.ofRealHom x) = 0
  rw [Polynomial.eval₂_at_apply, hzero]
  rfl

theorem source_counterexample :
    D1.PosDef ∧ D2.PosDef ∧ D3.PosDef ∧
    ¬ Stable ((coefficientMatrix.submatrix (fun i : Fin 3 => i.val)
      (fun j : Fin 3 => j.val)).det) := by
  exact ⟨D1_posDef, D2_posDef, D3_posDef, minor_not_stable⟩

end
end CoefficientMinorCounterexample

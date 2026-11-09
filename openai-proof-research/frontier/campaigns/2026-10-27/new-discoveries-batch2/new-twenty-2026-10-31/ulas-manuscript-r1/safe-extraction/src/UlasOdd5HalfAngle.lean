import UlasOdd5Initialization
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4
/-- Integral half-angle pair: W_N(1+2Y), U_N(1+2Y). -/
noncomputable def halfPair : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1,1)
  | N+1 => let p := halfPair N
    (p.1+4*Polynomial.X*p.2, p.1+(1+4*Polynomial.X)*p.2)

theorem halfPair_correct (N : ℕ) :
    Represents (w^N*(1+y))
      ((1+Polynomial.X)*(halfPair N).1)
      (2*(halfPair N).2-(halfPair N).1) := by
  induction N with
  | zero =>
    have h := represents_add represents_one (represents_mul_y represents_one)
    convert h using 1 <;> norm_num [halfPair]
  | succ N ih =>
    have h := represents_mul_w ih
    convert h using 1 <;> simp [halfPair, pow_succ] <;> ring

/-- The half-angle rule for a constant input. -/
theorem halfAngle_constant (N : ℕ) :
    sectionEven (w^N*(1+y)) = (1+y)*ev (halfPair N).1 := by
  rw [halfPair_correct, sectionEven_add, sectionEven_expand, sectionEven_X_expand]
  simp

/-- These coefficient divisibilities are established by recurrence, with no interpolation. -/
def FourScaled (F : Polynomial ℤ) : Prop := ∀ E, (4:ℤ)^E ∣ F.coeff E

theorem fourScaled_one : FourScaled 1 := by
  intro E
  by_cases h : E=0
  · simp [h]
  · simp [Polynomial.coeff_one, h]

theorem fourScaled_add {F G : Polynomial ℤ} (hF : FourScaled F) (hG : FourScaled G) :
    FourScaled (F+G) := by
  intro E
  simpa using dvd_add (hF E) (hG E)

theorem fourScaled_four_X {F : Polynomial ℤ} (hF : FourScaled F) :
    FourScaled (4*Polynomial.X*F) := by
  have he : 4*Polynomial.X*F = Polynomial.C 4*(Polynomial.X*F) := by norm_num; ring
  rw [he]
  intro E
  cases E with
  | zero => simp
  | succ E =>
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, pow_succ']
    exact mul_dvd_mul_left 4 (hF E)

theorem halfPair_scaled (N : ℕ) : FourScaled (halfPair N).1 ∧ FourScaled (halfPair N).2 := by
  induction N with
  | zero => exact ⟨fourScaled_one,fourScaled_one⟩
  | succ N ih =>
    constructor
    · exact fourScaled_add ih.1 (fourScaled_four_X ih.2)
    · have he : (halfPair (N+1)).2 = (halfPair N).1 +
          ((halfPair N).2+4*Polynomial.X*(halfPair N).2) := by simp [halfPair]; ring
      rw [he]
      exact fourScaled_add ih.1 (fourScaled_add ih.2 (fourScaled_four_X ih.2))

/-- Constant coefficients of both half-angle polynomials are fixed. -/
theorem halfPair_constants (N : ℕ) :
    (halfPair N).1.coeff 0 = 1 ∧ (halfPair N).2.coeff 0 = (N:ℤ)+1 := by
  induction N with
  | zero => simp [halfPair]
  | succ N ih => simp [halfPair, add_mul, ih]; ring
end Ulas.Round5Odd

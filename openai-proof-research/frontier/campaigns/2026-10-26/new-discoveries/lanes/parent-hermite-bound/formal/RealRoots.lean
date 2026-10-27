import InitialValues

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial

def complexHermite (n : ℕ) (z : ℂ) : ℂ := aeval z (hermitePoly n)

def crossImaginary (n : ℕ) (z : ℂ) : ℝ :=
  (complexHermite (n + 1) z * star (complexHermite n z)).im

theorem complexHermite_recurrence (n : ℕ) (z : ℂ) :
    complexHermite (n + 2) z = 2 * z * complexHermite (n + 1) z -
      ((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * complexHermite n z := by
  have h := congrArg (aeval z) (hermitePoly_recurrence n)
  simpa [complexHermite] using h

theorem crossImaginary_recurrence (n : ℕ) (z : ℂ) :
    crossImaginary (n + 1) z = 2 * z.im * Complex.normSq (complexHermite (n + 1) z) +
      2 * ((n : ℝ) + 1) * crossImaginary n z := by
  unfold crossImaginary
  rw [show n + 1 + 1 = n + 2 by omega, complexHermite_recurrence]
  simp only [sub_mul, mul_assoc, Complex.sub_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  norm_num
  ring

theorem crossImaginary_same_sign (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    0 < z.im * crossImaginary n z := by
  induction n with
  | zero =>
    norm_num [crossImaginary, complexHermite, hermitePoly, Complex.mul_im]
    nlinarith [sq_pos_of_ne_zero hz]
  | succ n ih =>
    rw [crossImaginary_recurrence]
    have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
    have hs := mul_nonneg (sq_nonneg z.im)
      (Complex.normSq_nonneg (complexHermite (n + 1) z))
    nlinarith [mul_pos hp ih]

theorem complexHermite_root_real (n : ℕ) (z : ℂ) (hz : complexHermite n z = 0) :
    z.im = 0 := by
  cases n with
  | zero => simp [complexHermite, hermitePoly] at hz
  | succ n =>
    by_contra hi
    have h := crossImaginary_same_sign n z hi
    simp [crossImaginary, hz] at h

theorem hermitePoly_ne_zero (n : ℕ) : hermitePoly n ≠ 0 := by
  induction n with
  | zero => simp [hermitePoly]
  | succ n ih =>
    intro h
    have hd := congrArg derivative h
    rw [hermitePoly_derivative_succ, derivative_zero] at hd
    have hc : (C (2 * ((n : ℝ) + 1)) : Polynomial ℝ) ≠ 0 := by
      intro he
      have hv := congrArg (fun p : Polynomial ℝ => p.eval 0) he
      simp only [eval_C, eval_zero] at hv
      have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
      linarith
    exact (mul_ne_zero hc ih) hd

theorem hermitePoly_splits (n : ℕ) : (hermitePoly n).Splits := by
  have hc : ((hermitePoly n).map (algebraMap ℝ ℂ)).Splits := IsAlgClosed.splits _
  apply hc.of_splits_map (algebraMap ℝ ℂ)
  intro z hz
  have hp : (hermitePoly n).map (algebraMap ℝ ℂ) ≠ 0 :=
    Polynomial.map_ne_zero (hermitePoly_ne_zero n)
  have hr : complexHermite n z = 0 := by
    simpa [complexHermite, aeval_def] using (Polynomial.mem_roots hp).mp hz
  have hi := complexHermite_root_real n z hr
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [hi]

end HermiteEnvelope

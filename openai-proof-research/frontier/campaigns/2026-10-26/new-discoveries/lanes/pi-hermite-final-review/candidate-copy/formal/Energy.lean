import SourceDefs

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial Set

def weightedSlope (n : ℕ) (x : ℝ) : ℝ :=
  ((derivative (hermitePoly n) - X * hermitePoly n).eval x) *
    Real.exp (-(x ^ 2) / 2)

def energy (n : ℕ) (x : ℝ) : ℝ :=
  (2 * (n : ℝ) + 1 - x ^ 2) * weightedHermite n x ^ 2 + weightedSlope n x ^ 2

theorem exp_weight_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1
  all_goals simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
  all_goals ring

theorem polynomial_weight_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun t => p.eval t * Real.exp (-(t ^ 2) / 2))
      ((derivative p - X * p).eval x * Real.exp (-(x ^ 2) / 2)) x := by
  convert (p.hasDerivAt x).mul (exp_weight_hasDerivAt x) using 1
  simp only [eval_sub, eval_mul, eval_X]
  ring

theorem weightedHermite_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (weightedHermite n) (weightedSlope n x) x :=
  polynomial_weight_hasDerivAt (hermitePoly n) x

theorem weightedSlope_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (weightedSlope n)
      ((x ^ 2 - (2 * (n : ℝ) + 1)) * weightedHermite n x) x := by
  have hp := polynomial_weight_hasDerivAt
    (derivative (hermitePoly n) - X * hermitePoly n) x
  have hode := congrArg (fun p : Polynomial ℝ => p.eval x) (hermitePoly_ode n)
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_zero] at hode
  have hd2 : (derivative (derivative (hermitePoly n))).eval x =
      2 * x * (derivative (hermitePoly n)).eval x -
        2 * (n : ℝ) * (hermitePoly n).eval x := by linarith
  convert hp using 1
  · rfl
  · simp only [weightedHermite, hermiteValue, derivative_sub, derivative_mul,
      derivative_X, one_mul, eval_sub, eval_add, eval_mul, eval_X]
    rw [hd2]
    ring

theorem energy_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (energy n) (-2 * x * weightedHermite n x ^ 2) x := by
  have hq : HasDerivAt (fun t : ℝ => 2 * (n : ℝ) + 1 - t ^ 2) (-2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub (2 * (n : ℝ) + 1)
  have h := ((hq.mul ((weightedHermite_hasDerivAt n x).pow 2)).add
    ((weightedSlope_hasDerivAt n x).pow 2))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply, Nat.cast_ofNat]
    ring

theorem energy_antitone (n : ℕ) : AntitoneOn (energy n) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr (fun x => (energy_hasDerivAt n x).continuousAt)).continuousOn
  · exact (fun x _ => (energy_hasDerivAt n x).differentiableAt.differentiableWithinAt)
  · intro x hx
    rw [(energy_hasDerivAt n x).deriv]
    have hx0 : 0 ≤ x := le_of_lt (by simpa using hx : 0 < x)
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)

theorem weighted_bulk_of_initial_energy (n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (h0 : energy n 0 ≤ (2 * (n : ℝ) + 1) * C ^ 2)
    (x : ℝ) (hx : 0 ≤ x) (hq : x ^ 2 < 2 * (n : ℝ) + 1) :
    |weightedHermite n x| ≤ C /
      Real.sqrt (1 - x ^ 2 / (2 * (n : ℝ) + 1)) := by
  have hE : 0 < 2 * (n : ℝ) + 1 := by positivity
  have he := (energy_antitone n) (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  have hbound : (2 * (n : ℝ) + 1 - x ^ 2) * weightedHermite n x ^ 2 ≤
      (2 * (n : ℝ) + 1) * C ^ 2 := by
    have he0 := he.trans h0
    unfold energy at he0
    nlinarith [sq_nonneg (weightedSlope n x)]
  have ht : 0 < 1 - x ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [sub_pos, div_lt_one hE]
    exact hq
  have hs := Real.sq_sqrt ht.le
  have hsp := Real.sqrt_pos.mpr ht
  apply (le_div_iff₀ hsp).2
  refine le_of_sq_le_sq ?_ hC
  rw [mul_pow, sq_abs, hs]
  calc
    _ = ((2 * (n : ℝ) + 1 - x ^ 2) * weightedHermite n x ^ 2) /
        (2 * (n : ℝ) + 1) := by field_simp
    _ ≤ C ^ 2 := (div_le_iff₀ hE).2 (by nlinarith [hbound])

end HermiteEnvelope

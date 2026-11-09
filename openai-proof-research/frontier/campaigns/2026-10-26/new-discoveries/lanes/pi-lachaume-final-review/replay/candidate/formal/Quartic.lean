import Mathlib

open Polynomial

namespace Lachaume

noncomputable def quartic {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 4 + 8 * x ^ 3 + 6 * x ^ 2 + 8 * x + 1

noncomputable def quarticPoly : ℝ[X] := X ^ 4 + 8 * X ^ 3 + 6 * X ^ 2 + 8 * X + 1

noncomputable def first (x : ℝ) : ℝ := 4 * x ^ 3 + 24 * x ^ 2 + 12 * x + 8
noncomputable def second (x : ℝ) : ℝ := 12 * x ^ 2 + 48 * x + 12

theorem quarticPoly_eval (x : ℝ) : quarticPoly.eval x = quartic x := by
  simp [quarticPoly, quartic]

theorem quarticPoly_degree : quarticPoly.natDegree = 4 := by
  unfold quarticPoly
  compute_degree!

theorem quarticPoly_coeff_nonneg (i : ℕ) : 0 ≤ quarticPoly.coeff i := by
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    by_cases h3 : i = 3 <;> by_cases h4 : i = 4 <;>
    simp_all [quarticPoly, coeff_add, coeff_X_pow, coeff_one, coeff_X, eq_comm]

theorem derivative_eval (x : ℝ) : quarticPoly.derivative.eval x = first x := by
  simp [quarticPoly, first, derivative_add, derivative_mul, derivative_pow]
  ring

theorem second_derivative_eval (x : ℝ) :
    quarticPoly.derivative.derivative.eval x = second x := by
  simp [quarticPoly, second, derivative_add, derivative_mul, derivative_pow]
  ring

theorem laguerre_identity (x : ℝ) :
    4 * quartic x * second x - 3 * first x ^ 2 = -144 * (x ^ 2 - 1) ^ 2 := by
  unfold quartic first second
  ring

theorem source_global_differential_condition (x : ℝ) :
    quarticPoly.eval x * quarticPoly.derivative.derivative.eval x +
      (1 / (quarticPoly.natDegree : ℝ) - 1) * (quarticPoly.derivative.eval x) ^ 2 ≤ 0 := by
  rw [quarticPoly_degree, quarticPoly_eval, derivative_eval, second_derivative_eval]
  have h := laguerre_identity x
  nlinarith [sq_nonneg (x ^ 2 - 1)]

theorem quartic_pos {x : ℝ} (hx : 0 < x) : 0 < quartic x := by
  unfold quartic
  positivity

theorem hasDerivAt_quartic (x : ℝ) : HasDerivAt quartic (first x) x := by
  convert (((((hasDerivAt_id x).pow 4).add (((hasDerivAt_id x).pow 3).const_mul 8)).add
    (((hasDerivAt_id x).pow 2).const_mul 6)).add ((hasDerivAt_id x).const_mul 8)).add_const 1 using 1
  · funext y
    dsimp [quartic]
  · dsimp [first]
    ring

theorem hasDerivAt_first (x : ℝ) : HasDerivAt first (second x) x := by
  convert (((((hasDerivAt_id x).pow 3).const_mul 4).add
    (((hasDerivAt_id x).pow 2).const_mul 24)).add ((hasDerivAt_id x).const_mul 12)).add_const 8 using 1
  · funext y
    dsimp [first]
  · dsimp [second]
    ring

noncomputable def nonrealRoot : ℂ :=
  ⟨Real.sqrt 3 - 2, Real.sqrt (4 * Real.sqrt 3 - 6)⟩

theorem sqrt_three_bounds : 3 / 2 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem nonrealRoot_im_pos : 0 < nonrealRoot.im := by
  apply Real.sqrt_pos.2
  nlinarith [sqrt_three_bounds.1]

theorem quartic_complex_factorization (z : ℂ) :
    quartic z = (z ^ 2 + (4 - 2 * (Real.sqrt 3 : ℂ)) * z + 1) *
      (z ^ 2 + (4 + 2 * (Real.sqrt 3 : ℂ)) * z + 1) := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold quartic
  linear_combination 4 * z ^ 2 * hs

theorem nonrealRoot_quadratic :
    nonrealRoot ^ 2 + (4 - 2 * (Real.sqrt 3 : ℂ)) * nonrealRoot + 1 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hv := Real.sq_sqrt (show 0 ≤ 4 * Real.sqrt 3 - 6 by nlinarith [sqrt_three_bounds.1])
  apply Complex.ext <;>
    simp [nonrealRoot, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem nonrealRoot_isRoot :
    (quarticPoly.map (algebraMap ℝ ℂ)).IsRoot nonrealRoot := by
  change (quarticPoly.map (algebraMap ℝ ℂ)).eval nonrealRoot = 0
  have he : (quarticPoly.map (algebraMap ℝ ℂ)).eval nonrealRoot = quartic nonrealRoot := by
    simp [quarticPoly, quartic]
  rw [he, quartic_complex_factorization, nonrealRoot_quadratic, zero_mul]

theorem source_nonreal_root_counterexample :
    quarticPoly.natDegree = 4 ∧ (∀ i, 0 ≤ quarticPoly.coeff i) ∧
    (∀ x : ℝ, quarticPoly.eval x * quarticPoly.derivative.derivative.eval x +
      (1 / (quarticPoly.natDegree : ℝ) - 1) * (quarticPoly.derivative.eval x) ^ 2 ≤ 0) ∧
    ∃ z : ℂ, (quarticPoly.map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  exact ⟨quarticPoly_degree, quarticPoly_coeff_nonneg,
    source_global_differential_condition, nonrealRoot, nonrealRoot_isRoot,
    ne_of_gt nonrealRoot_im_pos⟩

end Lachaume

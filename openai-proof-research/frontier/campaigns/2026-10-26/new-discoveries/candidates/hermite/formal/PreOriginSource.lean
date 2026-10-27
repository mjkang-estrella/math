import OddAssembly
import PreOriginTrig

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

/-- The generic sine comparison now uses the proved trigonometric estimate. -/
theorem sine_comparison_bulk_bound_proved (E A C x y : ℝ) (hE : 7 ≤ E)
    (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / E)) (hy : 0 ≤ y)
    (hupper : y ≤ A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x))
    (hA : A ^ 2 ≤ (99 / 98 : ℝ) * (E * C ^ 2)) :
    (E - x ^ 2) * y ^ 2 ≤ E * C ^ 2 :=
  sine_comparison_bulk_bound E A C x y hE hx hx0 hy hupper hA
    (fun u hu hu2 => preX0_sin_sq_bound E hE u hu hu2)

/-- Source-scaled near-origin bound; only the actual oscillator comparison remains. -/
theorem source_odd_small_of_sine_upper (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / (4 * (m : ℝ) + 3)))
    (hy : 0 ≤ signedOddValue m x)
    (hupper : signedOddValue m x ≤
      oddSlopeMagnitude m / Real.sqrt ((4 * (m : ℝ) + 3) - 2 / (4 * (m : ℝ) + 3)) *
        Real.sin (Real.sqrt ((4 * (m : ℝ) + 3) - 2 / (4 * (m : ℝ) + 3)) * x)) :
    |weightedHermite (2 * m + 1) x| ≤
      sourceCoefficient (2 * m + 1) * sourceEnvelope (2 * m + 1) x := by
  have hE : 7 ≤ 4 * (m : ℝ) + 3 := by
    exact_mod_cast (show 7 ≤ 4 * m + 3 by omega)
  have hEp : 0 < 4 * (m : ℝ) + 3 := by positivity
  have hxsq : x ^ 2 ≤ 2 / (4 * (m : ℝ) + 3) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / (4 * (m : ℝ) + 3) by positivity)
    nlinarith [Real.sqrt_nonneg (2 / (4 * (m : ℝ) + 3))]
  have h2 : 2 / (4 * (m : ℝ) + 3) < 4 * (m : ℝ) + 3 := by
    apply (div_lt_iff₀ hEp).mpr
    nlinarith
  have hq : x ^ 2 < 2 * ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    have hh : x ^ 2 < 4 * (m : ℝ) + 3 := hxsq.trans_lt h2
    convert hh using 1
    push_cast
    ring
  exact source_odd_small_from_comparison m hm x hx hx0 hq hy hupper
    (fun u hu hu2 => preX0_sin_sq_bound (4 * (m : ℝ) + 3) hE u hu hu2)

end HermiteEnvelope

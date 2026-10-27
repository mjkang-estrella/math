import SourceAssembly

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Set

def signedOddValue (m : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ m * weightedHermite (2 * m + 1) x

def signedOddSlope (m : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ m * weightedSlope (2 * m + 1) x

theorem signedOddValue_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt (signedOddValue m) (signedOddSlope m x) x :=
  (weightedHermite_hasDerivAt (2 * m + 1) x).const_mul ((-1 : ℝ) ^ m)

theorem signedOddSlope_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt (signedOddSlope m) ((x ^ 2 - (4 * (m : ℝ) + 3)) * signedOddValue m x) x := by
  convert (weightedSlope_hasDerivAt (2 * m + 1) x).const_mul ((-1 : ℝ) ^ m) using 1
  · rfl
  · simp only [signedOddValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

theorem signedOddValue_zero (m : ℕ) : signedOddValue m 0 = 0 := by
  simp [signedOddValue, weightedHermite_zero_odd]

theorem signedOddSlope_zero (m : ℕ) : signedOddSlope m 0 = oddSlopeMagnitude m := by
  rw [signedOddSlope, weightedSlope_zero_odd, ← mul_assoc, ← pow_add]
  rw [show m + m = 2 * m by omega, pow_mul]
  norm_num

theorem signedOddValue_sq (m : ℕ) (x : ℝ) :
    signedOddValue m x ^ 2 = weightedHermite (2 * m + 1) x ^ 2 := by
  have hs : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  simp only [signedOddValue, mul_pow, hs, one_mul]

theorem signedOddSlope_sq (m : ℕ) (x : ℝ) :
    signedOddSlope m x ^ 2 = weightedSlope (2 * m + 1) x ^ 2 := by
  have hs : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  simp only [signedOddSlope, mul_pow, hs, one_mul]

theorem signedOdd_energy (m : ℕ) (x : ℝ) :
    (4 * (m : ℝ) + 3 - x ^ 2) * signedOddValue m x ^ 2 + signedOddSlope m x ^ 2 =
      energy (2 * m + 1) x := by
  rw [signedOddValue_sq, signedOddSlope_sq, energy]
  push_cast
  ring

theorem weighted_bulk_of_energy_at (n : ℕ) (C t x : ℝ) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (htx : t ≤ x) (hq : x ^ 2 < 2 * (n : ℝ) + 1)
    (he : energy n t ≤ (2 * (n : ℝ) + 1) * C ^ 2) :
    |weightedHermite n x| ≤ C * sourceEnvelope n x := by
  have hE : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hem := energy_antitone n ht (ht.trans htx) htx
  have hb : (2 * (n : ℝ) + 1 - x ^ 2) * weightedHermite n x ^ 2 ≤
      (2 * (n : ℝ) + 1) * C ^ 2 := by
    have h := hem.trans he
    unfold energy at h
    nlinarith [sq_nonneg (weightedSlope n x)]
  have hqpos : 0 < 1 - x ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [sub_pos, div_lt_one hE]
    exact hq
  apply abs_le_envelope_of_sq hC hqpos
  apply (mul_le_mul_iff_left₀ hE).mp
  convert hb using 1 <;> field_simp

theorem sine_comparison_bulk_bound (E A C x y : ℝ) (hE : 7 ≤ E)
    (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / E)) (hy : 0 ≤ y)
    (hupper : y ≤ A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x))
    (hA : A ^ 2 ≤ (99 / 98 : ℝ) * (E * C ^ 2))
    (htrig : ∀ u : ℝ, 0 ≤ u → u ≤ Real.sqrt 2 →
      (1 - u ^ 2 / E ^ 2) * Real.sin (Real.sqrt (1 - 2 / E ^ 2) * u) ^ 2 ≤
        (49 / 50 : ℝ) * (1 - 2 / E ^ 2)) :
    (E - x ^ 2) * y ^ 2 ≤ E * C ^ 2 := by
  have hEp : 0 < E := by linarith
  have hEn : E ≠ 0 := hEp.ne'
  have hq : 0 < E - 2 / E := by
    have h2 : 2 / E < E := (div_lt_iff₀ hEp).mpr (by nlinarith)
    linarith
  have hcsq : 0 < 1 - 2 / E ^ 2 := by
    have h2 : 2 / E ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  have hxx : x ^ 2 ≤ 2 / E := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / E by positivity)
    nlinarith [Real.sqrt_nonneg (2 / E)]
  have hqx : 0 ≤ E - x ^ 2 := by
    have h2 : 2 / E < E := (div_lt_iff₀ hEp).mpr (by nlinarith)
    linarith
  let u := Real.sqrt E * x
  have hu0 : 0 ≤ u := mul_nonneg (Real.sqrt_nonneg _) hx
  have husq : u ^ 2 = E * x ^ 2 := by dsimp [u]; rw [mul_pow, Real.sq_sqrt hEp.le]
  have hu2 : u ≤ Real.sqrt 2 := by
    have hh := (le_div_iff₀ hEp).mp hxx
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt : Real.sqrt (E - 2 / E) = Real.sqrt E * Real.sqrt (1 - 2 / E ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hEp.le, Real.sq_sqrt hcsq.le]
    field_simp
  have hphase : Real.sqrt (E - 2 / E) * x = Real.sqrt (1 - 2 / E ^ 2) * u := by
    rw [hsqrt]
    dsimp [u]
    ring
  have hscalar := mul_le_mul_of_nonneg_left (htrig u hu0 hu2) hEp.le
  have hs : (E - x ^ 2) * Real.sin (Real.sqrt (E - 2 / E) * x) ^ 2 ≤
      (49 / 50 : ℝ) * (E - 2 / E) := by
    rw [hphase]
    convert hscalar using 1
    · rw [husq]
      field_simp
    · field_simp
  have hsqp : 0 < Real.sqrt (E - 2 / E) := Real.sqrt_pos.mpr hq
  have hmul := mul_le_mul_of_nonneg_right hupper hsqp.le
  have hmul' : y * Real.sqrt (E - 2 / E) ≤ A * Real.sin (Real.sqrt (E - 2 / E) * x) := by
    have hc : A / Real.sqrt (E - 2 / E) * Real.sin (Real.sqrt (E - 2 / E) * x) *
        Real.sqrt (E - 2 / E) = A * Real.sin (Real.sqrt (E - 2 / E) * x) := by
      calc
        _ = (A / Real.sqrt (E - 2 / E) * Real.sqrt (E - 2 / E)) *
            Real.sin (Real.sqrt (E - 2 / E) * x) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hsqp.ne']
    simpa only [hc] using hmul
  have hab : 0 ≤ A * Real.sin (Real.sqrt (E - 2 / E) * x) :=
    (mul_nonneg hy hsqp.le).trans hmul'
  have hsquare := (sq_le_sq₀ (mul_nonneg hy hsqp.le) hab).mpr hmul'
  rw [mul_pow, mul_pow, Real.sq_sqrt hq.le] at hsquare
  have h1 := mul_le_mul_of_nonneg_left hsquare hqx
  have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg A)
  have hmid : (E - x ^ 2) * y ^ 2 ≤ (49 / 50 : ℝ) * A ^ 2 := by
    apply (mul_le_mul_iff_right₀ hq).mp
    nlinarith
  have hEC : 0 ≤ E * C ^ 2 := mul_nonneg hEp.le (sq_nonneg C)
  nlinarith

theorem weighted_bulk_of_quadratic (n : ℕ) (C x : ℝ) (hC : 0 ≤ C)
    (hq : x ^ 2 < 2 * (n : ℝ) + 1)
    (hb : (2 * (n : ℝ) + 1 - x ^ 2) * weightedHermite n x ^ 2 ≤
      (2 * (n : ℝ) + 1) * C ^ 2) :
    |weightedHermite n x| ≤ C * sourceEnvelope n x := by
  have hE : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hqpos : 0 < 1 - x ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [sub_pos, div_lt_one hE]
    exact hq
  apply abs_le_envelope_of_sq hC hqpos
  apply (mul_le_mul_iff_left₀ hE).mp
  convert hb using 1 <;> field_simp

theorem source_odd_large_from_loss (m : ℕ) (x : ℝ)
    (hx : Real.sqrt (2 / (4 * (m : ℝ) + 3)) ≤ x)
    (hq : x ^ 2 < 2 * ((2 * m + 1 : ℕ) : ℝ) + 1)
    (hloss :
      (4 * (m : ℝ) + 3 - Real.sqrt (2 / (4 * (m : ℝ) + 3)) ^ 2) *
          signedOddValue m (Real.sqrt (2 / (4 * (m : ℝ) + 3))) ^ 2 +
        signedOddSlope m (Real.sqrt (2 / (4 * (m : ℝ) + 3))) ^ 2 <
      oddSlopeMagnitude m ^ 2 * (1 - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2))) :
    |weightedHermite (2 * m + 1) x| ≤
      sourceCoefficient (2 * m + 1) * sourceEnvelope (2 * m + 1) x := by
  rw [signedOdd_energy] at hloss
  apply weighted_bulk_of_energy_at _ _ _ x (sourceCoefficient_pos _).le
    (Real.sqrt_nonneg _) hx hq
  have h := hloss.trans (odd_initial_corrected_bound m)
  convert h.le using 1; push_cast; ring

theorem source_odd_small_from_comparison (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx : 0 ≤ x) (hx0 : x ≤ Real.sqrt (2 / (4 * (m : ℝ) + 3)))
    (hq : x ^ 2 < 2 * ((2 * m + 1 : ℕ) : ℝ) + 1)
    (hy : 0 ≤ signedOddValue m x)
    (hupper : signedOddValue m x ≤
      oddSlopeMagnitude m / Real.sqrt ((4 * (m : ℝ) + 3) - 2 / (4 * (m : ℝ) + 3)) *
        Real.sin (Real.sqrt ((4 * (m : ℝ) + 3) - 2 / (4 * (m : ℝ) + 3)) * x))
    (htrig : ∀ u : ℝ, 0 ≤ u → u ≤ Real.sqrt 2 →
      (1 - u ^ 2 / (4 * (m : ℝ) + 3) ^ 2) *
        Real.sin (Real.sqrt (1 - 2 / (4 * (m : ℝ) + 3) ^ 2) * u) ^ 2 ≤
        (49 / 50 : ℝ) * (1 - 2 / (4 * (m : ℝ) + 3) ^ 2)) :
    |weightedHermite (2 * m + 1) x| ≤
      sourceCoefficient (2 * m + 1) * sourceEnvelope (2 * m + 1) x := by
  have hE : 7 ≤ 4 * (m : ℝ) + 3 := by exact_mod_cast (show 7 ≤ 4 * m + 3 by omega)
  have h := sine_comparison_bulk_bound (4 * (m : ℝ) + 3) (oddSlopeMagnitude m)
    (sourceCoefficient (2 * m + 1)) x (signedOddValue m x)
    hE hx hx0 hy hupper (odd_initial_small_bound m hm) htrig
  rw [signedOddValue_sq] at h
  apply weighted_bulk_of_quadratic _ _ x (sourceCoefficient_pos _).le hq
  convert h using 1 <;> push_cast <;> ring

end HermiteEnvelope

import RealRoots

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

def peakPolynomial (q : ℝ) : ℝ := q ^ 3 - q ^ 2 + 2 * q + 1

def rationalPeakUpper (E : ℝ) : ℝ := (22 / 7 : ℝ) - (22 / 7 : ℝ) ^ 2 / (4 * E)

theorem peakPolynomial_monotone : Monotone peakPolynomial := by
  intro u v huv
  have hb : 0 ≤ v ^ 2 + v * u + u ^ 2 - v - u + 2 := by
    nlinarith [sq_nonneg (u + v - 2 / 3), sq_nonneg (u - v)]
  have hp := mul_nonneg (sub_nonneg.mpr huv) hb
  unfold peakPolynomial
  nlinarith

theorem peak_certificate (E : ℝ) (hE : E ≠ 0) :
    (3 * E - peakPolynomial (rationalPeakUpper E)) * (117649 * E ^ 3) =
      352947 * (E - 7) ^ 4 + 6535179 * (E - 7) ^ 3 +
        40836159 * (E - 7) ^ 2 + 89231464 * (E - 7) + 19560668 := by
  unfold peakPolynomial rationalPeakUpper
  field_simp
  ring

theorem peak_rational_upper_lt (E : ℝ) (hE : 7 ≤ E) :
    peakPolynomial (rationalPeakUpper E) < 3 * E := by
  have hEp : 0 < E := by linarith
  have ht : 0 ≤ E - 7 := by linarith
  have hd : 0 < 117649 * E ^ 3 := by positivity
  have hp : 0 < (3 * E - peakPolynomial (rationalPeakUpper E)) * (117649 * E ^ 3) := by
    rw [peak_certificate E hEp.ne']
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hp)

theorem turning_upper_le_rational (E : ℝ) (hE : 7 ≤ E) :
    Real.pi - Real.pi ^ 2 / (4 * E) ≤ rationalPeakUpper E := by
  have hEp : 0 < E := by linarith
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hp : 0 ≤ ((22 / 7 : ℝ) - Real.pi) * (4 * E - ((22 / 7 : ℝ) + Real.pi)) :=
    mul_nonneg (sub_nonneg.mpr hpi) (by linarith)
  have hid : rationalPeakUpper E - (Real.pi - Real.pi ^ 2 / (4 * E)) =
      (((22 / 7 : ℝ) - Real.pi) * (4 * E - ((22 / 7 : ℝ) + Real.pi))) / (4 * E) := by
    unfold rationalPeakUpper
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hp (by positivity)

theorem peak_obstruction (E x : ℝ) (hE : 7 ≤ E)
    (hx : E - Real.pi + Real.pi ^ 2 / (4 * E) ≤ x ^ 2)
    (hm : 3 * E ≤ peakPolynomial (E - x ^ 2)) : False := by
  have hq : E - x ^ 2 ≤ Real.pi - Real.pi ^ 2 / (4 * E) := by linarith
  have hr := peakPolynomial_monotone (hq.trans (turning_upper_le_rational E hE))
  have hs := peak_rational_upper_lt E hE
  linarith

theorem moment_peak_inequality {ι : Type*} [Fintype ι] (a : ι → ℝ) (E q x : ℝ)
    (h2 : ∑ i, a i ^ 2 = q - 1) (h3 : ∑ i, a i ^ 3 = x)
    (h4 : ∑ i, a i ^ 4 = (q ^ 2 - 1) / 3) (hE : E = q + x ^ 2) :
    3 * E ≤ peakPolynomial q := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) a (fun i => a i ^ 2)
  have hm : (∑ i, a i * a i ^ 2) = ∑ i, a i ^ 3 := by congr 1; funext i; ring
  have hs : (∑ i, (a i ^ 2) ^ 2) = ∑ i, a i ^ 4 := by congr 1; funext i; ring
  rw [hm, hs, h2, h3, h4] at h
  unfold peakPolynomial
  nlinarith

end HermiteEnvelope

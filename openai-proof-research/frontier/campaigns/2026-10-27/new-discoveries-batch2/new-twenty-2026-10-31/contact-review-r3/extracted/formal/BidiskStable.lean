import CayleyPolynomials
import GraphResolvent

namespace ContactPilot
noncomputable section
open scoped Matrix

def dampedMatrix (z w : ℂ) (t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![-z-Complex.I*t,1,1,1,0; 1,-w,0,1,0; 1,0,-w,0,1;
     1,1,0,-z,1; 0,0,1,1,-z]

theorem damped_energy (z w : ℂ) (t : ℝ) (v : Fin 5 → ℂ) :
    (∑ j, star (v j) * (dampedMatrix z w t *ᵥ v) j).im =
      -z.im * (Complex.normSq (v 0) + Complex.normSq (v 3) + Complex.normSq (v 4))
      -w.im * (Complex.normSq (v 1) + Complex.normSq (v 2))
      -t * Complex.normSq (v 0) := by
  simp [dampedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem damped_kernel (z w : ℂ) (t : ℝ) (hz : 0 < z.im) (hw : 0 < w.im)
    (ht : 0 ≤ t) (v : Fin 5 → ℂ) (hv : dampedMatrix z w t *ᵥ v = 0) : v = 0 := by
  have he := damped_energy z w t v
  rw [hv] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_im] at he
  have h0 := Complex.normSq_nonneg (v 0)
  have h1 := Complex.normSq_nonneg (v 1)
  have h2 := Complex.normSq_nonneg (v 2)
  have h3 := Complex.normSq_nonneg (v 3)
  have h4 := Complex.normSq_nonneg (v 4)
  have hzS : 0 ≤ z.im * (Complex.normSq (v 0) + Complex.normSq (v 3) + Complex.normSq (v 4)) := mul_nonneg hz.le (by positivity)
  have hwS : 0 ≤ w.im * (Complex.normSq (v 1) + Complex.normSq (v 2)) := mul_nonneg hw.le (by positivity)
  have htS : 0 ≤ t * Complex.normSq (v 0) := mul_nonneg ht h0
  have hzs : Complex.normSq (v 0) + Complex.normSq (v 3) + Complex.normSq (v 4) = 0 := by nlinarith
  have hws : Complex.normSq (v 1) + Complex.normSq (v 2) = 0 := by nlinarith
  have e0 : v 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e1 : v 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e2 : v 2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e3 : v 3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e4 : v 4 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  funext j
  fin_cases j <;> assumption

theorem damped_det_ne_zero (z w : ℂ) (t : ℝ) (hz : 0 < z.im) (hw : 0 < w.im)
    (ht : 0 ≤ t) : (dampedMatrix z w t).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v u h
  have he : dampedMatrix z w t *ᵥ (v-u) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (damped_kernel z w t hz hw ht (v-u) he)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem damped_det (z w : ℂ) (t : ℝ) :
    (dampedMatrix z w t).det = Q z w - Complex.I*t*N z w := by
  simp [dampedMatrix, Matrix.det_succ_row_zero, Fin.succAbove,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Q, N]
  ring

theorem disk_one_add_ne_zero (z : ℂ) (hz : ‖z‖ < 1) : 1+z ≠ 0 := by
  intro he
  have hez : z = -1 := by linear_combination he
  simp [hez] at hz

theorem betaInv_im (z : ℂ) :
    (betaInv z).im = (1-Complex.normSq z) / Complex.normSq (1+z) := by
  simp [betaInv, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem betaInv_im_pos (z : ℂ) (hz : ‖z‖ < 1) : 0 < (betaInv z).im := by
  rw [betaInv_im]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (disk_one_add_ne_zero z hz)

theorem Q_upper_ne_zero (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) : Q z w ≠ 0 := by
  have h := damped_det_ne_zero z w 0 hz hw (by norm_num)
  simpa [damped_det] using h

theorem Q_sub_I_N_upper_ne_zero (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    Q z w - Complex.I*N z w ≠ 0 := by
  have h := damped_det_ne_zero z w 1 hz hw (by norm_num)
  simpa [damped_det] using h

theorem bidisk_denominator_stable : ∀ z w : ℂ,
    ‖z‖ < 1 → ‖w‖ < 1 → eval₂ bidiskDenominator z w ≠ 0 := by
  intro z w hz hw
  have hz' := disk_one_add_ne_zero z hz
  have hw' := disk_one_add_ne_zero w hw
  have hclear : eval₂ bidiskDenominator z w =
      ((1+z)^3*(1+w)^2) *
      (Q (betaInv z) (betaInv w)-Complex.I*N (betaInv z) (betaInv w)) := by
    simp only [bidiskDenominator, eval₂, map_sub, map_mul, MvPolynomial.eval_C]
    change eval₂ cayleyQ z w - Complex.I*eval₂ cayleyN z w = _
    rw [cayleyQ_clearing z w hz' hw', cayleyN_clearing z w hz' hw', eval_q, eval_n]
    unfold Q N
    ring
  rw [hclear]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz') (pow_ne_zero _ hw'))
    (Q_sub_I_N_upper_ne_zero _ _ (betaInv_im_pos z hz) (betaInv_im_pos w hw))

theorem bidisk_represents_graph : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
    beta (graphFunction candidateGraph candidateColors 0 (betaInv z) (betaInv w)) =
      eval₂ bidiskNumerator z w / eval₂ bidiskDenominator z w := by
  intro z w hz hw
  rw [graph_quotient]
  have hq : eval₂ q (betaInv z) (betaInv w) ≠ 0 := by
    rw [eval_q]
    exact Q_upper_ne_zero _ _ (betaInv_im_pos z hz) (betaInv_im_pos w hw)
  simpa only [eval_n, eval_q, N, Q] using
    bidisk_represents_quotient z w (disk_one_add_ne_zero z hz) (disk_one_add_ne_zero w hw) hq
end
end ContactPilot

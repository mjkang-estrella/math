module
public import Substitution
public import Defs
public section
noncomputable section
open Real MeasureTheory Set
namespace PendulumTimeMap
@[expose] def angle (c r : ℝ) : ℝ := b (2*r/c)
theorem angle_range {c r : ℝ} (hr : 0<r) (hcr : r<c) :
 0<angle c r ∧ angle c r<Real.pi/2 := by
 have hc : 0<c := lt_trans hr hcr
 apply b_range
 · positivity
 · exact (div_lt_iff₀ hc).mpr (by linarith)
theorem change_angle {c r : ℝ} (hr : 0<r) (hcr : r<c) : change c (angle c r)=r := by
 have hc : 0<c := lt_trans hr hcr
 have hh := a_b (z := 2*r/c) (by positivity) (le_of_lt ((div_lt_iff₀ hc).mpr (by linarith)))
 change c/2*a (b (2*r/c))=r
 rw [hh]
 field_simp
theorem moment_piece {n : ℕ} {c r : ℝ} (hr : 0<r) (hcr : r<c) :
 IntervalIntegrable (fun t => t^n/Real.sqrt (t*(c-t))) volume 0 r ∧
 (∫ t in 0..r, t^n/Real.sqrt (t*(c-t))) =
 2*(∫ x in 0..angle c r, (change c x)^n) := by
 have hq := angle_range hr hcr
 have h := weighted_substitution (lt_trans hr hcr) hq.1 hq.2 (fun t => t^n)
   (continuous_pow n).continuousOn
 rwa [change_angle hr hcr] at h
theorem moment_integrable (n : ℕ) {a z : ℝ} (ha : 0<a) (hz : 0<z) :
 IntervalIntegrable (momentKernel n a z) volume 0 a ∧
 IntervalIntegrable (momentKernel n a z) volume 0 z := by
 exact ⟨(moment_piece (n := n) (c := a+z) ha (by linarith)).1,
 (moment_piece (n := n) (c := a+z) hz (by linarith)).1⟩
theorem angle_complement {a z : ℝ} (ha : 0<a) (hz : 0<z) :
 angle (a+z) a + angle (a+z) z=Real.pi/2 := by
 have hc : a+z≠0 := ne_of_gt (by linarith)
 have he : 1-2*z/(a+z) = -(1-2*a/(a+z)) := by field_simp; ring
 unfold angle b
 rw [he, Real.arccos_neg]
 ring
theorem moment_zero {a z : ℝ} (ha : 0<a) (hz : 0<z) : moment 0 a z=Real.pi := by
 have h1 := (moment_piece (n := 0) ha (show a<a+z by linarith)).2
 have h2 := (moment_piece (n := 0) hz (show z<a+z by linarith)).2
 simp only [pow_zero, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at h1 h2
 unfold moment momentKernel
 simp only [pow_zero]
 rw [h1,h2]
 linarith [angle_complement ha hz]
theorem integral_change (c q : ℝ) :
 (∫ x in 0..q, change c x)=c/2*(q-Real.sin (2*q)/2) := by
 have hc : Continuous (fun x : ℝ => Real.cos (2*x)) := by fun_prop
 have hi := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos) (a := 0) (b := q) 2
 simp only [mul_zero, integral_cos, Real.sin_zero, sub_zero] at hi
 unfold change
 rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
   (intervalIntegrable_const) (hc.intervalIntegrable 0 q)]
 simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
 congr 1
 linarith
theorem angle_sine {a z : ℝ} (ha : 0<a) (hz : 0<z) :
 (a+z)/2*Real.sin (2*angle (a+z) a)=Real.sqrt (a*z) := by
 have hq := angle_range ha (show a<a+z by linarith)
 -- The endpoint itself lies inside a slightly larger admissible angle.
 have hbig : (angle (a+z) a + Real.pi/2)/2 < Real.pi/2 := by linarith [hq.2]
 have hmem : angle (a+z) a ∈ Ioo 0 ((angle (a+z) a + Real.pi/2)/2) := ⟨hq.1, by linarith [hq.2]⟩
 have h := change_sqrt (c := a+z) (by linarith) hbig hmem
 rw [change_angle ha (by linarith), show a+z-a=z by ring] at h
 exact h.symm
theorem moment_one {a z : ℝ} (ha : 0<a) (hz : 0<z) :
 moment 1 a z=Real.pi*(a+z)/2-2*Real.sqrt (a*z) := by
 have h1 := (moment_piece (n := 1) ha (show a<a+z by linarith)).2
 have h2 := (moment_piece (n := 1) hz (show z<a+z by linarith)).2
 simp only [pow_one, integral_change] at h1 h2
 unfold moment momentKernel
 simp only [pow_one]
 rw [h1,h2]
 have hs1 := angle_sine ha hz
 have hs2 := angle_sine hz ha
 rw [add_comm z a, mul_comm z a] at hs2
 have hq := angle_complement ha hz
 nlinarith
end PendulumTimeMap
